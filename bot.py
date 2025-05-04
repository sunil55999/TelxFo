import asyncio
import logging
import json
from telethon import TelegramClient, events, errors
from telethon.tl.types import (
    MessageMediaWebPage, MessageEntityTextUrl, MessageEntityUrl,
    MessageMediaPhoto, MessageMediaDocument, MessageMediaPoll,
    MessageMediaGeo, MessageMediaContact, MessageMediaVenue,
    MessageMediaGame, MessageMediaInvoice, MessageMediaGeoLive,
    MessageMediaDice, MessageMediaStory, InputMediaPoll, Poll,
    PollAnswer, InputReplyToMessage, Updates, UpdateNewMessage,
    InputMediaUploadedPhoto, InputFile
)
from collections import deque
from datetime import datetime
import imagehash
from PIL import Image, ImageDraw, ImageFont
import io
import traceback
import re
import shutil
import ahocorasick
import textwrap
import os
import random

# Configuration
API_ID = 29371370  # Replace with your API ID
API_HASH = "01f1272c02b1b322ac339c800bbb1cf2"  # Replace with your API hash
SESSION_FILE = "userbot_session"
client = TelegramClient(SESSION_FILE, API_ID, API_HASH)

MAPPINGS_FILE = "channel_mappings.json"
MAX_RETRIES = 3
RETRY_DELAY = 5  # seconds
MAX_QUEUE_SIZE = 100
MAX_MAPPING_HISTORY = 1000
MONITOR_CHAT_ID = None
NOTIFY_CHAT_ID = None
INACTIVITY_THRESHOLD = 21600  # 6 hours in seconds
MAX_MESSAGE_LENGTH = 4096  # Telegram's max message length
FORWARD_DELAY = 1  # seconds delay between forwarding messages
QUEUE_INACTIVITY_THRESHOLD = 600  # 10 minutes in seconds for queue inactivity alert
NUM_WORKERS = 3  # Number of async workers for queue processing

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.FileHandler("forward_bot.log"), logging.StreamHandler()]
)
logger = logging.getLogger("ForwardBot")

# Data structures
channel_mappings = {}
message_queue = deque(maxlen=MAX_QUEUE_SIZE)
is_connected = False
pair_stats = {}

# Helper Functions
def save_mappings():
    """Save channel mappings to a JSON file."""
    try:
        with open(MAPPINGS_FILE, "w") as f:
            json.dump(channel_mappings, f)
        logger.info("Channel mappings saved to file.")
    except Exception as e:
        logger.error(f"Error saving mappings: {e}")

def load_mappings():
    """Load channel mappings from a JSON file, handling corrupted files."""
    global channel_mappings
    try:
        with open(MAPPINGS_FILE, "r") as f:
            channel_mappings = json.load(f)
        logger.info(f"Loaded {sum(len(v) for v in channel_mappings.values())} mappings from file.")
        for user_id, pairs in channel_mappings.items():
            if user_id not in pair_stats:
                pair_stats[user_id] = {}
            for pair_name in pairs:
                pair_stats[user_id][pair_name] = {
                    'forwarded': 0, 'edited': 0, 'deleted': 0, 'blocked': 0, 'queued': 0, 'last_activity': None
                }
    except FileNotFoundError:
        logger.info("No existing mappings file found. Starting fresh.")
    except json.JSONDecodeError as e:
        logger.error(f"Corrupted mapping file: {e}. Backing up and starting fresh.")
        shutil.move(MAPPINGS_FILE, MAPPINGS_FILE + ".bak")
        channel_mappings = {}
    except Exception as e:
        logger.error(f"Error loading mappings: {e}")

def compile_blocked_sentences(blocked_sentences):
    """Compile blocked sentences into a single regex pattern."""
    if not blocked_sentences:
        return None
    escaped = [re.escape(s.lower()) for s in blocked_sentences]
    return re.compile('|'.join(escaped))

def check_blocked_sentences_fast(text, compiled_pattern):
    """Check if text contains any blocked sentences using compiled regex."""
    if not text or not compiled_pattern:
        return False, None
    match = compiled_pattern.search(text.lower())
    return (True, match.group(0)) if match else (False, None)

def build_blacklist_trie(words):
    """Build an Aho-Corasick automaton for fast multi-word searching."""
    A = ahocorasick.Automaton()
    for idx, word in enumerate(words):
        A.add_word(word.lower(), (idx, word))
    A.make_automaton()
    return A

def filter_text_with_blacklist(text, automaton):
    """Filter text using Aho-Corasick automaton, replacing matches with '***'."""
    found = False
    for end_index, (idx, word) in automaton.iter(text.lower()):
        text = text.replace(word, '***')
        found = True
    return text, found

def filter_urls(text, block_urls, blacklist_urls=None):
    """Filter or block URLs based on settings."""
    if not text:
        return text, True
    url_pattern = r'https?://(?:[-\w.]|(?:%[\da-fA-F]{2}))+(?:/[^\s]*)?'
    urls = re.findall(url_pattern, text)
    if block_urls:
        text = re.sub(url_pattern, '[URL REMOVED]', text)
        return text, False
    elif blacklist_urls and urls:
        for url in urls:
            if any(blacklisted in url for blacklisted in blacklist_urls):
                text = text.replace(url, '[URL BLOCKED]')
        return text, True
    return text, True

def remove_header_footer(text, header_pattern, footer_pattern):
    """Remove specified header and footer from text."""
    if not text:
        return text
    if header_pattern and text.startswith(header_pattern):
        text = text[len(header_pattern):].strip()
    if footer_pattern and text.endswith(footer_pattern):
        text = text[:-len(footer_pattern)].strip()
    return text

def apply_custom_header_footer(text, custom_header, custom_footer):
    """Add custom header and footer to text."""
    if not text:
        return text
    result = text
    if custom_header:
        result = f"{custom_header}\n{result}"
    if custom_footer:
        result = f"{result}\n{custom_footer}"
    return result.strip()

async def send_split_message(client, entity, message_text, reply_to=None, silent=False, entities=None):
    """Send long messages by splitting them into parts."""
    if len(message_text) <= MAX_MESSAGE_LENGTH:
        return await client.send_message(
            entity=entity,
            message=message_text,
            reply_to=reply_to,
            silent=silent,
            formatting_entities=entities if entities else None
        )
    parts = [message_text[i:i + MAX_MESSAGE_LENGTH] for i in range(0, len(message_text), MAX_MESSAGE_LENGTH)]
    sent_messages = []
    for part in parts:
        sent_msg = await client.send_message(
            entity=entity,
            message=part,
            reply_to=reply_to if not sent_messages else None,
            silent=silent,
            formatting_entities=entities if entities and not sent_messages else None
        )
        sent_messages.append(sent_msg)
        await asyncio.sleep(0.5)
    return sent_messages[0] if sent_messages else None

async def notify_blocked(event, mapping, pair_name, reason):
    """Notify the owner when a message is blocked."""
    if NOTIFY_CHAT_ID:
        msg_id = getattr(event.message, 'id', 'Unknown')
        await client.send_message(
            NOTIFY_CHAT_ID,
            f"🚫 Message blocked in pair '{pair_name}' from '{mapping['source']}'.\n"
            f"📄 Reason: {reason}\n🆔 Source Message ID: {msg_id}"
        )

# Watermark Functions
def get_font_path(font_name):
    """Get the path to a font file based on name."""
    font_mappings = {
        'arial': '/usr/share/fonts/truetype/msttcorefonts/Arial.ttf',
        'times': '/usr/share/fonts/truetype/msttcorefonts/Times_New_Roman.ttf',
        'verdana': '/usr/share/fonts/truetype/msttcorefonts/Verdana.ttf',
        'georgia': '/usr/share/fonts/truetype/msttcorefonts/Georgia.ttf',
        'courier': '/usr/share/fonts/truetype/msttcorefonts/Courier_New.ttf',
        'comic': '/usr/share/fonts/truetype/msttcorefonts/Comic_Sans_MS.ttf',
        'impact': '/usr/share/fonts/truetype/msttcorefonts/Impact.ttf',
        'roboto': '/usr/share/fonts/truetype/roboto/Roboto-Regular.ttf',
        'opensans': '/usr/share/fonts/truetype/opensans/OpenSans-Regular.ttf',
    }

    font_path = font_mappings.get(font_name.lower(), '')
    if not font_path or not os.path.exists(font_path):
        possible_font_dirs = [
            '/usr/share/fonts/truetype/',
            '/usr/share/fonts/TTF/',
            '/usr/share/fonts/',
            '/Library/Fonts/',
            'C:\\Windows\\Fonts\\'
        ]
        for font_dir in possible_font_dirs:
            if os.path.exists(font_dir):
                font_files = [f for f in os.listdir(font_dir) if f.endswith(('.ttf', '.otf'))]
                if font_files:
                    return os.path.join(font_dir, font_files[0])
        return None  # Fallback to default font
    return font_path

def parse_color(color_str):
    """Parse color string to RGB tuple."""
    color_map = {
        'white': (255, 255, 255),
        'black': (0, 0, 0),
        'red': (255, 0, 0),
        'green': (0, 255, 0),
        'blue': (0, 0, 255),
        'yellow': (255, 255, 0),
        'purple': (128, 0, 128),
        'orange': (255, 165, 0),
        'pink': (255, 192, 203),
        'gray': (128, 128, 128),
    }

    if color_str.lower() in color_map:
        return color_map[color_str.lower()]
    if color_str.startswith('#') and len(color_str) == 7:
        try:
            r = int(color_str[1:3], 16)
            g = int(color_str[3:5], 16)
            b = int(color_str[5:7], 16)
            return (r, g, b)
        except ValueError:
            pass
    return (255, 255, 255)  # Default to white

def calculate_position(watermark_position, img_width, img_height, text_width, text_height):
    """Calculate watermark text position."""
    padding = 20
    if watermark_position == 'random':
        positions = ['top-left', 'top-right', 'bottom-left', 'bottom-right', 'center']
        watermark_position = random.choice(positions)
    if watermark_position == 'top-left':
        return (padding, padding)
    elif watermark_position == 'top-right':
        return (img_width - text_width - padding, padding)
    elif watermark_position == 'bottom-left':
        return (padding, img_height - text_height - padding)
    elif watermark_position == 'bottom-right':
        return (img_width - text_width - padding, img_height - text_height - padding)
    elif watermark_position == 'center':
        return ((img_width - text_width) // 2, (img_height - text_height) // 2)
    else:
        return (img_width - text_width - padding, img_height - text_height - padding)

def add_watermark(image_data, watermark_config):
    """Add watermark to an image."""
    if not watermark_config['enabled']:
        return image_data

    try:
        image = Image.open(io.BytesIO(image_data))
        watermark_img = image.copy()

        watermark_text = watermark_config['text']
        position = watermark_config['position']
        opacity = float(watermark_config['opacity'])
        color = parse_color(watermark_config['color'])
        font_name = watermark_config['font']
        font_size = int(watermark_config['font_size'])

        font_path = get_font_path(font_name)
        try:
            if font_path:
                font = ImageFont.truetype(font_path, font_size)
            else:
                font = ImageFont.load_default(size=font_size)
        except Exception as e:
            logger.error(f"Font error: {e}, using default")
            font = ImageFont.load_default(size=20)

        max_width = image.width - 40
        watermark_lines = textwrap.wrap(watermark_text, width=max_width // (font_size // 2))
        watermark_text = '\n'.join(watermark_lines)

        draw = ImageDraw.Draw(watermark_img)
        text_bbox = draw.multiline_textbbox((0, 0), watermark_text, font=font)
        text_width = text_bbox[2] - text_bbox[0]
        text_height = text_bbox[3] - text_bbox[1]

        pos = calculate_position(position, image.width, image.height, text_width, text_height)

        watermark_layer = Image.new('RGBA', watermark_img.size, (0, 0, 0, 0))
        watermark_layer_draw = ImageDraw.Draw(watermark_layer)
        watermark_layer_draw.multiline_text(
            pos, watermark_text, font=font, fill=(color[0], color[1], color[2], int(255 * opacity))
        )

        if watermark_img.mode != 'RGBA':
            watermark_img = watermark_img.convert('RGBA')
        result = Image.alpha_composite(watermark_img, watermark_layer)

        if image.mode != 'RGBA':
            result = result.convert(image.mode)

        output = io.BytesIO()
        result.save(output, format=image.format or 'JPEG')
        output.seek(0)
        return output.getvalue()

    except Exception as e:
        logger.error(f"Error adding watermark: {e}", exc_info=True)
        return image_data

# Core Functions
async def forward_message_with_retry(event, mapping, user_id, pair_name):
    """Forward a message with retries, filtering, and error handling."""
    source_msg_id = event.message.id if hasattr(event.message, 'id') else "Unknown"
    for attempt in range(MAX_RETRIES):
        try:
            start_time = datetime.now()
            message_text = event.message.raw_text or ""
            text_lower = message_text.lower()
            original_entities = event.message.entities or []
            media = event.message.media
            reply_to = await handle_reply_mapping(event, mapping)

            if message_text:
                compiled_blocked = compile_blocked_sentences(mapping.get('blocked_sentences'))
                should_block, matching_sentence = check_blocked_sentences_fast(text_lower, compiled_blocked)
                if should_block:
                    reason = f"Blocked sentence match: '{matching_sentence}'"
                    await notify_blocked(event, mapping, pair_name, reason)
                    pair_stats[user_id][pair_name]['blocked'] += 1
                    return True

                if mapping.get('blacklist'):
                    automaton = build_blacklist_trie(mapping['blacklist'])
                    message_text, found = filter_text_with_blacklist(message_text, automaton)
                    if found and message_text.strip() == "***":
                        reason = "Entire message blacklisted"
                        await notify_blocked(event, mapping, pair_name, reason)
                        pair_stats[user_id][pair_name]['blocked'] += 1
                        return True

                if mapping.get('block_urls', False) or mapping.get('blacklist_urls'):
                    original_text = message_text
                    message_text, allow_preview = filter_urls(
                        message_text,
                        mapping.get('block_urls', False),
                        mapping.get('blacklist_urls')
                    )
                    if message_text != original_text:
                        original_entities = None
                        if mapping.get('block_urls', False):
                            await notify_blocked(event, mapping, pair_name, "URLs removed due to block_urls setting")

                if mapping.get('header_pattern') or mapping.get('footer_pattern'):
                    message_text = remove_header_footer(
                        message_text, mapping.get('header_pattern', ''), mapping.get('footer_pattern', '')
                    )
                    if message_text != event.message.raw_text:
                        original_entities = None

                if mapping.get('remove_mentions', False):
                    message_text = re.sub(r'@[a-zA-Z0-9_]+|\[([^\]]+)\]\(tg://user\?id=\d+\)', '', message_text)
                    message_text = re.sub(r'\s+', ' ', message_text).strip()
                    original_entities = None

                message_text = apply_custom_header_footer(
                    message_text, mapping.get('custom_header', ''), mapping.get('custom_footer', '')
                )
                if message_text != event.message.raw_text:
                    original_entities = None

            filter_time = (datetime.now() - start_time).total_seconds()
            logger.info(f"Filtering took {filter_time:.3f}s for pair '{pair_name}' (Source Msg ID: {source_msg_id})")

            if media:
                logger.info(f"Media type: {type(media).__name__}")
                if isinstance(media, MessageMediaPhoto):
                    if mapping.get('blocked_image_hashes') or mapping.get('watermark', {}).get('enabled', False):
                        photo_data = await client.download_media(event.message, bytes)
                        if mapping.get('blocked_image_hashes'):
                            image = Image.open(io.BytesIO(photo_data))
                            image_hash = str(imagehash.phash(image))
                            if image_hash in mapping['blocked_image_hashes']:
                                reason = f"Image hash match: {image_hash}"
                                await notify_blocked(event, mapping, pair_name, reason)
                                pair_stats[user_id][pair_name]['blocked'] += 1
                                return True

                    if mapping.get('watermark', {}).get('enabled', False):
                        watermarked_data = add_watermark(photo_data, mapping['watermark'])
                        file_handle = await client.upload_file(watermarked_data, file_name="watermarked_image.jpg")
                        sent_message = await client.send_message(
                            entity=int(mapping['destination']),
                            file=InputMediaUploadedPhoto(file=file_handle),
                            message=message_text,
                            reply_to=reply_to,
                            silent=event.message.silent,
                            formatting_entities=original_entities if original_entities else None
                        )
                    else:
                        sent_message = await client.send_message(
                            entity=int(mapping['destination']),
                            file=media,
                            message=message_text,
                            reply_to=reply_to,
                            silent=event.message.silent,
                            formatting_entities=original_entities if original_entities else None
                        )
                elif isinstance(media, MessageMediaPoll):
                    poll = media.poll
                    answers = [PollAnswer(answer.text, answer.option) for answer in poll.answers]
                    # Warn if it's a quiz, as correct answers cannot be preserved
                    if poll.quiz:
                        logger.warning(f"Forwarding quiz poll for pair '{pair_name}', but correct answers cannot be preserved.")
                        if NOTIFY_CHAT_ID:
                            await client.send_message(
                                NOTIFY_CHAT_ID,
                                f"⚠️ Forwarding quiz poll for pair '{pair_name}', but correct answers cannot be preserved."
                            )
                    try:
                        sent_message = await client.send_message(
                            entity=int(mapping['destination']),
                            message=message_text,
                            file=InputMediaPoll(
                                poll=Poll(
                                    id=poll.id,
                                    question=poll.question,
                                    answers=answers,
                                    public_voters=poll.public_voters,
                                    multiple_choice=poll.multiple_choice,
                                    quiz=poll.quiz,
                                    close_date=poll.close_date,
                                    closed=poll.closed
                                ),
                                correct_answers=None  # Cannot preserve correct answers when forwarding
                            ),
                            reply_to=reply_to,
                            silent=event.message.silent,
                            formatting_entities=original_entities if original_entities else None
                        )
                        logger.info(f"Forwarded poll for pair '{pair_name}' (Source Msg ID: {source_msg_id})")
                    except Exception as e:
                        logger.error(f"Error sending poll for pair '{pair_name}': {e}")
                        await notify_blocked(event, mapping, pair_name, f"Error sending poll: {e}")
                        return False
                elif isinstance(media, MessageMediaDocument):
                    sent_message = await client.send_message(
                        entity=int(mapping['destination']),
                        file=media,
                        message=message_text,
                        reply_to=reply_to,
                        silent=event.message.silent,
                        formatting_entities=original_entities if original_entities else None
                    )
                else:
                    sent_message = await client.send_message(
                        entity=int(mapping['destination']),
                        message=message_text,
                        reply_to=reply_to,
                        silent=event.message.silent,
                        formatting_entities=original_entities if original_entities else None,
                        link_preview=True
                    )
            else:
                if not message_text.strip():
                    reason = "Empty message after filtering"
                    await notify_blocked(event, mapping, pair_name, reason)
                    pair_stats[user_id][pair_name]['blocked'] += 1
                    return True
                sent_message = await send_split_message(
                    client,
                    int(mapping['destination']),
                    message_text,
                    reply_to=reply_to,
                    silent=event.message.silent,
                    entities=original_entities
                )

            await store_message_mapping(event, mapping, sent_message)
            pair_stats[user_id][pair_name]['forwarded'] += 1
            pair_stats[user_id][pair_name]['last_activity'] = datetime.now().isoformat()
            logger.info(f"Message forwarded from {mapping['source']} to {mapping['destination']} (ID: {sent_message.id})")
            return True

        except errors.FloodWaitError as e:
            wait_time = e.seconds
            logger.warning(f"Flood wait error, sleeping for {wait_time} seconds for pair '{pair_name}' (Source Msg ID: {source_msg_id})")
            await asyncio.sleep(wait_time)
        except errors.PollOptionInvalidError as e:
            logger.error(f"Poll option error for pair '{pair_name}' (Source Msg ID: {source_msg_id}): {e}")
            await notify_blocked(event, mapping, pair_name, f"Invalid poll options: {e}")
            return False
        except errors.ChatWriteForbiddenError as e:
            logger.warning(f"Bot forbidden to write in {mapping['destination']}. Disabling pair '{pair_name}'.")
            mapping['active'] = False
            save_mappings()
            if NOTIFY_CHAT_ID:
                await client.send_message(NOTIFY_CHAT_ID, f"⚠️ Disabled pair '{pair_name}' due to write permission error.")
            return False
        except errors.ChannelInvalidError as e:
            logger.warning(f"Invalid channel {mapping['destination']}. Disabling pair '{pair_name}'.")
            mapping['active'] = False
            save_mappings()
            if NOTIFY_CHAT_ID:
                await client.send_message(NOTIFY_CHAT_ID, f"⚠️ Disabled pair '{pair_name}' due to invalid channel.")
            return False
        except (errors.RPCError, ConnectionError) as e:
            logger.warning(f"Attempt {attempt + 1} failed for pair '{pair_name}' (Source Msg ID: {source_msg_id}): {e}")
            if attempt < MAX_RETRIES - 1:
                wait_time = RETRY_DELAY * (2 ** attempt)
                logger.info(f"Retrying in {wait_time} seconds...")
                await asyncio.sleep(wait_time)
            else:
                error_msg = f"❌ Failed to forward message for pair '{pair_name}' (Source Msg ID: {source_msg_id}) after {MAX_RETRIES} attempts. Error: {e}"
                logger.error(error_msg)
                if NOTIFY_CHAT_ID:
                    await client.send_message(NOTIFY_CHAT_ID, error_msg)
                return False
        except Exception as e:
            error_msg = f"⚠️ Unexpected error forwarding message for pair '{pair_name}' (Source Msg ID: {source_msg_id}): {e}"
            logger.error(error_msg, exc_info=True)
            if NOTIFY_CHAT_ID:
                await client.send_message(NOTIFY_CHAT_ID, error_msg)
            return False

async def edit_forwarded_message(event, mapping, user_id, pair_name):
    """Edit a forwarded message when the source message is edited."""
    try:
        if not hasattr(client, 'forwarded_messages'):
            client.forwarded_messages = {}
            logger.info("Initialized missing forwarded_messages attribute.")
        mapping_key = f"{mapping['source']}:{event.message.id}"
        if mapping_key not in client.forwarded_messages:
            logger.warning(f"No mapping found for message: {mapping_key}")
            return

        forwarded_msg_id = client.forwarded_messages[mapping_key]
        forwarded_msg = await client.get_messages(int(mapping['destination']), ids=forwarded_msg_id)
        if not forwarded_msg:
            logger.warning(f"Forwarded message {forwarded_msg_id} not found in destination {mapping['destination']}")
            del client.forwarded_messages[mapping_key]
            return

        message_text = event.message.raw_text or ""
        text_lower = message_text.lower()
        original_entities = event.message.entities or []
        media = event.message.media

        if isinstance(media, MessageMediaPhoto) and mapping.get('blocked_image_hashes'):
            photo = await client.download_media(event.message, bytes)
            image = Image.open(io.BytesIO(photo))
            image_hash = str(imagehash.phash(image))
            if image_hash in mapping['blocked_image_hashes']:
                await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
                reason = f"Image hash match: {image_hash}"
                await notify_blocked(event, mapping, pair_name, reason)
                pair_stats[user_id][pair_name]['blocked'] += 1
                pair_stats[user_id][pair_name]['deleted'] += 1
                return

        if mapping.get('blocked_sentences'):
            compiled_blocked = compile_blocked_sentences(mapping.get('blocked_sentences'))
            should_block, matching_sentence = check_blocked_sentences_fast(text_lower, compiled_blocked)
            if should_block:
                await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
                reason = f"Blocked sentence match: '{matching_sentence}'"
                await notify_blocked(event, mapping, pair_name, reason)
                pair_stats[user_id][pair_name]['blocked'] += 1
                pair_stats[user_id][pair_name]['deleted'] += 1
                return

        if mapping.get('blacklist') and message_text:
            automaton = build_blacklist_trie(mapping['blacklist'])
            message_text, found = filter_text_with_blacklist(message_text, automaton)
            if found and message_text.strip() == "***":
                await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
                reason = "Entire message blacklisted"
                await notify_blocked(event, mapping, pair_name, reason)
                pair_stats[user_id][pair_name]['blocked'] += 1
                pair_stats[user_id][pair_name]['deleted'] += 1
                return

        if mapping.get('block_urls', False) or mapping.get('blacklist_urls'):
            original_text = message_text
            message_text, _ = filter_urls(
                message_text,
                mapping.get('block_urls', False),
                mapping.get('blacklist_urls')
            )
            if message_text != original_text:
                original_entities = None

        if (mapping.get('header_pattern') or mapping.get('footer_pattern')) and message_text:
            message_text = remove_header_footer(
                message_text, mapping.get('header_pattern', ''), mapping.get('footer_pattern', '')
            )
            if message_text != event.message.raw_text:
                original_entities = None

        if mapping.get('remove_mentions', False) and message_text:
            message_text = re.sub(r'@[a-zA-Z0-9_]+|\[([^\]]+)\]\(tg://user\?id=\d+\)', '', message_text)
            message_text = re.sub(r'\s+', ' ', message_text).strip()
            original_entities = None

        if not message_text.strip() and not media:
            await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
            reason = "Empty message after filtering"
            await notify_blocked(event, mapping, pair_name, reason)
            pair_stats[user_id][pair_name]['blocked'] += 1
            pair_stats[user_id][pair_name]['deleted'] += 1
            return

        message_text = apply_custom_header_footer(
            message_text, mapping.get('custom_header', ''), mapping.get('custom_footer', '')
        )
        if message_text != event.message.raw_text:
            original_entities = None

        if isinstance(media, MessageMediaPoll):
            logger.info(f"Poll message {forwarded_msg_id} cannot be edited; deleting and resending")
            await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
            del client.forwarded_messages[mapping_key]
            await forward_message_with_retry(event, mapping, user_id, pair_name)
            return

        await client.edit_message(
            entity=int(mapping['destination']),
            message=forwarded_msg_id,
            text=message_text,
            file=media if media and isinstance(media, (MessageMediaPhoto, MessageMediaDocument)) else None,
            formatting_entities=original_entities if original_entities else None
        )
        pair_stats[user_id][pair_name]['edited'] += 1
        pair_stats[user_id][pair_name]['last_activity'] = datetime.now().isoformat()
        logger.info(f"Forwarded message {forwarded_msg_id} edited in {mapping['destination']}")

    except errors.MessageAuthorRequiredError:
        logger.error(f"Cannot edit message {forwarded_msg_id}: Bot must be the original author")
    except errors.MessageIdInvalidError:
        logger.error(f"Cannot edit message {forwarded_msg_id}: Message ID is invalid or deleted")
        if mapping_key in client.forwarded_messages:
            del client.forwarded_messages[mapping_key]
    except errors.FloodWaitError as e:
        logger.warning(f"Flood wait error while editing, sleeping for {e.seconds} seconds...")
        await asyncio.sleep(e.seconds)
    except Exception as e:
        logger.error(f"Error editing forwarded message {forwarded_msg_id}: {e}")

async def delete_forwarded_message(event, mapping, user_id, pair_name):
    """Delete a forwarded message when the source message is deleted."""
    try:
        if not hasattr(client, 'forwarded_messages'):
            client.forwarded_messages = {}
            logger.info("Initialized missing forwarded_messages attribute.")
        mapping_key = f"{mapping['source']}:{event.message.id}"
        if mapping_key not in client.forwarded_messages:
            logger.warning(f"No mapping found for deleted message: {mapping_key}")
            return

        forwarded_msg_id = client.forwarded_messages[mapping_key]
        await client.delete_messages(int(mapping['destination']), [forwarded_msg_id])
        pair_stats[user_id][pair_name]['deleted'] += 1
        pair_stats[user_id][pair_name]['last_activity'] = datetime.now().isoformat()
        logger.info(f"Forwarded message {forwarded_msg_id} deleted from {mapping['destination']}")
        del client.forwarded_messages[mapping_key]

    except errors.MessageIdInvalidError:
        logger.warning(f"Cannot delete message {forwarded_msg_id}: Already deleted or invalid")
        if mapping_key in client.forwarded_messages:
            del client.forwarded_messages[mapping_key]
    except Exception as e:
        logger.error(f"Error deleting forwarded message: {e}")

async def handle_reply_mapping(event, mapping):
    """Map replies from source to destination messages."""
    if not hasattr(event.message, 'reply_to') or not event.message.reply_to:
        return None
    try:
        source_reply_id = event.message.reply_to.reply_to_msg_id
        if not source_reply_id:
            return None
        mapping_key = f"{mapping['source']}:{source_reply_id}"
        if hasattr(client, 'forwarded_messages') and mapping_key in client.forwarded_messages:
            return client.forwarded_messages[mapping_key]
        replied_msg = await client.get_messages(int(mapping['source']), ids=source_reply_id)
        if replied_msg and replied_msg.text:
            dest_msgs = await client.get_messages(int(mapping['destination']), search=replied_msg.text[:20], limit=5)
            if dest_msgs:
                return dest_msgs[0].id
    except Exception as e:
        logger.error(f"Error handling reply mapping: {e}")
    return None

async def store_message_mapping(event, mapping, sent_message):
    """Store the mapping of source message ID to forwarded message ID."""
    try:
        if not hasattr(event.message, 'id'):
            return
        if not hasattr(client, 'forwarded_messages'):
            client.forwarded_messages = {}
        if len(client.forwarded_messages) >= MAX_MAPPING_HISTORY:
            oldest_key = next(iter(client.forwarded_messages))
            client.forwarded_messages.pop(oldest_key)
        source_msg_id = event.message.id
        mapping_key = f"{mapping['source']}:{source_msg_id}"
        client.forwarded_messages[mapping_key] = sent_message.id
    except Exception as e:
        logger.error(f"Error storing message mapping: {e}")

# Event Handlers
@client.on(events.NewMessage(pattern='(?i)^/sx$'))
async def start(event):
    """Handle the /sx command."""
    await event.reply("✅ ForwardBot Running!\nUse `/commands` for options.")

@client.on(events.NewMessage(pattern='(?i)^/commands$'))
async def list_commands(event):
    """Handle the /commands command to list available commands."""
    commands = """
    📋 ForwardBot Commands

    **Setup & Management**
    - `/setpair <name> <source> <dest> [yes|no]` - Add a forwarding pair (yes/no for mentions)
    - `/listpairs` - Show all pairs
    - `/pausepair <name>` - Pause a pair
    - `/startpair <name>` - Resume a pair
    - `/clearpairs` - Remove all pairs
    - `/togglementions <name>` - Toggle mention removal
    - `/monitor` - View pair stats
    - `/status` - Check bot status

    **🔍 Filters**
    - `/addblacklist <name> <word1,word2,...>` - Blacklist words
    - `/clearblacklist <name>` - Clear blacklist
    - `/showblacklist <name>` - Show blacklist
    - `/toggleurlblock <name>` - Toggle URL blocking
    - `/addurlblacklist <name> <url1,url2,...>` - Blacklist specific URLs
    - `/clearurlblacklist <name>` - Clear URL blacklist
    - `/setheader <name> <text>` - Set header to remove
    - `/setfooter <name> <text>` - Set footer to remove
    - `/clearheaderfooter <name>` - Clear header/footer

    **🖼️ Image Blocking and Watermarking**
    - `/blockimage <name>` - Block a specific image (reply to image)
    - `/clearblockedimages <name>` - Clear blocked images
    - `/showblockedimages <name>` - Show blocked image hashes
    - `/togglewatermark <name>` - Toggle watermark on/off
    - `/setwatermarktext <name> <text>` - Set watermark text
    - `/setwatermarkposition <name> <position>` - Set position (top-left, top-right, bottom-left, bottom-right, center, random)
    - `/setwatermarkfont <name> <font> [size]` - Set font and size
    - `/setwatermarkcolor <name> <color> [opacity]` - Set color and opacity (0.0-1.0)
    - `/watermarkinfo <name>` - Show watermark settings

    **✍️ Custom Text**
    - `/setcustomheader <name> <text>` - Set custom header
    - `/setcustomfooter <name> <text>` - Set custom footer
    - `/clearcustomheaderfooter <name>` - Clear custom text

    **🚫 Blocking**
    - `/blocksentence <name> <sentence>` - Block a sentence
    - `/clearblocksentences <name>` - Clear blocked sentences
    - `/showblocksentences <name>` - Show blocked sentences
    """
    await event.reply(commands)

@client.on(events.NewMessage(pattern='(?i)^/status$'))
async def status(event):
    """Handle the /status command to show bot status."""
    status_msg = f"🛠️ Bot Status\n" \
                 f"📡 Connected: {'✅' if is_connected else '❌'}\n" \
                 f"📥 Queue Size: {len(message_queue)}/{MAX_QUEUE_SIZE}\n" \
                 f"📊 Total Pairs: {sum(len(pairs) for pairs in channel_mappings.values())}"
    await event.reply(status_msg)

@client.on(events.NewMessage(pattern='(?i)^/monitor$'))
async def monitor_pairs(event):
    """Handle the /monitor command to show pair statistics."""
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or not channel_mappings[user_id]:
        await event.reply("❌ No forwarding pairs found.")
        return

    header = "📊 Forwarding Monitor\n--------------------\n"
    footer = f"\n--------------------\n📥 Total Queued: {len(message_queue)}"
    report = []
    for pair_name, data in channel_mappings[user_id].items():
        stats = pair_stats.get(user_id, {}).get(pair_name, {
            'forwarded': 0, 'edited': 0, 'deleted': 0, 'blocked': 0, 'queued': 0, 'last_activity': None
        })
        last_activity = stats['last_activity'] or 'N/A'
        if len(last_activity) > 20:
            last_activity = last_activity[:17] + "..."
        report.append(
            f"📌 {pair_name}\n"
            f"   ➡️ Route: {data['source']} → {data['destination']}\n"
            f"   ✅ Status: {'Active' if data['active'] else 'Paused'}\n"
            f"   📈 Stats: Fwd: {stats['forwarded']} | Edt: {stats['edited']} | Del: {stats['deleted']} | Blk: {stats['blocked']} | Que: {stats['queued']}\n"
            f"   ⏰ Last: {last_activity}\n"
            f"---------------"
        )
    full_message = header + "\n".join(report) + footer
    await send_split_message_event(event, full_message)

async def send_split_message_event(event, full_message):
    """Send a long message as multiple parts in response to an event."""
    if len(full_message) <= MAX_MESSAGE_LENGTH:
        await event.reply(full_message)
        return
    parts = [full_message[i:i + MAX_MESSAGE_LENGTH] for i in range(0, len(full_message), MAX_MESSAGE_LENGTH)]
    for i, part in enumerate(parts, 1):
        await event.reply(f"📜 Part {i}/{len(parts)}\n{part}")
        await asyncio.sleep(0.5)

@client.on(events.NewMessage(pattern=r'/setpair (\S+) (\S+) (\S+)(?: (yes|no))?'))
async def set_pair(event):
    """Handle the /setpair command to add a forwarding pair."""
    pair_name, source, destination, remove_mentions = event.pattern_match.groups()
    user_id = str(event.sender_id)
    remove_mentions = remove_mentions == "yes"

    logger.info(f"Setting pair {pair_name} for user {user_id}: {source} -> {destination}")

    if user_id not in channel_mappings:
        channel_mappings[user_id] = {}
    if user_id not in pair_stats:
        pair_stats[user_id] = {}

    channel_mappings[user_id][pair_name] = {
        'source': source,
        'destination': destination,
        'active': True,
        'remove_mentions': remove_mentions,
        'blacklist': [],
        'block_urls': False,
        'blacklist_urls': [],
        'header_pattern': '',
        'footer_pattern': '',
        'custom_header': '',
        'custom_footer': '',
        'blocked_sentences': [],
        'blocked_image_hashes': [],
        'watermark': {
            'enabled': False,
            'text': 'Watermark',
            'position': 'bottom-right',
            'font': 'arial',
            'font_size': 36,
            'color': 'white',
            'opacity': 0.7
        }
    }
    pair_stats[user_id][pair_name] = {'forwarded': 0, 'edited': 0, 'deleted': 0, 'blocked': 0, 'queued': 0, 'last_activity': None}
    save_mappings()
    await event.reply(f"✅ Pair '{pair_name}' Added\n{source} ➡️ {destination}\nMentions: {'✅' if remove_mentions else '❌'}")

@client.on(events.NewMessage(pattern=r'/blockimage (\S+)'))
async def block_image(event):
    """Handle the /blockimage command to block an image by its hash."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)

    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found. Use /listpairs or /setpair.")
        return

    if not event.message.reply_to:
        await event.reply("📷 Please reply to an image to block it.")
        return

    replied_msg = await event.get_reply_message()
    if not isinstance(replied_msg.media, MessageMediaPhoto):
        await event.reply("📷 Please reply to a photo message.")
        return

    try:
        photo = await client.download_media(replied_msg, bytes)
        image = Image.open(io.BytesIO(photo))
        image_hash = str(imagehash.phash(image))

        channel_mappings[user_id][pair_name].setdefault('blocked_image_hashes', []).append(image_hash)
        channel_mappings[user_id][pair_name]['blocked_image_hashes'] = list(set(channel_mappings[user_id][pair_name]['blocked_image_hashes']))
        save_mappings()

        logger.info(f"Blocked image hash {image_hash} for pair {pair_name} by user {user_id}")
        await event.reply(f"🖼️ Image hash {image_hash} blocked for '{pair_name}'")
    except Exception as e:
        logger.error(f"Error blocking image: {e}", exc_info=True)
        await event.reply(f"❌ Error blocking image: {str(e)}")

@client.on(events.NewMessage(pattern=r'/listpairs'))
async def list_pairs(event):
    """Handle the /listpairs command to show all pairs for the user."""
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or not channel_mappings[user_id]:
        await event.reply("❌ No forwarding pairs found.")
        return
    pairs_list = "\n".join(
        f"📌 {name}: {data['source']} ➡️ {data['destination']} [{'Active' if data['active'] else 'Paused'}]"
        for name, data in channel_mappings[user_id].items()
    )
    await event.reply(f"📋 Your Pairs:\n{pairs_list}")

@client.on(events.NewMessage(pattern=r'/pausepair (\S+)'))
async def pause_pair(event):
    """Handle the /pausepair command to pause a forwarding pair."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['active'] = False
    save_mappings()
    await event.reply(f"⏸️ Pair '{pair_name}' paused.")

@client.on(events.NewMessage(pattern=r'/startpair (\S+)'))
async def start_pair(event):
    """Handle the /startpair command to resume a forwarding pair."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['active'] = True
    save_mappings()
    await event.reply(f"▶️ Pair '{pair_name}' started.")

@client.on(events.NewMessage(pattern=r'/clearpairs'))
async def clear_pairs(event):
    """Handle the /clearpairs command to remove all pairs for the user."""
    user_id = str(event.sender_id)
    if user_id in channel_mappings:
        del channel_mappings[user_id]
        if user_id in pair_stats:
            del pair_stats[user_id]
        save_mappings()
        await event.reply("🗑️ All pairs cleared.")
    else:
        await event.reply("❌ No pairs to clear.")

@client.on(events.NewMessage(pattern=r'/togglementions (\S+)'))
async def toggle_mentions(event):
    """Handle the /togglementions command to toggle mention removal."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    current = channel_mappings[user_id][pair_name]['remove_mentions']
    channel_mappings[user_id][pair_name]['remove_mentions'] = not current
    save_mappings()
    await event.reply(f"🔍 Mentions removal for '{pair_name}' set to {'✅' if not current else '❌'}.")

@client.on(events.NewMessage(pattern=r'/addblacklist (\S+) (.+)'))
async def add_blacklist(event):
    """Handle the /addblacklist command to add words to the blacklist."""
    pair_name, words = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    word_list = [word.strip() for word in words.split(',')]
    channel_mappings[user_id][pair_name]['blacklist'].extend(word_list)
    channel_mappings[user_id][pair_name]['blacklist'] = list(set(channel_mappings[user_id][pair_name]['blacklist']))
    save_mappings()
    await event.reply(f"🚫 Added {len(word_list)} words to blacklist for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/clearblacklist (\S+)'))
async def clear_blacklist(event):
    """Handle the /clearblacklist command to clear the blacklist."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['blacklist'] = []
    save_mappings()
    await event.reply(f"🗑️ Blacklist cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/showblacklist (\S+)'))
async def show_blacklist(event):
    """Handle the /showblacklist command to display the blacklist."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    blacklist = channel_mappings[user_id][pair_name]['blacklist']
    if not blacklist:
        await event.reply(f"📋 Blacklist for '{pair_name}' is empty.")
        return
    await event.reply(f"📋 Blacklist for '{pair_name}':\n{', '.join(blacklist)}")

@client.on(events.NewMessage(pattern=r'/toggleurlblock (\S+)'))
async def toggle_url_block(event):
    """Handle the /toggleurlblock command to toggle URL blocking."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    current = channel_mappings[user_id][pair_name]['block_urls']
    channel_mappings[user_id][pair_name]['block_urls'] = not current
    save_mappings()
    await event.reply(f"🔗 URL blocking for '{pair_name}' set to {'✅' if not current else '❌'}.")

@client.on(events.NewMessage(pattern=r'/addurlblacklist (\S+) (.+)'))
async def add_url_blacklist(event):
    """Handle the /addurlblacklist command to add URLs to the blacklist."""
    pair_name, urls = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    url_list = [url.strip() for url in urls.split(',')]
    channel_mappings[user_id][pair_name]['blacklist_urls'].extend(url_list)
    channel_mappings[user_id][pair_name]['blacklist_urls'] = list(set(channel_mappings[user_id][pair_name]['blacklist_urls']))
    save_mappings()
    await event.reply(f"🚫 Added {len(url_list)} URLs to blacklist for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/clearurlblacklist (\S+)'))
async def clear_url_blacklist(event):
    """Handle the /clearurlblacklist command to clear the URL blacklist."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['blacklist_urls'] = []
    save_mappings()
    await event.reply(f"🗑️ URL blacklist cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/setheader (\S+) (.+)'))
async def set_header(event):
    """Handle the /setheader command to set a header to remove."""
    pair_name, header = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['header_pattern'] = header
    save_mappings()
    await event.reply(f"📏 Header set for '{pair_name}': {header}")

@client.on(events.NewMessage(pattern=r'/setfooter (\S+) (.+)'))
async def set_footer(event):
    """Handle the /setfooter command to set a footer to remove."""
    pair_name, footer = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['footer_pattern'] = footer
    save_mappings()
    await event.reply(f"📏 Footer set for '{pair_name}': {footer}")

@client.on(events.NewMessage(pattern=r'/clearheaderfooter (\S+)'))
async def clear_header_footer(event):
    """Handle the /clearheaderfooter command to clear header and footer."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['header_pattern'] = ''
    channel_mappings[user_id][pair_name]['footer_pattern'] = ''
    save_mappings()
    await event.reply(f"🗑️ Header and footer cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/setcustomheader (\S+) (.+)'))
async def set_custom_header(event):
    """Handle the /setcustomheader command to set a custom header."""
    pair_name, header = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['custom_header'] = header
    save_mappings()
    await event.reply(f"✍️ Custom header set for '{pair_name}': {header}")

@client.on(events.NewMessage(pattern=r'/setcustomfooter (\S+) (.+)'))
async def set_custom_footer(event):
    """Handle the /setcustomfooter command to set a custom footer."""
    pair_name, footer = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['custom_footer'] = footer
    save_mappings()
    await event.reply(f"✍️ Custom footer set for '{pair_name}': {footer}")

@client.on(events.NewMessage(pattern=r'/clearcustomheaderfooter (\S+)'))
async def clear_custom_header_footer(event):
    """Handle the /clearcustomheaderfooter command to clear custom header and footer."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['custom_header'] = ''
    channel_mappings[user_id][pair_name]['custom_footer'] = ''
    save_mappings()
    await event.reply(f"🗑️ Custom header and footer cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/blocksentence (\S+) (.+)'))
async def block_sentence(event):
    """Handle the /blocksentence command to block a sentence."""
    pair_name, sentence = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['blocked_sentences'].append(sentence)
    channel_mappings[user_id][pair_name]['blocked_sentences'] = list(set(channel_mappings[user_id][pair_name]['blocked_sentences']))
    save_mappings()
    await event.reply(f"🚫 Sentence blocked for '{pair_name}': {sentence}")

@client.on(events.NewMessage(pattern=r'/clearblocksentences (\S+)'))
async def clear_blocked_sentences(event):
    """Handle the /clearblocksentences command to clear blocked sentences."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['blocked_sentences'] = []
    save_mappings()
    await event.reply(f"🗑️ Blocked sentences cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/showblocksentences (\S+)'))
async def show_blocked_sentences(event):
    """Handle the /showblocksentences command to display blocked sentences."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    blocked_sentences = channel_mappings[user_id][pair_name]['blocked_sentences']
    if not blocked_sentences:
        await event.reply(f"📋 Blocked sentences for '{pair_name}' is empty.")
        return
    await event.reply(f"📋 Blocked sentences for '{pair_name}':\n" + "\n".join(blocked_sentences))

@client.on(events.NewMessage(pattern=r'/clearblockedimages (\S+)'))
async def clear_blocked_images(event):
    """Handle the /clearblockedimages command to clear blocked image hashes."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    channel_mappings[user_id][pair_name]['blocked_image_hashes'] = []
    save_mappings()
    await event.reply(f"🗑️ Blocked images cleared for '{pair_name}'.")

@client.on(events.NewMessage(pattern=r'/showblockedimages (\S+)'))
async def show_blocked_images(event):
    """Handle the /showblockedimages command to display blocked image hashes."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return
    blocked_images = channel_mappings[user_id][pair_name]['blocked_image_hashes']
    if not blocked_images:
        await event.reply(f"📋 Blocked images for '{pair_name}' is empty.")
        return
    await event.reply(f"📋 Blocked image hashes for '{pair_name}':\n" + "\n".join(blocked_images))

@client.on(events.NewMessage(pattern=r'/togglewatermark (\S+)'))
async def toggle_watermark(event):
    """Toggle watermarking for a pair."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': False,
            'text': 'Watermark',
            'position': 'bottom-right',
            'font': 'arial',
            'font_size': 36,
            'color': 'white',
            'opacity': 0.7,
        }

    current = channel_mappings[user_id][pair_name]['watermark']['enabled']
    channel_mappings[user_id][pair_name]['watermark']['enabled'] = not current
    save_mappings()
    status = "enabled" if not current else "disabled"
    await event.reply(f"🖌️ Watermark for '{pair_name}' {status}.")

@client.on(events.NewMessage(pattern=r'/setwatermarktext (\S+) (.+)'))
async def set_watermark_text(event):
    """Set the watermark text for a pair."""
    pair_name, text = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': True,
            'text': text,
            'position': 'bottom-right',
            'font': 'arial',
            'font_size': 36,
            'color': 'white',
            'opacity': 0.7,
        }
    else:
        channel_mappings[user_id][pair_name]['watermark']['text'] = text
        channel_mappings[user_id][pair_name]['watermark']['enabled'] = True

    save_mappings()
    await event.reply(f"✍️ Watermark text for '{pair_name}' set to: {text}")

@client.on(events.NewMessage(pattern=r'/setwatermarkposition (\S+) (top-left|top-right|bottom-left|bottom-right|center|random)'))
async def set_watermark_position(event):
    """Set the watermark position for a pair."""
    pair_name, position = event.pattern_match.group(1), event.pattern_match.group(2)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': True,
            'text': 'Watermark',
            'position': position,
            'font': 'arial',
            'font_size': 36,
            'color': 'white',
            'opacity': 0.7,
        }
    else:
        channel_mappings[user_id][pair_name]['watermark']['position'] = position

    save_mappings()
    await event.reply(f"📍 Watermark position for '{pair_name}' set to: {position}")

@client.on(events.NewMessage(pattern=r'/setwatermarkfont (\S+) (\S+)(?: (\d+))?'))
async def set_watermark_font(event):
    """Set the watermark font and size for a pair."""
    pair_name, font = event.pattern_match.group(1), event.pattern_match.group(2)
    size = event.pattern_match.group(3)
    size = int(size) if size else 36
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': True,
            'text': 'Watermark',
            'position': 'bottom-right',
            'font': font,
            'font_size': size,
            'color': 'white',
            'opacity': 0.7,
        }
    else:
        channel_mappings[user_id][pair_name]['watermark']['font'] = font
        channel_mappings[user_id][pair_name]['watermark']['font_size'] = size

    save_mappings()
    await event.reply(f"🔤 Watermark font for '{pair_name}' set to: {font}, size: {size}")

@client.on(events.NewMessage(pattern=r'/setwatermarkcolor (\S+) (\S+)(?: (0\.\d+))?'))
async def set_watermark_color(event):
    """Set the watermark color and opacity for a pair."""
    pair_name, color = event.pattern_match.group(1), event.pattern_match.group(2)
    opacity = event.pattern_match.group(3)
    opacity = float(opacity) if opacity else 0.7
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': True,
            'text': 'Watermark',
            'position': 'bottom-right',
            'font': 'arial',
            'font_size': 36,
            'color': color,
            'opacity': opacity,
        }
    else:
        channel_mappings[user_id][pair_name]['watermark']['color'] = color
        channel_mappings[user_id][pair_name]['watermark']['opacity'] = opacity

    save_mappings()
    await event.reply(f"🎨 Watermark color for '{pair_name}' set to: {color}, opacity: {opacity}")

@client.on(events.NewMessage(pattern=r'/watermarkinfo (\S+)'))
async def watermark_info(event):
    """Display current watermark settings for a pair."""
    pair_name = event.pattern_match.group(1)
    user_id = str(event.sender_id)
    if user_id not in channel_mappings or pair_name not in channel_mappings[user_id]:
        await event.reply("❌ Pair not found.")
        return

    if 'watermark' not in channel_mappings[user_id][pair_name]:
        channel_mappings[user_id][pair_name]['watermark'] = {
            'enabled': False,
            'text': 'Watermark',
            'position': 'bottom-right',
            'font': 'arial',
            'font_size': 36,
            'color': 'white',
            'opacity': 0.7,
        }
        save_mappings()

    watermark = channel_mappings[user_id][pair_name]['watermark']
    info = (
        f"🖌️ Watermark Settings for '{pair_name}':\n"
        f"✅ Enabled: {'Yes' if watermark['enabled'] else 'No'}\n"
        f"✍️ Text: {watermark['text']}\n"
        f"📍 Position: {watermark['position']}\n"
        f"🔤 Font: {watermark['font']}\n"
        f"📏 Font Size: {watermark['font_size']}\n"
        f"🎨 Color: {watermark['color']}\n"
        f"🔍 Opacity: {watermark['opacity']}"
    )
    await event.reply(info)

@client.on(events.NewMessage)
async def forward_messages(event):
    """Handle new messages and queue them for forwarding."""
    queued_time = datetime.now()
    for user_id, pairs in channel_mappings.items():
        for pair_name, mapping in pairs.items():
            if mapping['active'] and event.chat_id == int(mapping['source']):
                message_queue.append((event, mapping, user_id, pair_name, queued_time))
                pair_stats[user_id][pair_name]['queued'] += 1
                logger.info(f"Message queued for '{pair_name}' at {queued_time.isoformat()}")
                return

@client.on(events.MessageEdited)
async def handle_message_edit(event):
    """Handle edited messages and update forwarded copies."""
    if not is_connected:
        return
    for user_id, pairs in channel_mappings.items():
        for pair_name, mapping in pairs.items():
            if mapping['active'] and event.chat_id == int(mapping['source']):
                try:
                    await edit_forwarded_message(event, mapping, user_id, pair_name)
                except Exception as e:
                    logger.error(f"Error editing for '{pair_name}': {e}")
                return

@client.on(events.MessageDeleted)
async def handle_message_deleted(event):
    """Handle deleted messages and remove forwarded copies."""
    if not is_connected:
        return
    for user_id, pairs in channel_mappings.items():
        for pair_name, mapping in pairs.items():
            if mapping['active'] and event.chat_id == int(mapping['source']):
                try:
                    for deleted_id in event.deleted_ids:
                        event.message.id = deleted_id
                        await delete_forwarded_message(event, mapping, user_id, pair_name)
                except Exception as e:
                    logger.error(f"Error handling deletion for '{pair_name}': {e}")
                return

# Periodic Tasks
async def check_connection_status():
    """Periodically check and update connection status."""
    global is_connected
    while True:
        current_status = client.is_connected()
        if current_status and not is_connected:
            is_connected = True
            logger.info("📡 Connection established")
        elif not current_status and is_connected:
            is_connected = False
            logger.warning("📡 Connection lost")
        await asyncio.sleep(5)

async def queue_worker():
    """Process messages from the queue concurrently."""
    while True:
        if is_connected and message_queue:
            try:
                event, mapping, user_id, pair_name, queued_time = message_queue.popleft()
                await forward_message_with_retry(event, mapping, user_id, pair_name)
                await asyncio.sleep(FORWARD_DELAY)
            except Exception as e:
                logger.error(f"Worker error: {e}")
        else:
            await asyncio.sleep(1)

async def check_queue_inactivity():
    """Check for messages stuck in the queue and notify."""
    while True:
        await asyncio.sleep(60)
        if not is_connected or not NOTIFY_CHAT_ID or not message_queue:
            continue
        current_time = datetime.now()
        for i, (event, mapping, user_id, pair_name, queued_time) in enumerate(message_queue):
            wait_duration = (current_time - queued_time).total_seconds()
            if wait_duration > QUEUE_INACTIVITY_THRESHOLD:
                source_msg_id = event.message.id if hasattr(event.message, 'id') else "Unknown"
                alert_msg = (
                    f"⏳ Queue Inactivity Alert: Message for pair '{pair_name}' "
                    f"(Source Msg ID: {source_msg_id}) has been in queue for "
                    f"{int(wait_duration // 60)} minutes. Queue size: {len(message_queue)}"
                )
                logger.warning(alert_msg)
                await client.send_message(NOTIFY_CHAT_ID, alert_msg)
                break

async def check_pair_inactivity():
    """Check for inactive pairs and notify."""
    while True:
        await asyncio.sleep(300)
        if not is_connected or not NOTIFY_CHAT_ID:
            continue
        current_time = datetime.now()
        for user_id, pairs in channel_mappings.items():
            for pair_name, mapping in pairs.items():
                if not mapping['active']:
                    continue
                stats = pair_stats.get(user_id, {}).get(pair_name, {})
                last_activity_str = stats.get('last_activity')
                if not last_activity_str:
                    continue
                last_activity = datetime.fromisoformat(last_activity_str)
                inactivity_duration = (current_time - last_activity).total_seconds()
                if inactivity_duration > INACTIVITY_THRESHOLD:
                    await client.send_message(
                        NOTIFY_CHAT_ID,
                        f"⏰ Inactivity Alert: Pair '{pair_name}' inactive for over {INACTIVITY_THRESHOLD // 3600} hours."
                    )
                    pair_stats[user_id][pair_name]['last_activity'] = datetime.now().isoformat()

async def send_periodic_report():
    """Send periodic reports on pair statistics."""
    while True:
        await asyncio.sleep(21600)
        if not is_connected or not MONITOR_CHAT_ID:
            continue
        for user_id in channel_mappings:
            header = "📊 6-Hour Report\n--------------------\n"
            report = []
            total_queued = len(message_queue)
            for pair_name, data in channel_mappings[user_id].items():
                stats = pair_stats.get(user_id, {}).get(pair_name, {
                    'forwarded': 0, 'edited': 0, 'deleted': 0, 'blocked': 0, 'queued': 0, 'last_activity': None
                })
                report.append(
                    f"📌 {pair_name}\n"
                    f"   ➡️ Route: {data['source']} → {data['destination']}\n"
                    f"   ✅ Status: {'Active' if data['active'] else 'Paused'}\n"
                    f"   📈 Fwd: {stats['forwarded']} | Edt: {stats['edited']} | Del: {stats['deleted']}\n"
                    f"   🚫 Blk: {stats['blocked']} | 📥 Que: {stats['queued']}\n"
                    f"---------------"
                )
            full_message = header + "\n".join(report) + f"\n📥 Queued: {total_queued}"
            try:
                await client.send_message(MONITOR_CHAT_ID, full_message)
                logger.info("Sent periodic report")
            except Exception as e:
                logger.error(f"Error sending report: {e}")

# Main Function
async def main():
    """Start the bot and manage periodic tasks."""
    load_mappings()
    tasks = [
        check_connection_status(),
        send_periodic_report(),
        check_pair_inactivity(),
        check_queue_inactivity()
    ]
    for _ in range(NUM_WORKERS):
        tasks.append(queue_worker())
    for task in tasks:
        asyncio.create_task(task)
    logger.info("🤖 Bot is starting...")

    try:
        await client.start()
        if not await client.is_user_authorized():
            phone = input("Please enter your phone (or bot token): ")
            await client.start(phone=phone)
            code = input("Please enter the verification code you received: ")
            await client.sign_in(phone=phone, code=code)

        global is_connected, MONITOR_CHAT_ID, NOTIFY_CHAT_ID
        is_connected = client.is_connected()
        MONITOR_CHAT_ID = (await client.get_me()).id
        NOTIFY_CHAT_ID = MONITOR_CHAT_ID

        if is_connected:
            logger.info("📡 Initial connection established")
        else:
            logger.warning("📡 Initial connection not established")

        await client.run_until_disconnected()
    except Exception as e:
        logger.error(f"❌ Fatal error: {e}", exc_info=True)
    finally:
        logger.info("🤖 Bot is shutting down...")
        save_mappings()

if __name__ == "__main__":
    try:
        client.loop.run_until_complete(main())
    except KeyboardInterrupt:
        logger.info("🤖 Bot stopped by user")
    except Exception as e:
        logger.error(f"❌ Unexpected error: {e}", exc_info=True)
