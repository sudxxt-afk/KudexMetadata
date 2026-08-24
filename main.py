import asyncio
import html
import io
import logging
import os
import secrets
import sqlite3
import time
import zipfile
from datetime import datetime
from urllib.parse import quote
from xml.etree import ElementTree

import pillow_heif
from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import BaseFilter, Command, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import (
    BotCommand,
    BotCommandScopeChat,
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    LinkPreviewOptions,
    Message,
)
from PIL import Image
from PIL.ExifTags import GPSTAGS, TAGS
from mutagen import File as MutagenFile
from pypdf import PdfReader, PdfWriter

pillow_heif.register_heif_opener()

BOT_TOKEN = os.getenv("BOT_TOKEN")
DB_DIR = os.getenv("DB_DIR", os.path.dirname(os.path.abspath(__file__)))
DB_PATH = os.path.join(DB_DIR, "kudexmeta.db")

ADMIN_IDS = {
    int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x.isdigit()
}
ADMIN_USERNAMES = {
    x.strip().lower().lstrip("@")
    for x in os.getenv("ADMIN_USERNAMES", "").split(",")
    if x.strip()
}

START_TIME = time.time()
VERSION = "1.3"
OWNER = os.getenv("OWNER_USERNAME", "inhgalator").lstrip("@")

logging.basicConfig(level=logging.INFO)

dp = Dispatcher()

pending: dict[str, dict] = {}
PENDING_TTL = 1800
MAX_PENDING = 200

IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".heic", ".heif", ".bmp", ".tiff")
AUDIO_EXTS = (".mp3", ".flac", ".ogg", ".opus", ".m4a", ".wav", ".aac", ".wma")
OFFICE_EXTS = (".docx", ".xlsx", ".pptx")


def esc(value) -> str:
    return html.escape(str(value))


def human_size(n: int) -> str:
    if n >= 1024 * 1024:
        return f"{n / 1024 / 1024:.1f} МБ"
    return f"{n / 1024:.0f} КБ"


def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        """CREATE TABLE IF NOT EXISTS users(
            user_id INTEGER PRIMARY KEY,
            name TEXT,
            username TEXT,
            scanned INTEGER DEFAULT 0,
            cleaned INTEGER DEFAULT 0,
            gps_hits INTEGER DEFAULT 0,
            send_as_doc INTEGER DEFAULT 1,
            first_seen TEXT DEFAULT CURRENT_TIMESTAMP,
            last_seen TEXT DEFAULT CURRENT_TIMESTAMP)"""
    )
    conn.execute(
        """CREATE TABLE IF NOT EXISTS banned(
            user_id INTEGER PRIMARY KEY,
            reason TEXT,
            banned_at TEXT DEFAULT CURRENT_TIMESTAMP)"""
    )
    conn.execute(
        """CREATE TABLE IF NOT EXISTS admins(
            user_id INTEGER PRIMARY KEY,
            username TEXT,
            added_at TEXT DEFAULT CURRENT_TIMESTAMP)"""
    )
    return conn


admin_cache: set[int] = set()


def load_admins() -> None:
    with db_connect() as c:
        rows = c.execute("SELECT user_id FROM admins").fetchall()
    admin_cache.clear()
    admin_cache.update(ADMIN_IDS)
    admin_cache.update(r[0] for r in rows)


def touch_user(user_id: int, name: str | None, username: str | None) -> None:
    uname = (username or "").lstrip("@").lower()
    with db_connect() as c:
        c.execute(
            """INSERT INTO users(user_id, name, username) VALUES(?, ?, ?)
               ON CONFLICT(user_id) DO UPDATE SET name=excluded.name,
               username=excluded.username, last_seen=CURRENT_TIMESTAMP""",
            (user_id, name, username),
        )
        if uname and uname in ADMIN_USERNAMES:
            c.execute(
                "INSERT OR IGNORE INTO admins(user_id, username) VALUES(?, ?)",
                (user_id, uname),
            )
            admin_cache.add(user_id)


def is_admin(user_id: int, username: str | None = None) -> bool:
    if user_id in ADMIN_IDS or user_id in admin_cache:
        return True
    uname = (username or "").lstrip("@").lower()
    if uname and uname in ADMIN_USERNAMES:
        with db_connect() as c:
            c.execute(
                "INSERT OR IGNORE INTO admins(user_id, username) VALUES(?, ?)",
                (user_id, uname),
            )
        admin_cache.add(user_id)
        return True
    return False


class IsAdmin(BaseFilter):
    async def __call__(self, event: Message | CallbackQuery) -> bool:
        user = event.from_user
        return user is not None and is_admin(user.id, user.username)


def bump_stat(user_id: int, field: str) -> None:
    if field not in ("scanned", "cleaned", "gps_hits"):
        return
    with db_connect() as c:
        c.execute(f"UPDATE users SET {field} = {field} + 1 WHERE user_id=?", (user_id,))


def get_user_row(user_id: int) -> tuple[int, int, int, int]:
    with db_connect() as c:
        row = c.execute(
            "SELECT scanned, cleaned, gps_hits, send_as_doc FROM users WHERE user_id=?",
            (user_id,),
        ).fetchone()
    return row if row else (0, 0, 0, 1)


def set_send_mode(user_id: int, mode: int) -> None:
    with db_connect() as c:
        c.execute("UPDATE users SET send_as_doc=? WHERE user_id=?", (mode, user_id))


def ban_user(user_id: int, reason: str) -> bool:
    with db_connect() as c:
        exists = c.execute("SELECT 1 FROM users WHERE user_id=?", (user_id,)).fetchone()
        if not exists:
            return False
        c.execute(
            "INSERT OR REPLACE INTO banned(user_id, reason) VALUES(?, ?)",
            (user_id, reason),
        )
    return True


def unban_user(user_id: int) -> bool:
    with db_connect() as c:
        cur = c.execute("DELETE FROM banned WHERE user_id=?", (user_id,))
    return cur.rowcount > 0


def is_banned(user_id: int) -> bool:
    with db_connect() as c:
        return bool(c.execute("SELECT 1 FROM banned WHERE user_id=?", (user_id,)).fetchone())


EXIF_FIELDS = [
    ("DateTimeOriginal", "📅", "Дата съёмки"),
    ("Model", "📱", "Устройство"),
    ("Make", "🏭", "Производитель"),
    ("LensModel", "🔭", "Объектив"),
    ("Software", "💻", "Обработка"),
    ("ISOSpeedRatings", "💡", "ISO"),
    ("FNumber", "🔘", "Диафрагма"),
    ("ExposureTime", "⏱", "Выдержка"),
    ("FocalLength", "🎯", "Фокусное"),
]


def get_exif(image: Image.Image) -> dict:
    try:
        raw = image.getexif()
    except Exception:
        return {}
    exif = {}
    for tag_id, value in raw.items():
        exif[TAGS.get(tag_id, tag_id)] = value
    for tag_id, value in raw.get_ifd(0x8769).items():
        exif[TAGS.get(tag_id, tag_id)] = value
    gps_ifd = raw.get_ifd(0x8825)
    if gps_ifd:
        exif["GPSInfo"] = {GPSTAGS.get(k, k): v for k, v in gps_ifd.items()}
    return {k: v for k, v in exif.items() if v is not None}


def gps_to_decimal(gps: dict) -> tuple[float, float] | None:
    def convert(coord):
        d, m, s = coord
        return float(d) + float(m) / 60 + float(s) / 3600

    try:
        lat = convert(gps["GPSLatitude"])
        if gps.get("GPSLatitudeRef") == "S":
            lat = -lat
        lon = convert(gps["GPSLongitude"])
        if gps.get("GPSLongitudeRef") == "W":
            lon = -lon
        return lat, lon
    except Exception:
        return None


def fmt_value(tag: str, value):
    if value is None:
        return None
    if isinstance(value, bytes):
        try:
            value = value.decode(errors="ignore").strip("\x00")
        except Exception:
            return None
    if tag == "FNumber":
        try:
            v = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
            return f"f/{v:.1f}"
        except Exception:
            return None
    if tag == "ExposureTime":
        try:
            v = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
            return f"1/{round(1 / v)} с" if v < 1 else f"{v:g} с"
        except Exception:
            return None
    if tag == "FocalLength":
        try:
            v = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
            return f"{v:g} мм"
        except Exception:
            return None
    if tag in ("DateTimeOriginal", "DateTime", "DateTimeDigitized"):
        try:
            return datetime.strptime(str(value), "%Y:%m:%d %H:%M:%S").strftime("%d.%m.%Y · %H:%M")
        except Exception:
            return str(value)
    text = str(value).strip()
    return text or None


def count_fields(exif: dict) -> int:
    n = 0
    for value in exif.values():
        n += len(value) if isinstance(value, dict) else 1
    return n


def risk_level(exif: dict, coords) -> int:
    if not exif:
        return 0
    level = 2
    if coords:
        level += 2
    elif len(exif) > 12:
        level += 1
    return min(level, 5)


RISK_LABELS = {
    0: ("ЧИСТО ✨", "метаданных нет"),
    2: ("НИЗКИЙ 🟢", "есть базовые теги"),
    3: ("СРЕДНИЙ 🟡", "много скрытых данных"),
    4: ("ВЫСОКИЙ 🟠", "обнаружены координаты!"),
    5: ("КРИТИЧЕСКИЙ 🔴", "твоё местоположение внутри!"),
}


def risk_block(level: int) -> str:
    label, hint = RISK_LABELS[level]
    filled = max(level, 1)
    icon = "🔴" if level >= 4 else "🟡" if level >= 2 else "🟢"
    bar = icon * filled + "⚪" * (5 - filled)
    if level == 0:
        bar = "🟢🟢🟢🟢🟢"
    return (
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"<b>УРОВЕНЬ РИСКА:</b> {label}\n"
        f"{bar}\n"
        f"<i>{hint}</i>"
    )


def format_value_tag(tag: str, value):
    if isinstance(value, dict):
        return ", ".join(f"{GPSTAGS.get(k, k)}={v}" for k, v in value.items())
    return fmt_value(tag, value)


def build_details(exif: dict) -> str | None:
    if not exif:
        return None
    lines = []
    for tag, value in sorted(exif.items()):
        rendered = format_value_tag(tag, value)
        if rendered:
            lines.append(f"{tag}: {rendered}"[:120])
    if not lines:
        return None
    head = lines[:40]
    rest = len(lines) - len(head)
    body = "\n".join(esc(line) for line in head)
    if rest > 0:
        body += f"\n… и ещё {rest} полей"
    return body


def strip_image(data: bytes):
    image = Image.open(io.BytesIO(data))
    clean = Image.new(image.mode, image.size)
    clean.putdata(list(image.getdata()))
    buf = io.BytesIO()
    fmt = (image.format or "JPEG").upper()
    if fmt in ("JPEG", "MPO"):
        clean.save(buf, "JPEG", quality=95, subsampling=0)
        return buf.getvalue(), "cleaned.jpg"
    if fmt == "PNG":
        clean.save(buf, "PNG", optimize=True)
        return buf.getvalue(), "cleaned.png"
    if fmt == "WEBP":
        clean.save(buf, "WEBP", quality=95)
        return buf.getvalue(), "cleaned.webp"
    clean.convert("RGB").save(buf, "JPEG", quality=95)
    return buf.getvalue(), "cleaned.jpg"


def analyze_pdf(data: bytes):
    reader = PdfReader(io.BytesIO(data))
    meta = reader.metadata or {}
    pages = len(reader.pages)

    fields = [
        ("📝", "Заголовок", meta.get("/Title")),
        ("✍️", "Автор", meta.get("/Author")),
        ("🏷", "Тема", meta.get("/Subject")),
        ("🔑", "Ключевые слова", meta.get("/Keywords")),
        ("🏭", "Создатель", meta.get("/Creator")),
        ("💻", "Продюсер", meta.get("/Producer")),
        ("📅", "Создан", meta.get("/CreationDate")),
        ("🔄", "Изменён", meta.get("/ModDate")),
    ]
    rows = [f"{icon} <b>{title}:</b> {esc(v)}" for icon, title, v in fields if v]
    total = sum(1 for _, _, v in fields if v) + 3

    text = [
        "📕 <b>PDF-документ</b>",
        f"📄 Страниц: <b>{pages}</b>",
    ]
    if rows:
        text.append("┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈")
        text.extend(rows[:7])
    text.append("")
    text.append(risk_block(min(4, 2 + (1 if rows else 0))))
    summary = {"total": total}
    return "\n".join(text), summary


def clean_pdf(data: bytes):
    reader = PdfReader(io.BytesIO(data))
    writer = PdfWriter()
    for page in reader.pages:
        writer.add_page(page)
    writer.add_metadata({"/Producer": "", "/Creator": ""})
    buf = io.BytesIO()
    writer.write(buf)
    return buf.getvalue(), "cleaned.pdf"


OFFICE_NS = {
    "cp": "http://schemas.openxmlformats.org/package/2006/metadata/core-properties",
    "dc": "http://purl.org/dc/elements/1.1/",
    "dcterms": "http://purl.org/dc/terms/",
}

OFFICE_ICONS = {
    "docx": "📘", "xlsx": "📗", "pptx": "📙",
}


def analyze_office(data: bytes, name: str):
    ext = (name.rsplit(".", 1)[-1] if "." in name else "").lower()
    icon = OFFICE_ICONS.get(ext, "📦")
    rows = []
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        core_name = next((n for n in z.namelist() if n.endswith("docProps/core.xml")), None)
        app_name = next((n for n in z.namelist() if n.endswith("docProps/app.xml")), None)
        if core_name:
            root = ElementTree.fromstring(z.read(core_name))
            mapping = [
                ("dc:title", "📝", "Заголовок"),
                ("dc:subject", "🏷", "Тема"),
                ("dc:creator", "✍️", "Автор"),
                ("cp:lastModifiedBy", "👤", "Последний редактор"),
                ("dcterms:created", "📅", "Создан"),
                ("dcterms:modified", "🔄", "Изменён"),
                ("dc:description", "💬", "Описание"),
            ]
            for path, ic, title in mapping:
                el = root.find(path, OFFICE_NS)
                if el is not None and el.text and el.text.strip():
                    rows.append(f"{ic} <b>{title}:</b> {esc(el.text.strip())}")
        if app_name:
            root = ElementTree.fromstring(z.read(app_name))
            for tag, title in (("Application", "Программа"), ("Company", "Организация")):
                el = root.find(tag)
                if el is not None and el.text and el.text.strip():
                    rows.append(f"💻 <b>{title}:</b> {esc(el.text.strip())}")

    text = [
        f"{icon} <b>Документ Office</b>",
        f"📄 {esc(name)}",
    ]
    if rows:
        text.append("┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈")
        text.extend(rows[:8])
    text.append("")
    if rows:
        text.append("⚠️ Внутри документа найдены <b>личные данные автора</b>")
    else:
        text.append("✅ Скрытых данных не найдено")
    return "\n".join(text)


def analyze_audio(data: bytes, name: str):
    try:
        audio = MutagenFile(io.BytesIO(data))
    except Exception:
        return None
    if audio is None:
        return None
    info = audio.info
    rows = []
    duration = getattr(info, "length", 0)
    mins, secs = divmod(int(duration), 60)
    rows.append(f"⏱ <b>Длительность:</b> {mins}:{secs:02d}")
    bitrate = getattr(info, "bitrate", 0)
    if bitrate:
        rows.append(f"🎚 <b>Битрейт:</b> {bitrate // 1000} кбит/с")

    tags_map = [
        ("title", "🎵", "Название"), ("TIT2", "🎵", "Название"), ("\xa9nam", "🎵", "Название"),
        ("artist", "🎤", "Исполнитель"), ("TPE1", "🎤", "Исполнитель"), ("\xa9ART", "🎤", "Исполнитель"),
        ("album", "💿", "Альбом"), ("TALB", "💿", "Альбом"), ("\xa9alb", "💿", "Альбом"),
        ("date", "📅", "Дата"), ("TDRC", "📅", "Дата"), ("\xa9day", "📅", "Дата"),
        ("genre", "🎭", "Жанр"), ("TCON", "🎭", "Жанр"), ("\xa9gen", "🎭", "Жанр"),
        ("organization", "🏢", "Лейбл"), ("\xa9too", "💻", "Кодировщик"), ("TENC", "💻", "Кодировщик"),
    ]
    seen = set()
    tags = audio.tags or {}
    if hasattr(tags, "keys"):
        for key, ic, title in tags_map:
            if key in tags and key not in seen:
                val = tags[key]
                if isinstance(val, list):
                    val = val[0]
                rows.append(f"{ic} <b>{title}:</b> {esc(str(val)[:60])}")
                seen.add(key)

    text = [
        f"🎧 <b>Аудиофайл</b>",
        f"📄 {esc(name)}",
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈",
        *rows[:8],
        "",
    ]
    has_tags = bool(seen)
    if has_tags:
        text.append("⚠️ Найдены теги с личными данными")
    else:
        text.append("✅ Теги не обнаружены")
    return "\n".join(text), bool(audio.tags)


def clean_audio(data: bytes, name: str):
    ext = name.rsplit(".", 1)[-1].lower() if "." in name else "mp3"
    out = io.BytesIO(data)
    audio = MutagenFile(out, easy=True)
    if audio is not None:
        try:
            audio.delete()
            audio.save(out)
        except Exception:
            pass
    return out.getvalue(), f"cleaned.{ext}"


def build_report(image: Image.Image, size: int, name: str | None):
    exif = get_exif(image)
    coords = gps_to_decimal(exif["GPSInfo"]) if isinstance(exif.get("GPSInfo"), dict) else None
    level = risk_level(exif, coords)

    display_name = name or f"photo.{(image.format or 'img').lower()}"
    lines = [
        f"📄 <b>{esc(display_name)}</b>",
        f"🖼 {image.width} × {image.height} · {esc(image.format or '?')} · {human_size(size)}",
    ]

    info_rows = []
    for tag, icon, title in EXIF_FIELDS:
        value = fmt_value(tag, exif.get(tag))
        if value:
            info_rows.append(f"{icon} <b>{title}:</b> {esc(value)}")

    if info_rows:
        lines.append("┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈")
        lines.extend(info_rows[:6])

    if coords:
        lat, lon = coords
        lines.append("┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈")
        lines.append(f"📍 <b>ГЕОЛОКАЦИЯ:</b> {lat:.5f}, {lon:.5f}")

    lines.append("")
    lines.append(risk_block(level))

    summary = {
        "total": count_fields(exif),
        "has_gps": coords is not None,
        "has_camera": bool(fmt_value("Model", exif.get("Model"))),
        "has_details": build_details(exif) is not None,
    }
    return "\n".join(lines), summary, coords


def build_markup(key: str, coords, has_details: bool, kind: str = "image") -> InlineKeyboardMarkup:
    rows = []
    if coords:
        lat, lon = coords
        rows.append([InlineKeyboardButton(text="📍 Открыть на карте", url=f"https://maps.google.com/?q={lat},{lon}")])
    rows.append([InlineKeyboardButton(text="🧹 Очистить всё", callback_data=f"clean:{key}")])
    if has_details and kind == "image":
        rows.append([InlineKeyboardButton(text="📖 Все данные", callback_data=f"all:{key}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def prune_pending() -> None:
    now = time.time()
    stale = [k for k, v in pending.items() if now - v["ts"] > PENDING_TTL]
    for k in stale:
        pending.pop(k, None)
    while len(pending) > MAX_PENDING:
        pending.pop(next(iter(pending)))


SHARE_TEXT = "Узнаю всё о твоих фото и стираю метаданные 🧹"
SHARE_URL = "https://t.me/share/url?url=https://t.me/KudexMeta_bot&text=" + quote(SHARE_TEXT)


def main_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="🔍 Сканировать", callback_data="menu:scan"),
                InlineKeyboardButton(text="📖 Инструкция", callback_data="menu:help"),
            ],
            [
                InlineKeyboardButton(text="📊 Статистика", callback_data="menu:stats"),
                InlineKeyboardButton(text="⚙️ Настройки", callback_data="menu:settings"),
            ],
            [
                InlineKeyboardButton(text="ℹ️ О боте", callback_data="menu:about"),
                InlineKeyboardButton(text="✨ Поделиться", url=SHARE_URL),
            ],
        ]
    )


def back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="⬅️ В меню", callback_data="menu:main")]]
    )


START_TEXT = (
    "🔍 <b>KUDEX META</b>\n"
    "<blockquote>Каждый файл рассказывает о тебе\nбольше, чем ты думаешь 👀</blockquote>\n\n"
    "📱 Камера · 📅 Дата · 📍 Геолокация\n"
    "💻 Программы · ⚙️ Настройки съёмки\n\n"
    "<i>Пришли фото или файл — покажу всё скрытое и сотру следы 🧹</i>\n\n"
    "<b>Поддержка:</b> JPG · PNG · WEBP · HEIC · PDF · MP3/FLAC · DOCX/XLSX"
)

HELP_TEXT = (
    "📖 <b>Как это работает</b>\n\n"
    "<b>1.</b> Пришли фото <u>файлом</u> (📎 → Файл)\n"
    "<b>2.</b> Получи карточку со всеми скрытыми данными\n"
    "<b>3.</b> Жми «🧹 Очистить всё» — забирай чистый файл\n\n"
    "<b>Что читаю:</b>\n"
    "🖼 Изображения — полный EXIF, GPS, камера\n"
    "📕 PDF — автор, программа, даты\n"
    "🎧 Аудио — теги, исполнитель, кодировщик\n"
    "📘 DOCX/XLSX/PPTX — автор, организация\n\n"
    "<b>Что очищаю:</b> изображения, PDF, аудио-теги"
)

ABOUT_TEXT = (
    "ℹ️ <b>KudexMeta</b>\n"
    "<blockquote>Твой щит от скрытых данных в файлах</blockquote>\n\n"
    "🔒 <b>Приватность:</b> файлы не сохраняются на сервере — только в памяти на время обработки\n"
    "⚡ <b>Стек:</b> Python · aiogram · Pillow\n"
    "🧹 <b>Очистка:</b> EXIF, GPS, PDF-мета, аудио-теги\n\n"
    "Версия 1.1 · сделано с ❤️"
)

LEVELS = [
    (100, "👻 Легенда анонимности"),
    (25, "🕵️ Профессионал приватности"),
    (5, "🎭 Скрытный"),
    (0, "🐣 Новичок"),
]


async def handle_file(message: Message, bot: Bot) -> None:
    user = message.from_user
    touch_user(user.id, user.full_name, user.username)

    if is_banned(user.id):
        await message.answer("🚫 Доступ закрыт.")
        return

    status = await message.answer(
        "🔎 <i>Сканирую файл…</i>",
        link_preview_options=LinkPreviewOptions(is_disabled=True),
    )

    if message.photo:
        file_id = message.photo[-1].file_id
        source_name = None
        compressed = True
    else:
        doc = message.document
        file_id = doc.file_id
        source_name = doc.file_name
        compressed = False

    tg_file = await bot.get_file(file_id)
    buf = io.BytesIO()
    await bot.download_file(tg_file.file_path, destination=buf)
    data = buf.getvalue()

    lower_name = (source_name or "").lower()
    mime = (message.document.mime_type if message.document else "") or ""

    prune_pending()
    key = secrets.token_urlsafe(16)
    entry = {"ts": time.time(), "data": data, "name": source_name, "kind": "unknown"}

    try:
        if message.photo or mime.startswith("image/") or lower_name.endswith(IMAGE_EXTS) or compressed:
            image = Image.open(io.BytesIO(data))
            image.load()
            entry["kind"] = "image"
            report, summary, coords = build_report(image, len(data), source_name)
            markup = build_markup(key, coords, summary["has_details"])
            note = ""
            if compressed:
                note = "\n\n<i>⚠️ Telegram уже сжал это фото и стёр часть данных.\nОтправь файлом (📎) — увижу настоящий EXIF</i>"
            bump_stat(user.id, "scanned")
            if coords:
                bump_stat(user.id, "gps_hits")
            await status.edit_text(report + note, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif mime == "application/pdf" or lower_name.endswith(".pdf"):
            report, _ = analyze_pdf(data)
            entry["kind"] = "pdf"
            markup = build_markup(key, None, False, kind="pdf")
            bump_stat(user.id, "scanned")
            await status.edit_text(report, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif lower_name.endswith(OFFICE_EXTS):
            report = analyze_office(data, source_name or "document")
            bump_stat(user.id, "scanned")
            await status.edit_text(report + "\n\n<i>🧹 Очистка документов скоро…</i>", link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif mime.startswith("audio/") or lower_name.endswith(AUDIO_EXTS):
            result = analyze_audio(data, source_name or "audio")
            if result is None:
                size_line = f"📄 <b>{esc(source_name)}</b>\n💾 {human_size(len(data))}\n🏷 MIME: {esc(mime or 'неизвестно')}"
                await status.edit_text(size_line + "\n\n🤷 Не смог разобрать теги этого аудио.")
                return
            report, has_tags = result
            entry["kind"] = "audio"
            markup = build_markup(key, None, False, kind="audio")
            bump_stat(user.id, "scanned")
            await status.edit_text(report, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        else:
            size_line = f"📄 <b>{esc(source_name)}</b>\n💾 {human_size(len(data))}\n🏷 MIME: {esc(mime or 'неизвестно')}"
            await status.edit_text(size_line + "\n\n🤷 Метаданные для этого типа я пока не читаю.\nПопробуй изображение, PDF, аудио или документ Office.")
            return

        pending[key] = entry
    except Exception:
        logging.exception("analyze failed")
        await status.edit_text("😵 <b>Не смог прочитать этот файл</b>\n\nПришли изображение, PDF, аудио или документ Office.")


@dp.message(CommandStart())
async def cmd_start(message: Message) -> None:
    user = message.from_user
    if is_banned(user.id):
        await message.answer("🚫 Доступ закрыт.")
        return
    touch_user(user.id, user.full_name, user.username)
    await message.answer(START_TEXT, reply_markup=main_menu_kb())


@dp.message(Command("help"))
async def cmd_help(message: Message) -> None:
    await message.answer(HELP_TEXT)


@dp.message(Command("stats"))
async def cmd_stats(message: Message) -> None:
    scanned, cleaned, gps_hits, _ = get_user_row(message.from_user.id)
    await message.answer(stats_text(scanned, cleaned, gps_hits))


@dp.message(Command("settings"))
async def cmd_settings(message: Message) -> None:
    _, _, _, mode = get_user_row(message.from_user.id)
    await message.answer(settings_text(mode), reply_markup=settings_kb(mode))


class Bcast(StatesGroup):
    content = State()
    buttons = State()


class Bans(StatesGroup):
    add = State()
    remove = State()


def admin_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="📢 Рассылка", callback_data="adm:bcast"),
                InlineKeyboardButton(text="📊 Статистика", callback_data="adm:stats"),
            ],
            [
                InlineKeyboardButton(text="👥 Юзеры", callback_data="adm:users"),
                InlineKeyboardButton(text="🚫 Бан-лист", callback_data="adm:bans"),
            ],
            [InlineKeyboardButton(text="⬅️ Главное меню", callback_data="menu:main")],
        ]
    )


def adm_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="⬅️ В админку", callback_data="adm:main")]]
    )


ADMIN_HOME = (
    f"🛠 <b>ПАНЕЛЬ АДМИНА</b> · v{VERSION}\n"
    "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
    "📢 Рассылка — медиа + кнопки + HTML\n"
    "📊 Статистика — вся база одним экраном\n"
    "👥 Юзеры — топ и новички\n"
    "🚫 Бан-лист — блокировка доступа"
)


def uptime_text() -> str:
    secs = int(time.time() - START_TIME)
    h, m = secs // 3600, (secs % 3600) // 60
    return f"⏱ Аптайм: {h}ч {m}м"


def bot_stats_text() -> str:
    with db_connect() as c:
        total = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        week = c.execute("SELECT COUNT(*) FROM users WHERE first_seen >= datetime('now', '-7 day')").fetchone()[0]
        active = c.execute("SELECT COUNT(*) FROM users WHERE last_seen >= datetime('now', '-7 day')").fetchone()[0]
        scanned, cleaned, gps_hits = c.execute(
            "SELECT COALESCE(SUM(scanned),0), COALESCE(SUM(cleaned),0), COALESCE(SUM(gps_hits),0) FROM users"
        ).fetchone()
        banned = c.execute("SELECT COUNT(*) FROM banned").fetchone()[0]
        admins_n = c.execute("SELECT COUNT(*) FROM admins").fetchone()[0]
    return (
        "📊 <b>СТАТИСТИКА БОТА</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"👥 Пользователей: <b>{total}</b>\n"
        f"🆕 Новых за неделю: <b>+{week}</b>\n"
        f"🔥 Активных за неделю: <b>{active}</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"🔍 Сканнирований: <b>{scanned}</b>\n"
        f"🧹 Очищено файлов: <b>{cleaned}</b>\n"
        f"📍 GPS перехвачено: <b>{gps_hits}</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"🚫 Забанено: <b>{banned}</b>\n"
        f"🔑 Админов: <b>{admins_n}</b>\n"
        f"{uptime_text()}"
    )


def users_text() -> str:
    with db_connect() as c:
        top = c.execute(
            "SELECT name, username, scanned, cleaned FROM users ORDER BY scanned DESC LIMIT 8"
        ).fetchall()
        fresh = c.execute(
            "SELECT name, username, first_seen FROM users ORDER BY first_seen DESC LIMIT 8"
        ).fetchall()

    def fmt_user(name, username):
        base = esc((name or "?")[:18])
        return f"{base} (@{username})" if username else base

    lines = ["👥 <b>ТОП ПО АКТИВНОСТИ</b>\n"]
    for i, (name, username, scanned, cleaned) in enumerate(top, 1):
        medal = ["🥇", "🥈", "🥉"][i - 1] if i <= 3 else f"{i}."
        lines.append(f"{medal} {fmt_user(name, username)} — 🔍{scanned} 🧹{cleaned}")
    lines.append("\n🆕 <b>НОВИЧКИ</b>\n")
    for name, username, _ in fresh:
        lines.append(f"• {fmt_user(name, username)}")
    return "\n".join(lines)


def bans_text() -> str:
    with db_connect() as c:
        rows = c.execute(
            "SELECT b.user_id, b.reason, u.name FROM banned b LEFT JOIN users u ON u.user_id=b.user_id"
        ).fetchall()
    if not rows:
        return "🚫 <b>Бан-лист пуст</b>\n\nВсе ведут себя прилично 😇"
    lines = ["🚫 <b>БАН-ЛИСТ</b>\n"]
    for uid, reason, name in rows:
        lines.append(f"• <code>{uid}</code> {esc((name or '')[:15])}" + (f" — {esc(reason)}" if reason else ""))
    return "\n".join(lines[:20])


def bans_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="➕ Забанить", callback_data="adm:ban_add"),
                InlineKeyboardButton(text="➖ Разбанить", callback_data="adm:ban_del"),
            ],
            [InlineKeyboardButton(text="⬅️ В админку", callback_data="adm:main")],
        ]
    )


async def send_one(bot: Bot, src_chat: int, src_msg: int, uid: int, kb: InlineKeyboardMarkup | None) -> bool:
    async def deliver():
        await bot.copy_message(chat_id=uid, from_chat_id=src_chat, message_id=src_msg, reply_markup=kb)

    try:
        await deliver()
        return True
    except TelegramRetryAfter as e:
        await asyncio.sleep(e.retry_after + 1)
        try:
            await deliver()
            return True
        except Exception:
            return False
    except TelegramForbiddenError:
        return False
    except Exception:
        return False


async def run_broadcast(bot: Bot, admin_id: int, src_chat: int, src_msg: int, buttons: list) -> None:
    with db_connect() as c:
        targets = [r[0] for r in c.execute(
            "SELECT user_id FROM users WHERE user_id NOT IN (SELECT user_id FROM banned)"
        ).fetchall()]

    total = len(targets)
    progress = await bot.send_message(admin_id, f"📤 <b>Рассылка запущена</b>\n\n🎯 Получателей: {total}")
    kb = InlineKeyboardMarkup(inline_keyboard=[[b] for b in buttons]) if buttons else None
    sent = failed = 0

    for i, uid in enumerate(targets, 1):
        if await send_one(bot, src_chat, src_msg, uid, kb):
            sent += 1
        else:
            failed += 1
        if i % 15 == 0 or i == total:
            try:
                done = round(i / total * 10) if total else 10
                await progress.edit_text(
                    f"📤 <b>Рассылка идёт…</b>\n\n"
                    f"{'▰' * done}{'▱' * (10 - done)} {i}/{total}\n"
                    f"✅ Доставлено: {sent}\n"
                    f"❌ Ошибок: {failed}"
                )
            except Exception:
                pass
        await asyncio.sleep(0.05)

    await progress.edit_text(
        "🏁 <b>Рассылка завершена!</b>\n\n"
        f"✅ Доставлено: <b>{sent}</b>\n"
        f"❌ Не доставлено: <b>{failed}</b>\n"
        f"🎯 Всего: <b>{total}</b>"
    )


@dp.message(Command("cancel"), StateFilter("*"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    await state.clear()
    await message.answer("❌ Отменено.")


@dp.message(Command("admin"), IsAdmin())
async def cmd_admin(message: Message, state: FSMContext, bot: Bot) -> None:
    await state.clear()
    try:
        await bot.set_my_commands(
            ADMIN_COMMANDS,
            scope=BotCommandScopeChat(chat_id=message.chat.id),
        )
    except Exception:
        logging.exception("admin commands setup failed")
    await message.answer(ADMIN_HOME, reply_markup=admin_menu_kb())


@dp.callback_query(F.data.startswith("adm:"), IsAdmin())
async def on_admin(callback: CallbackQuery, state: FSMContext) -> None:
    action = callback.data.split(":", 1)[1]
    await callback.answer()

    if action == "main":
        await state.clear()
        await callback.message.edit_text(ADMIN_HOME, reply_markup=admin_menu_kb())

    elif action == "stats":
        await callback.message.edit_text(bot_stats_text(), reply_markup=adm_back_kb())

    elif action == "users":
        await callback.message.edit_text(users_text(), reply_markup=adm_back_kb())

    elif action == "bans":
        await state.clear()
        await callback.message.edit_text(bans_text(), reply_markup=bans_kb())

    elif action == "bcast":
        await state.set_state(Bcast.content)
        await callback.message.edit_text(
            "📢 <b>КОНСТРУКТОР РАССЫЛКИ</b> · шаг 1/3\n"
            "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
            "Пришли контент рассылки:\n\n"
            "📝 Текст с любым HTML-форматированием\n"
            "🖼 Фото / видео / гифка / кружок\n"
            "🎧 Аудио / голосовые\n"
            "📎 Документы\n\n"
            "<i>Получателям уйдёт точная копия, без пометки «переслано»</i>\n\n"
            "/cancel — отмена",
        )

    elif action == "ban_add":
        await state.set_state(Bans.add)
        await callback.message.edit_text(
            "➕ Пришли <b>ID пользователя</b> для бана\n<code>(число, например 123456789)</code>\n\n/cancel — отмена",
            reply_markup=bans_kb(),
        )

    elif action == "ban_del":
        await state.set_state(Bans.remove)
        await callback.message.edit_text(
            "➖ Пришли <b>ID пользователя</b> для разбана\n\n/cancel — отмена",
            reply_markup=bans_kb(),
        )


@dp.message(Bans.add, F.text)
async def bans_add(message: Message, state: FSMContext) -> None:
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("🤔 Нужен числовой ID. Попробуй ещё раз:")
        return
    if ban_user(int(raw), reason=message.from_user.full_name):
        await state.clear()
        await message.answer(f"🚫 Пользователь <code>{raw}</code> забанен.", reply_markup=bans_kb())
    else:
        await message.answer("👻 Такого юзера нет в базе. Пусть сначала напишет боту.")


@dp.message(Bans.remove, F.text)
async def bans_remove(message: Message, state: FSMContext) -> None:
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("🤔 Нужен числовой ID. Попробуй ещё раз:")
        return
    if unban_user(int(raw)):
        await state.clear()
        await message.answer(f"✅ Пользователь <code>{raw}</code> разбанен.", reply_markup=bans_kb())
    else:
        await state.clear()
        await message.answer("🤷 Его и не было в бан-листе.", reply_markup=bans_kb())


def confirm_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🚀 ЗАПУСТИТЬ РАССЫЛКУ", callback_data="bc:go")],
            [InlineKeyboardButton(text="✏️ Изменить кнопки", callback_data="bc:editbtn")],
            [InlineKeyboardButton(text="❌ Отмена", callback_data="bc:cancel")],
        ]
    )


async def finish_confirm(target, state: FSMContext, buttons: list, edit: bool) -> None:
    with db_connect() as c:
        targets = c.execute(
            "SELECT COUNT(*) FROM users WHERE user_id NOT IN (SELECT user_id FROM banned)"
        ).fetchone()[0]

    text = (
        "📋 <b>ВСЁ ГОТОВО К ЗАПУСКУ</b> · шаг 3/3\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"🎯 Получателей: <b>{targets}</b>\n"
        f"🔘 Кнопок: <b>{len(buttons)}</b>\n\n"
        "<i>Превью выше ⬆️ Проверь ещё раз!</i>"
    )
    await state.update_data(
        buttons=[{"text": b.text, "url": b.url} for b in buttons],
    )
    if edit:
        await target.edit_text(text, reply_markup=confirm_kb())
    else:
        await target.answer(text, reply_markup=confirm_kb())


@dp.message(Bcast.content)
async def bcast_content(message: Message, state: FSMContext) -> None:
    if message.text and message.text.startswith("/"):
        await message.answer("⚠️ Сначала пришли контент рассылки или /cancel")
        return
    await state.update_data(src_chat=message.chat.id, src_msg=message.message_id)
    await message.copy_to(message.chat.id)

    with db_connect() as c:
        targets = c.execute(
            "SELECT COUNT(*) FROM users WHERE user_id NOT IN (SELECT user_id FROM banned)"
        ).fetchone()[0]

    await state.set_state(Bcast.buttons)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="⏭ Без кнопок, дальше", callback_data="bc:nobtn")],
        ]
    )
    await message.answer(
        "✅ Контент принят! Выше — превью.\n\n"
        "📢 <b>Шаг 2/3 — кнопки</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        "Пришли кнопки построчно:\n"
        "<code>Текст кнопки | https://ссылка.ru</code>\n\n"
        f"🎯 Получателей: <b>{targets}</b>\n\n"
        "<i>Или жми «Без кнопок»</i>\n/cancel — отмена",
        reply_markup=kb,
    )


@dp.callback_query(F.data == "bc:nobtn", Bcast.buttons, IsAdmin())
async def bc_nobtn(callback: CallbackQuery, state: FSMContext) -> None:
    await callback.answer()
    await finish_confirm(callback.message, state, [], edit=True)


@dp.message(Bcast.buttons, F.text)
async def bcast_buttons(message: Message, state: FSMContext) -> None:
    if message.text.startswith("/"):
        await message.answer("⚠️ Пришли кнопки формата <code>Текст | https://ссылка</code>, нажми «Без кнопок» или /cancel")
        return
    buttons = []
    errors = []
    for line in message.text.splitlines():
        line = line.strip()
        if not line:
            continue
        if "|" not in line:
            errors.append(line)
            continue
        title, url = line.split("|", 1)
        title, url = title.strip(), url.strip()
        if not title or not url.lower().startswith(("http://", "https://", "tg://")):
            errors.append(line)
            continue
        buttons.append(InlineKeyboardButton(text=title[:40], url=url))
    if errors:
        await message.answer(
            "⚠️ Не понял строки:\n" + "\n".join(f"<code>{esc(e)}</code>" for e in errors[:3]) +
            "\n\nФормат: <code>Текст | https://ссылка</code>"
        )
        return
    if not buttons:
        await message.answer("🤔 Пусто. Пришли хотя бы одну кнопку или жми «Без кнопок».")
        return
    buttons = buttons[:10]
    kb = InlineKeyboardMarkup(inline_keyboard=[[b] for b in buttons])
    await message.answer("🔘 Предпросмотр кнопок:", reply_markup=kb)
    await finish_confirm(message, state, buttons, edit=False)


@dp.callback_query(F.data == "bc:go", IsAdmin())
async def bc_go(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    data = await state.get_data()
    if "src_chat" not in data:
        await callback.answer("Черновик потерян — начни заново через /admin", show_alert=True)
        return
    await callback.answer("🚀 Поехали!")
    buttons = [InlineKeyboardButton(text=b["text"], url=b["url"]) for b in data.get("buttons", [])]
    src_chat, src_msg = data["src_chat"], data["src_msg"]
    await state.clear()
    asyncio.create_task(run_broadcast(bot, callback.from_user.id, src_chat, src_msg, buttons))


@dp.callback_query(F.data == "bc:editbtn")
async def bc_editbtn(callback: CallbackQuery, state: FSMContext) -> None:
    await callback.answer()
    await callback.message.edit_text(
        "✏️ Пришли новый набор кнопок:\n<code>Текст | https://ссылка</code>\n\n/cancel — отмена",
    )
    await state.set_state(Bcast.buttons)


@dp.callback_query(F.data == "bc:cancel")
async def bc_cancel(callback: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await callback.answer("Отменено")
    await callback.message.edit_text(ADMIN_HOME, reply_markup=admin_menu_kb())


@dp.message(F.photo)
async def on_photo(message: Message, bot: Bot) -> None:
    await handle_file(message, bot)


@dp.message(F.document)
async def on_document(message: Message, bot: Bot) -> None:
    await handle_file(message, bot)


def stats_text(scanned: int, cleaned: int, gps_hits: int) -> str:
    level = LEVELS[-1][1]
    for threshold, title in LEVELS:
        if cleaned >= threshold:
            level = title
            break
    bar = "▰" * min(cleaned // 10, 10) + "▱" * (10 - min(cleaned // 10, 10))
    return (
        "📊 <b>Твоя статистика</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"🔍 Просканировано: <b>{scanned}</b>\n"
        f"🧹 Очищено файлов: <b>{cleaned}</b>\n"
        f"📍 Перехвачено GPS: <b>{gps_hits}</b>\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"<b>Ранг:</b> {level}\n"
        f"{bar}\n"
        "<i>До следующего ранга осталось совсем чуть-чуть 😉</i>"
    )


def settings_text(mode: int) -> str:
    current = "📄 Документ (сохраняет качество)" if mode else "🖼 Фото (сжатие Telegram)"
    return (
        "⚙️ <b>Настройки</b>\n\n"
        f"📤 Отправка чистого файла:\n<b>{current}</b>"
    )


def settings_kb(mode: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="📄 Документ ✅" if mode else "📄 Документ", callback_data="mode:doc"),
                InlineKeyboardButton(text="🖼 Фото ✅" if not mode else "🖼 Фото", callback_data="mode:photo"),
            ],
            [InlineKeyboardButton(text="⬅️ В меню", callback_data="menu:main")],
        ]
    )


@dp.callback_query(F.data.startswith("mode:"))
async def on_mode(callback: CallbackQuery) -> None:
    mode = 1 if callback.data.endswith("doc") else 0
    set_send_mode(callback.from_user.id, mode)
    await callback.answer("Настройка сохранена ✅")
    await callback.message.edit_text(settings_text(mode), reply_markup=settings_kb(mode))


@dp.callback_query(F.data.startswith("menu:"))
async def on_menu(callback: CallbackQuery) -> None:
    action = callback.data.split(":", 1)[1]
    await callback.answer()
    if action == "main":
        await callback.message.edit_text(START_TEXT, reply_markup=main_menu_kb())
    elif action == "help":
        await callback.message.edit_text(HELP_TEXT, reply_markup=back_kb())
    elif action == "about":
        await callback.message.edit_text(ABOUT_TEXT, reply_markup=back_kb())
    elif action == "scan":
        await callback.message.answer("📎 Просто пришли мне фото или файл — я сразу начну сканирование!")
    elif action == "stats":
        scanned, cleaned, gps_hits, _ = get_user_row(callback.from_user.id)
        await callback.message.edit_text(stats_text(scanned, cleaned, gps_hits), reply_markup=back_kb())
    elif action == "settings":
        _, _, _, mode = get_user_row(callback.from_user.id)
        await callback.message.edit_text(settings_text(mode), reply_markup=settings_kb(mode))


@dp.callback_query(F.data.startswith("clean:"))
async def on_clean(callback: CallbackQuery, bot: Bot) -> None:
    key = callback.data.split(":", 1)[1]
    entry = pending.pop(key, None)
    if entry is None:
        await callback.answer("⌛ Данные устарели — отправь файл заново", show_alert=True)
        return

    await callback.answer()
    stage = await callback.message.edit_text("🧹 <b>Стираю цифровые следы…</b>\n\n⬛⬛⬛⬛⬛")

    data = entry["data"]
    kind = entry["kind"]
    name = entry["name"]

    try:
        removed_lines = []
        if kind == "image":
            exif = get_exif(Image.open(io.BytesIO(data)))
            removed_lines.append(f"▫️ {count_fields(exif)} скрытых полей")
            if fmt_value("Model", exif.get("Model")):
                removed_lines.insert(0, "▫️ данные камеры 📱")
            if isinstance(exif.get("GPSInfo"), dict) and gps_to_decimal(exif["GPSInfo"]):
                removed_lines.insert(0, "▫️ GPS-координаты 📍")
            clean_data, filename = strip_image(data)
        elif kind == "pdf":
            report, summary = analyze_pdf(data)
            removed_lines.append(f"▫️ ~{summary['total']} метаполей")
            clean_data, filename = clean_pdf(data)
        elif kind == "audio":
            removed_lines.append("▫️ все аудио-теги 🎧")
            clean_data, filename = clean_audio(data, name or "audio.mp3")
        else:
            raise ValueError("not cleanable")
    except Exception:
        logging.exception("clean failed")
        await stage.edit_text("💥 <b>Что-то пошло не так</b>\n\nПопробуй другой формат файла")
        return

    checklist = "\n".join(removed_lines[:4])
    caption = (
        "✅ <b>Файл очищен!</b>\n\n"
        f"<blockquote>Стерто:\n{esc(checklist)}</blockquote>\n"
        "Теперь он ничего о тебе не расскажет 🔒"
    )

    _, _, _, mode = get_user_row(callback.from_user.id)
    if kind == "image" and not mode:
        await callback.message.answer_photo(BufferedInputFile(clean_data, filename=filename), caption=caption)
    else:
        await callback.message.answer_document(BufferedInputFile(clean_data, filename=filename), caption=caption)

    bump_stat(callback.from_user.id, "cleaned")
    try:
        await stage.delete()
    except Exception:
        pass


@dp.callback_query(F.data.startswith("all:"))
async def on_all(callback: CallbackQuery) -> None:
    key = callback.data.split(":", 1)[1]
    entry = pending.get(key)
    if entry is None:
        await callback.answer("⌛ Данные устарели — отправь файл заново", show_alert=True)
        return
    try:
        details = build_details(get_exif(Image.open(io.BytesIO(entry["data"]))))
    except Exception:
        details = None
    if not details:
        await callback.answer("Дополнительных полей нет", show_alert=True)
        return
    await callback.answer()
    await callback.message.answer(
        "📖 <b>Полный дамп метаданных</b>\n"
        f"<pre>{details}</pre>",
        link_preview_options=LinkPreviewOptions(is_disabled=True),
    )


@dp.message()
async def on_unknown(message: Message) -> None:
    await message.answer(
        "🤔 Не понимаю.\n\nПришли фото или файл (📎) для сканирования,\nили открой меню через /start"
    )


BOT_DESCRIPTION = (
    f"🔍 KudexMeta вскрывает твои файлы, как forensic-эксперт\n\n"
    "Пришли фото или документ — и узнай:\n"
    "📍 где это снято — точные координаты и карта\n"
    "📱 каким устройством и когда\n"
    "⚙️ ISO, выдержку, диафрагму\n"
    "💻 в какой программе обработано\n\n"
    "Потом одной кнопкой сотри все следы 🧹 и получи чистый файл без метаданных.\n\n"
    "Поддержка: JPG · PNG · WEBP · HEIC · PDF · MP3/FLAC · DOCX/XLSX\n\n"
    f"👤 Владелец: @{OWNER}"
)

BOT_SHORT_DESCRIPTION = (
    "Вскрываю файлы: 📍GPS · 📱камера · 📅даты. "
    "Чистка метаданных одной кнопкой 🧹 "
    f"Владелец — @{OWNER}"
)

PUBLIC_COMMANDS = [
    BotCommand(command="start", description="🏠 Главное меню"),
    BotCommand(command="stats", description="📊 Моя статистика"),
    BotCommand(command="settings", description="⚙️ Настройки"),
    BotCommand(command="help", description="📖 Инструкция"),
    BotCommand(command="cancel", description="❌ Отменить действие"),
]

ADMIN_COMMANDS = [
    BotCommand(command="admin", description="🛠 Панель админа"),
    BotCommand(command="stats", description="📊 Статистика бота"),
    BotCommand(command="cancel", description="❌ Отменить действие"),
]


async def setup_profile(bot: Bot) -> None:
    try:
        await bot.set_my_description(BOT_DESCRIPTION)
        await bot.set_my_short_description(BOT_SHORT_DESCRIPTION)
        await bot.set_my_commands(PUBLIC_COMMANDS)
        logging.info("bot profile configured")
    except Exception:
        logging.exception("profile setup failed")


async def main() -> None:
    os.makedirs(DB_DIR, exist_ok=True)
    load_admins()
    with db_connect():
        pass
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await bot.delete_webhook(drop_pending_updates=True)
    await setup_profile(bot)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
