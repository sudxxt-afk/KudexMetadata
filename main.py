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
VERSION = "1.2"

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
        return f"{n / 1024 / 1024:.1f} РњР‘"
    return f"{n / 1024:.0f} РљР‘"


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
    ("DateTimeOriginal", "рџ“…", "Р”Р°С‚Р° СЃСЉС‘РјРєРё"),
    ("Model", "рџ“±", "РЈСЃС‚СЂРѕР№СЃС‚РІРѕ"),
    ("Make", "рџЏ­", "РџСЂРѕРёР·РІРѕРґРёС‚РµР»СЊ"),
    ("LensModel", "рџ”­", "РћР±СЉРµРєС‚РёРІ"),
    ("Software", "рџ’»", "РћР±СЂР°Р±РѕС‚РєР°"),
    ("ISOSpeedRatings", "рџ’Ў", "ISO"),
    ("FNumber", "рџ”", "Р”РёР°С„СЂР°РіРјР°"),
    ("ExposureTime", "вЏ±", "Р’С‹РґРµСЂР¶РєР°"),
    ("FocalLength", "рџЋЇ", "Р¤РѕРєСѓСЃРЅРѕРµ"),
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
            return f"1/{round(1 / v)} СЃ" if v < 1 else f"{v:g} СЃ"
        except Exception:
            return None
    if tag == "FocalLength":
        try:
            v = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
            return f"{v:g} РјРј"
        except Exception:
            return None
    if tag in ("DateTimeOriginal", "DateTime", "DateTimeDigitized"):
        try:
            return datetime.strptime(str(value), "%Y:%m:%d %H:%M:%S").strftime("%d.%m.%Y В· %H:%M")
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
    0: ("Р§РРЎРўРћ вњЁ", "РјРµС‚Р°РґР°РЅРЅС‹С… РЅРµС‚"),
    2: ("РќРР—РљРР™ рџџў", "РµСЃС‚СЊ Р±Р°Р·РѕРІС‹Рµ С‚РµРіРё"),
    3: ("РЎР Р•Р”РќРР™ рџџЎ", "РјРЅРѕРіРѕ СЃРєСЂС‹С‚С‹С… РґР°РЅРЅС‹С…"),
    4: ("Р’Р«РЎРћРљРР™ рџџ ", "РѕР±РЅР°СЂСѓР¶РµРЅС‹ РєРѕРѕСЂРґРёРЅР°С‚С‹!"),
    5: ("РљР РРўРР§Р•РЎРљРР™ рџ”ґ", "С‚РІРѕС‘ РјРµСЃС‚РѕРїРѕР»РѕР¶РµРЅРёРµ РІРЅСѓС‚СЂРё!"),
}


def risk_block(level: int) -> str:
    label, hint = RISK_LABELS[level]
    filled = max(level, 1)
    icon = "рџ”ґ" if level >= 4 else "рџџЎ" if level >= 2 else "рџџў"
    bar = icon * filled + "вљЄ" * (5 - filled)
    if level == 0:
        bar = "рџџўрџџўрџџўрџџўрџџў"
    return (
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"<b>РЈР РћР’Р•РќР¬ Р РРЎРљРђ:</b> {label}\n"
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
        body += f"\nвЂ¦ Рё РµС‰С‘ {rest} РїРѕР»РµР№"
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
        ("рџ“ќ", "Р—Р°РіРѕР»РѕРІРѕРє", meta.get("/Title")),
        ("вњЌпёЏ", "РђРІС‚РѕСЂ", meta.get("/Author")),
        ("рџЏ·", "РўРµРјР°", meta.get("/Subject")),
        ("рџ”‘", "РљР»СЋС‡РµРІС‹Рµ СЃР»РѕРІР°", meta.get("/Keywords")),
        ("рџЏ­", "РЎРѕР·РґР°С‚РµР»СЊ", meta.get("/Creator")),
        ("рџ’»", "РџСЂРѕРґСЋСЃРµСЂ", meta.get("/Producer")),
        ("рџ“…", "РЎРѕР·РґР°РЅ", meta.get("/CreationDate")),
        ("рџ”„", "РР·РјРµРЅС‘РЅ", meta.get("/ModDate")),
    ]
    rows = [f"{icon} <b>{title}:</b> {esc(v)}" for icon, title, v in fields if v]

    text = [
        "рџ“• <b>PDF-РґРѕРєСѓРјРµРЅС‚</b>",
        f"рџ“„ РЎС‚СЂР°РЅРёС†: <b>{pages}</b>",
    ]
    if rows:
        text.append("в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€")
        text.extend(rows[:7])
    text.append("")
    text.append(risk_block(min(4, 2 + (1 if rows else 0))))
    summary = {"total": sum(1 for _, _, v in fields if v)}
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

OFFICE_ICONS = {"docx": "рџ“", "xlsx": "рџ“—", "pptx": "рџ“™"}


def analyze_office(data: bytes, name: str):
    ext = (name.rsplit(".", 1)[-1] if "." in name else "").lower()
    icon = OFFICE_ICONS.get(ext, "рџ“¦")
    rows = []
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        core_name = next((n for n in z.namelist() if n.endswith("docProps/core.xml")), None)
        app_name = next((n for n in z.namelist() if n.endswith("docProps/app.xml")), None)
        if core_name:
            root = ElementTree.fromstring(z.read(core_name))
            mapping = [
                ("dc:title", "рџ“ќ", "Р—Р°РіРѕР»РѕРІРѕРє"),
                ("dc:subject", "рџЏ·", "РўРµРјР°"),
                ("dc:creator", "вњЌпёЏ", "РђРІС‚РѕСЂ"),
                ("cp:lastModifiedBy", "рџ‘¤", "РџРѕСЃР»РµРґРЅРёР№ СЂРµРґР°РєС‚РѕСЂ"),
                ("dcterms:created", "рџ“…", "РЎРѕР·РґР°РЅ"),
                ("dcterms:modified", "рџ”„", "РР·РјРµРЅС‘РЅ"),
                ("dc:description", "рџ’¬", "РћРїРёСЃР°РЅРёРµ"),
            ]
            for path, ic, title in mapping:
                el = root.find(path, OFFICE_NS)
                if el is not None and el.text and el.text.strip():
                    rows.append(f"{ic} <b>{title}:</b> {esc(el.text.strip())}")
        if app_name:
            root = ElementTree.fromstring(z.read(app_name))
            for tag, title in (("Application", "РџСЂРѕРіСЂР°РјРјР°"), ("Company", "РћСЂРіР°РЅРёР·Р°С†РёСЏ")):
                el = root.find(tag)
                if el is not None and el.text and el.text.strip():
                    rows.append(f"рџ’» <b>{title}:</b> {esc(el.text.strip())}")

    text = [
        f"{icon} <b>Р”РѕРєСѓРјРµРЅС‚ Office</b>",
        f"рџ“„ {esc(name)}",
    ]
    if rows:
        text.append("в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€")
        text.extend(rows[:8])
    text.append("")
    if rows:
        text.append("вљ пёЏ Р’РЅСѓС‚СЂРё РґРѕРєСѓРјРµРЅС‚Р° РЅР°Р№РґРµРЅС‹ <b>Р»РёС‡РЅС‹Рµ РґР°РЅРЅС‹Рµ Р°РІС‚РѕСЂР°</b>")
    else:
        text.append("вњ… РЎРєСЂС‹С‚С‹С… РґР°РЅРЅС‹С… РЅРµ РЅР°Р№РґРµРЅРѕ")
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
    rows.append(f"вЏ± <b>Р”Р»РёС‚РµР»СЊРЅРѕСЃС‚СЊ:</b> {mins}:{secs:02d}")
    bitrate = getattr(info, "bitrate", 0)
    if bitrate:
        rows.append(f"рџЋљ <b>Р‘РёС‚СЂРµР№С‚:</b> {bitrate // 1000} РєР±РёС‚/СЃ")

    tags_map = [
        ("title", "рџЋµ", "РќР°Р·РІР°РЅРёРµ"), ("TIT2", "рџЋµ", "РќР°Р·РІР°РЅРёРµ"), ("\xa9nam", "рџЋµ", "РќР°Р·РІР°РЅРёРµ"),
        ("artist", "рџЋ¤", "РСЃРїРѕР»РЅРёС‚РµР»СЊ"), ("TPE1", "рџЋ¤", "РСЃРїРѕР»РЅРёС‚РµР»СЊ"), ("\xa9ART", "рџЋ¤", "РСЃРїРѕР»РЅРёС‚РµР»СЊ"),
        ("album", "рџ’ї", "РђР»СЊР±РѕРј"), ("TALB", "рџ’ї", "РђР»СЊР±РѕРј"), ("\xa9alb", "рџ’ї", "РђР»СЊР±РѕРј"),
        ("date", "рџ“…", "Р”Р°С‚Р°"), ("TDRC", "рџ“…", "Р”Р°С‚Р°"), ("\xa9day", "рџ“…", "Р”Р°С‚Р°"),
        ("genre", "рџЋ­", "Р–Р°РЅСЂ"), ("TCON", "рџЋ­", "Р–Р°РЅСЂ"), ("\xa9gen", "рџЋ­", "Р–Р°РЅСЂ"),
        ("organization", "рџЏў", "Р›РµР№Р±Р»"), ("\xa9too", "рџ’»", "РљРѕРґРёСЂРѕРІС‰РёРє"), ("TENC", "рџ’»", "РљРѕРґРёСЂРѕРІС‰РёРє"),
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
        "рџЋ§ <b>РђСѓРґРёРѕС„Р°Р№Р»</b>",
        f"рџ“„ {esc(name)}",
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€",
        *rows[:8],
        "",
    ]
    if seen:
        text.append("вљ пёЏ РќР°Р№РґРµРЅС‹ С‚РµРіРё СЃ Р»РёС‡РЅС‹РјРё РґР°РЅРЅС‹РјРё")
    else:
        text.append("вњ… РўРµРіРё РЅРµ РѕР±РЅР°СЂСѓР¶РµРЅС‹")
    return "\n".join(text), bool(audio.tags)


def clean_audio(data: bytes, name: str):
    ext = name.rsplit(".", 1)[-1].lower() if "." in name else "mp3"
    out = io.BytesIO(data)
    try:
        audio = MutagenFile(out, easy=True)
        if audio is not None:
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
        f"рџ“„ <b>{esc(display_name)}</b>",
        f"рџ–ј {image.width} Г— {image.height} В· {esc(image.format or '?')} В· {human_size(size)}",
    ]

    info_rows = []
    for tag, icon, title in EXIF_FIELDS:
        value = fmt_value(tag, exif.get(tag))
        if value:
            info_rows.append(f"{icon} <b>{title}:</b> {esc(value)}")

    if info_rows:
        lines.append("в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€")
        lines.extend(info_rows[:6])

    if coords:
        lat, lon = coords
        lines.append("в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€")
        lines.append(f"рџ“Ќ <b>Р“Р•РћР›РћРљРђР¦РРЇ:</b> {lat:.5f}, {lon:.5f}")

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
        rows.append([InlineKeyboardButton(text="рџ“Ќ РћС‚РєСЂС‹С‚СЊ РЅР° РєР°СЂС‚Рµ", url=f"https://maps.google.com/?q={lat},{lon}")])
    rows.append([InlineKeyboardButton(text="рџ§№ РћС‡РёСЃС‚РёС‚СЊ РІСЃС‘", callback_data=f"clean:{key}")])
    if has_details and kind == "image":
        rows.append([InlineKeyboardButton(text="рџ“– Р’СЃРµ РґР°РЅРЅС‹Рµ", callback_data=f"all:{key}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def prune_pending() -> None:
    now = time.time()
    stale = [k for k, v in pending.items() if now - v["ts"] > PENDING_TTL]
    for k in stale:
        pending.pop(k, None)
    while len(pending) > MAX_PENDING:
        pending.pop(next(iter(pending)))


def main_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="рџ”Ќ РЎРєР°РЅРёСЂРѕРІР°С‚СЊ", callback_data="menu:scan"),
                InlineKeyboardButton(text="рџ“– РРЅСЃС‚СЂСѓРєС†РёСЏ", callback_data="menu:help"),
            ],
            [
                InlineKeyboardButton(text="рџ“Љ РЎС‚Р°С‚РёСЃС‚РёРєР°", callback_data="menu:stats"),
                InlineKeyboardButton(text="вљ™пёЏ РќР°СЃС‚СЂРѕР№РєРё", callback_data="menu:settings"),
            ],
            [
                InlineKeyboardButton(text="в„№пёЏ Рћ Р±РѕС‚Рµ", callback_data="menu:about"),
                InlineKeyboardButton(text="вњЁ РџРѕРґРµР»РёС‚СЊСЃСЏ", url="https://t.me/share/url?url=https://t.me/KudexMeta_bot&text=РЈР·РЅР°СЋ РІСЃС‘ Рѕ С‚РІРѕРёС… С„РѕС‚Рѕ Рё СЃС‚РёСЂР°СЋ РјРµС‚Р°РґР°РЅРЅС‹Рµ рџ§№"),
            ],
        ]
    )


def back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="в¬…пёЏ Р’ РјРµРЅСЋ", callback_data="menu:main")]]
    )


START_TEXT = (
    "рџ”Ќ <b>KUDEX META</b>\n"
    "<blockquote>РљР°Р¶РґС‹Р№ С„Р°Р№Р» СЂР°СЃСЃРєР°Р·С‹РІР°РµС‚ Рѕ С‚РµР±Рµ\nР±РѕР»СЊС€Рµ, С‡РµРј С‚С‹ РґСѓРјР°РµС€СЊ рџ‘Ђ</blockquote>\n\n"
    "рџ“± РљР°РјРµСЂР° В· рџ“… Р”Р°С‚Р° В· рџ“Ќ Р“РµРѕР»РѕРєР°С†РёСЏ\n"
    "рџ’» РџСЂРѕРіСЂР°РјРјС‹ В· вљ™пёЏ РќР°СЃС‚СЂРѕР№РєРё СЃСЉС‘РјРєРё\n\n"
    "<i>РџСЂРёС€Р»Рё С„РѕС‚Рѕ РёР»Рё С„Р°Р№Р» вЂ” РїРѕРєР°Р¶Сѓ РІСЃС‘ СЃРєСЂС‹С‚РѕРµ Рё СЃРѕС‚СЂСѓ СЃР»РµРґС‹ рџ§№</i>\n\n"
    "<b>РџРѕРґРґРµСЂР¶РєР°:</b> JPG В· PNG В· WEBP В· HEIC В· PDF В· MP3/FLAC В· DOCX/XLSX"
)

HELP_TEXT = (
    "рџ“– <b>РљР°Рє СЌС‚Рѕ СЂР°Р±РѕС‚Р°РµС‚</b>\n\n"
    "<b>1.</b> РџСЂРёС€Р»Рё С„РѕС‚Рѕ <u>С„Р°Р№Р»РѕРј</u> (рџ“Ћ в†’ Р¤Р°Р№Р»)\n"
    "<b>2.</b> РџРѕР»СѓС‡Рё РєР°СЂС‚РѕС‡РєСѓ СЃРѕ РІСЃРµРјРё СЃРєСЂС‹С‚С‹РјРё РґР°РЅРЅС‹РјРё\n"
    "<b>3.</b> Р–РјРё В«рџ§№ РћС‡РёСЃС‚РёС‚СЊ РІСЃС‘В» вЂ” Р·Р°Р±РёСЂР°Р№ С‡РёСЃС‚С‹Р№ С„Р°Р№Р»\n\n"
    "<b>Р§С‚Рѕ С‡РёС‚Р°СЋ:</b>\n"
    "рџ–ј РР·РѕР±СЂР°Р¶РµРЅРёСЏ вЂ” РїРѕР»РЅС‹Р№ EXIF, GPS, РєР°РјРµСЂР°\n"
    "рџ“• PDF вЂ” Р°РІС‚РѕСЂ, РїСЂРѕРіСЂР°РјРјР°, РґР°С‚С‹\n"
    "рџЋ§ РђСѓРґРёРѕ вЂ” С‚РµРіРё, РёСЃРїРѕР»РЅРёС‚РµР»СЊ, РєРѕРґРёСЂРѕРІС‰РёРє\n"
    "рџ“ DOCX/XLSX/PPTX вЂ” Р°РІС‚РѕСЂ, РѕСЂРіР°РЅРёР·Р°С†РёСЏ\n\n"
    "<b>Р§С‚Рѕ РѕС‡РёС‰Р°СЋ:</b> РёР·РѕР±СЂР°Р¶РµРЅРёСЏ, PDF, Р°СѓРґРёРѕ-С‚РµРіРё"
)

ABOUT_TEXT = (
    "в„№пёЏ <b>KudexMeta</b>\n"
    "<blockquote>РўРІРѕР№ С‰РёС‚ РѕС‚ СЃРєСЂС‹С‚С‹С… РґР°РЅРЅС‹С… РІ С„Р°Р№Р»Р°С…</blockquote>\n\n"
    "рџ”’ <b>РџСЂРёРІР°С‚РЅРѕСЃС‚СЊ:</b> С„Р°Р№Р»С‹ РЅРµ СЃРѕС…СЂР°РЅСЏСЋС‚СЃСЏ РЅР° СЃРµСЂРІРµСЂРµ вЂ” С‚РѕР»СЊРєРѕ РІ РїР°РјСЏС‚Рё РЅР° РІСЂРµРјСЏ РѕР±СЂР°Р±РѕС‚РєРё\n"
    "вљЎ <b>РЎС‚РµРє:</b> Python В· aiogram В· Pillow\n"
    "рџ§№ <b>РћС‡РёСЃС‚РєР°:</b> EXIF, GPS, PDF-РјРµС‚Р°, Р°СѓРґРёРѕ-С‚РµРіРё\n\n"
    f"Р’РµСЂСЃРёСЏ {VERSION} В· СЃРґРµР»Р°РЅРѕ СЃ вќ¤пёЏ"
)

LEVELS = [
    (100, "рџ‘» Р›РµРіРµРЅРґР° Р°РЅРѕРЅРёРјРЅРѕСЃС‚Рё"),
    (25, "рџ•µпёЏ РџСЂРѕС„РµСЃСЃРёРѕРЅР°Р» РїСЂРёРІР°С‚РЅРѕСЃС‚Рё"),
    (5, "рџЋ­ РЎРєСЂС‹С‚РЅС‹Р№"),
    (0, "рџђЈ РќРѕРІРёС‡РѕРє"),
]


def stats_text(scanned: int, cleaned: int, gps_hits: int) -> str:
    level = LEVELS[-1][1]
    for threshold, title in LEVELS:
        if cleaned >= threshold:
            level = title
            break
    bar = "в–°" * min(cleaned // 10, 10) + "в–±" * (10 - min(cleaned // 10, 10))
    return (
        "рџ“Љ <b>РўРІРѕСЏ СЃС‚Р°С‚РёСЃС‚РёРєР°</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"рџ”Ќ РџСЂРѕСЃРєР°РЅРёСЂРѕРІР°РЅРѕ: <b>{scanned}</b>\n"
        f"рџ§№ РћС‡РёС‰РµРЅРѕ С„Р°Р№Р»РѕРІ: <b>{cleaned}</b>\n"
        f"рџ“Ќ РџРµСЂРµС…РІР°С‡РµРЅРѕ GPS: <b>{gps_hits}</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"<b>Р Р°РЅРі:</b> {level}\n"
        f"{bar}\n"
        "<i>Р”Рѕ СЃР»РµРґСѓСЋС‰РµРіРѕ СЂР°РЅРіР° РѕСЃС‚Р°Р»РѕСЃСЊ СЃРѕРІСЃРµРј С‡СѓС‚СЊ-С‡СѓС‚СЊ рџ‰</i>"
    )


def settings_text(mode: int) -> str:
    current = "рџ“„ Р”РѕРєСѓРјРµРЅС‚ (СЃРѕС…СЂР°РЅСЏРµС‚ РєР°С‡РµСЃС‚РІРѕ)" if mode else "рџ–ј Р¤РѕС‚Рѕ (СЃР¶Р°С‚РёРµ Telegram)"
    return (
        "вљ™пёЏ <b>РќР°СЃС‚СЂРѕР№РєРё</b>\n\n"
        f"рџ“¤ РћС‚РїСЂР°РІРєР° С‡РёСЃС‚РѕРіРѕ С„Р°Р№Р»Р°:\n<b>{current}</b>"
    )


def settings_kb(mode: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="рџ“„ Р”РѕРєСѓРјРµРЅС‚ вњ…" if mode else "рџ“„ Р”РѕРєСѓРјРµРЅС‚", callback_data="mode:doc"),
                InlineKeyboardButton(text="рџ–ј Р¤РѕС‚Рѕ вњ…" if not mode else "рџ–ј Р¤РѕС‚Рѕ", callback_data="mode:photo"),
            ],
            [InlineKeyboardButton(text="в¬…пёЏ Р’ РјРµРЅСЋ", callback_data="menu:main")],
        ]
    )


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
                InlineKeyboardButton(text="рџ“ў Р Р°СЃСЃС‹Р»РєР°", callback_data="adm:bcast"),
                InlineKeyboardButton(text="рџ“Љ РЎС‚Р°С‚РёСЃС‚РёРєР°", callback_data="adm:stats"),
            ],
            [
                InlineKeyboardButton(text="рџ‘Ґ Р®Р·РµСЂС‹", callback_data="adm:users"),
                InlineKeyboardButton(text="рџљ« Р‘Р°РЅ-Р»РёСЃС‚", callback_data="adm:bans"),
            ],
            [InlineKeyboardButton(text="в¬…пёЏ Р“Р»Р°РІРЅРѕРµ РјРµРЅСЋ", callback_data="menu:main")],
        ]
    )


def adm_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="в¬…пёЏ Р’ Р°РґРјРёРЅРєСѓ", callback_data="adm:main")]]
    )


ADMIN_HOME = (
    f"рџ›  <b>РџРђРќР•Р›Р¬ РђР”РњРРќРђ</b> В· v{VERSION}\n"
    "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
    "рџ“ў Р Р°СЃСЃС‹Р»РєР° вЂ” РјРµРґРёР° + РєРЅРѕРїРєРё + HTML\n"
    "рџ“Љ РЎС‚Р°С‚РёСЃС‚РёРєР° вЂ” РІСЃСЏ Р±Р°Р·Р° РѕРґРЅРёРј СЌРєСЂР°РЅРѕРј\n"
    "рџ‘Ґ Р®Р·РµСЂС‹ вЂ” С‚РѕРї Рё РЅРѕРІРёС‡РєРё\n"
    "рџљ« Р‘Р°РЅ-Р»РёСЃС‚ вЂ” Р±Р»РѕРєРёСЂРѕРІРєР° РґРѕСЃС‚СѓРїР°"
)


def uptime_text() -> str:
    secs = int(time.time() - START_TIME)
    h, m = secs // 3600, (secs % 3600) // 60
    return f"вЏ± РђРїС‚Р°Р№Рј: {h}С‡ {m}Рј"


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
        "рџ“Љ <b>РЎРўРђРўРРЎРўРРљРђ Р‘РћРўРђ</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"рџ‘Ґ РџРѕР»СЊР·РѕРІР°С‚РµР»РµР№: <b>{total}</b>\n"
        f"рџ†• РќРѕРІС‹С… Р·Р° РЅРµРґРµР»СЋ: <b>+{week}</b>\n"
        f"рџ”Ґ РђРєС‚РёРІРЅС‹С… Р·Р° РЅРµРґРµР»СЋ: <b>{active}</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"рџ”Ќ РЎРєР°РЅРЅРёСЂРѕРІР°РЅРёР№: <b>{scanned}</b>\n"
        f"рџ§№ РћС‡РёС‰РµРЅРѕ С„Р°Р№Р»РѕРІ: <b>{cleaned}</b>\n"
        f"рџ“Ќ GPS РїРµСЂРµС…РІР°С‡РµРЅРѕ: <b>{gps_hits}</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"рџљ« Р—Р°Р±Р°РЅРµРЅРѕ: <b>{banned}</b>\n"
        f"рџ”‘ РђРґРјРёРЅРѕРІ: <b>{admins_n}</b>\n"
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

    lines = ["рџ‘Ґ <b>РўРћРџ РџРћ РђРљРўРР’РќРћРЎРўР</b>\n"]
    for i, (name, username, scanned, cleaned) in enumerate(top, 1):
        medal = ["рџҐ‡", "рџҐ€", "рџҐ‰"][i - 1] if i <= 3 else f"{i}."
        lines.append(f'{medal} {fmt_user(name, username)} вЂ” рџ”Ќ{scanned} рџ§№{cleaned}')
    lines.append("\nрџ†• <b>РќРћР’РР§РљР</b>\n")
    for name, username, _ in fresh:
        lines.append(f"вЂў {fmt_user(name, username)}")
    return "\n".join(lines)


def bans_text() -> str:
    with db_connect() as c:
        rows = c.execute(
            "SELECT b.user_id, b.reason, u.name FROM banned b LEFT JOIN users u ON u.user_id=b.user_id"
        ).fetchall()
    if not rows:
        return "рџљ« <b>Р‘Р°РЅ-Р»РёСЃС‚ РїСѓСЃС‚</b>\n\nР’СЃРµ РІРµРґСѓС‚ СЃРµР±СЏ РїСЂРёР»РёС‡РЅРѕ рџ‡"
    lines = ["рџљ« <b>Р‘РђРќ-Р›РРЎРў</b>\n"]
    for uid, reason, name in rows:
        lines.append(f"вЂў <code>{uid}</code> {esc((name or '')[:15])}" + (f" вЂ” {esc(reason)}" if reason else ""))
    return "\n".join(lines[:20])


def bans_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="вћ• Р—Р°Р±Р°РЅРёС‚СЊ", callback_data="adm:ban_add"),
                InlineKeyboardButton(text="вћ– Р Р°Р·Р±Р°РЅРёС‚СЊ", callback_data="adm:ban_del"),
            ],
            [InlineKeyboardButton(text="в¬…пёЏ Р’ Р°РґРјРёРЅРєСѓ", callback_data="adm:main")],
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
    progress = await bot.send_message(admin_id, f"рџ“¤ <b>Р Р°СЃСЃС‹Р»РєР° Р·Р°РїСѓС‰РµРЅР°</b>\n\nрџЋЇ РџРѕР»СѓС‡Р°С‚РµР»РµР№: {total}")
    kb = InlineKeyboardMarkup(inline_keyboard=[[b] for b in buttons]) if buttons else None
    sent = failed = 0

    for i, uid in enumerate(targets, 1):
        if await send_one(bot, src_chat, src_msg, uid, kb):
            sent += 1
        else:
            failed += 1
        if i % 15 == 0 or i == total:
            try:
                await progress.edit_text(
                    f"рџ“¤ <b>Р Р°СЃСЃС‹Р»РєР° РёРґС‘С‚вЂ¦</b>\n\n"
                    f"{'в–°' * round(i / total * 10)}{'в–±' * (10 - round(i / total * 10))} {i}/{total}\n"
                    f"вњ… Р”РѕСЃС‚Р°РІР»РµРЅРѕ: {sent}\n"
                    f"вќЊ РћС€РёР±РѕРє: {failed}"
                )
            except Exception:
                pass
        await asyncio.sleep(0.05)

    await progress.edit_text(
        "рџЏЃ <b>Р Р°СЃСЃС‹Р»РєР° Р·Р°РІРµСЂС€РµРЅР°!</b>\n\n"
        f"вњ… Р”РѕСЃС‚Р°РІР»РµРЅРѕ: <b>{sent}</b>\n"
        f"вќЊ РќРµ РґРѕСЃС‚Р°РІР»РµРЅРѕ: <b>{failed}</b>\n"
        f"рџЋЇ Р’СЃРµРіРѕ: <b>{total}</b>"
    )


@dp.message(CommandStart())
async def cmd_start(message: Message) -> None:
    user = message.from_user
    if is_banned(user.id):
        await message.answer("рџљ« Р”РѕСЃС‚СѓРї Р·Р°РєСЂС‹С‚.")
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


@dp.message(Command("cancel"), StateFilter("*"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    await state.clear()
    await message.answer("вќЊ РћС‚РјРµРЅРµРЅРѕ.")


@dp.message(Command("admin"), IsAdmin())
async def cmd_admin(message: Message, state: FSMContext) -> None:
    await state.clear()
    await message.answer(ADMIN_HOME, reply_markup=admin_menu_kb())


@dp.callback_query(F.data.startswith("adm:"), IsAdmin())
async def on_admin(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
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
            "рџ“ў <b>РљРћРќРЎРўР РЈРљРўРћР  Р РђРЎРЎР«Р›РљР</b> В· С€Р°Рі 1/3\n"
            "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
            "РџСЂРёС€Р»Рё РєРѕРЅС‚РµРЅС‚ СЂР°СЃСЃС‹Р»РєРё:\n\n"
            "рџ“ќ РўРµРєСЃС‚ СЃ Р»СЋР±С‹Рј HTML-С„РѕСЂРјР°С‚РёСЂРѕРІР°РЅРёРµРј\n"
            "рџ–ј Р¤РѕС‚Рѕ / РІРёРґРµРѕ / РіРёС„РєР° / РєСЂСѓР¶РѕРє\n"
            "рџЋ§ РђСѓРґРёРѕ / РіРѕР»РѕСЃРѕРІС‹Рµ\n"
            "рџ“Ћ Р”РѕРєСѓРјРµРЅС‚С‹\n\n"
            "<i>РџРѕР»СѓС‡Р°С‚РµР»СЏРј СѓР№РґС‘С‚ С‚РѕС‡РЅР°СЏ РєРѕРїРёСЏ, Р±РµР· РїРѕРјРµС‚РєРё В«РїРµСЂРµСЃР»Р°РЅРѕВ»</i>\n\n"
            "/cancel вЂ” РѕС‚РјРµРЅР°",
        )

    elif action == "ban_add":
        await state.set_state(Bans.add)
        await callback.message.edit_text(
            "вћ• РџСЂРёС€Р»Рё <b>ID РїРѕР»СЊР·РѕРІР°С‚РµР»СЏ</b> РґР»СЏ Р±Р°РЅР°\n<code>(С‡РёСЃР»Рѕ, РЅР°РїСЂРёРјРµСЂ 123456789)</code>\n\n/cancel вЂ” РѕС‚РјРµРЅР°",
            reply_markup=bans_kb(),
        )

    elif action == "ban_del":
        await state.set_state(Bans.remove)
        await callback.message.edit_text(
            "вћ– РџСЂРёС€Р»Рё <b>ID РїРѕР»СЊР·РѕРІР°С‚РµР»СЏ</b> РґР»СЏ СЂР°Р·Р±Р°РЅР°\n\n/cancel вЂ” РѕС‚РјРµРЅР°",
            reply_markup=bans_kb(),
        )


@dp.message(Bans.add, F.text)
async def bans_add(message: Message, state: FSMContext) -> None:
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("рџ¤” РќСѓР¶РµРЅ С‡РёСЃР»РѕРІРѕР№ ID. РџРѕРїСЂРѕР±СѓР№ РµС‰С‘ СЂР°Р·:")
        return
    if ban_user(int(raw), reason=message.from_user.full_name):
        await state.clear()
        await message.answer(f"рџљ« РџРѕР»СЊР·РѕРІР°С‚РµР»СЊ <code>{raw}</code> Р·Р°Р±Р°РЅРµРЅ.", reply_markup=bans_kb())
    else:
        await message.answer("рџ‘» РўР°РєРѕРіРѕ СЋР·РµСЂР° РЅРµС‚ РІ Р±Р°Р·Рµ. РџСѓСЃС‚СЊ СЃРЅР°С‡Р°Р»Р° РЅР°РїРёС€РµС‚ Р±РѕС‚Сѓ.")


@dp.message(Bans.remove, F.text)
async def bans_remove(message: Message, state: FSMContext) -> None:
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("рџ¤” РќСѓР¶РµРЅ С‡РёСЃР»РѕРІРѕР№ ID. РџРѕРїСЂРѕР±СѓР№ РµС‰С‘ СЂР°Р·:")
        return
    if unban_user(int(raw)):
        await state.clear()
        await message.answer(f"вњ… РџРѕР»СЊР·РѕРІР°С‚РµР»СЊ <code>{raw}</code> СЂР°Р·Р±Р°РЅРµРЅ.", reply_markup=bans_kb())
    else:
        await state.clear()
        await message.answer("рџ¤· Р•РіРѕ Рё РЅРµ Р±С‹Р»Рѕ РІ Р±Р°РЅ-Р»РёСЃС‚Рµ.", reply_markup=bans_kb())


@dp.message(Bcast.content)
async def bcast_content(message: Message, state: FSMContext) -> None:
    if message.text and message.text.startswith("/"):
        await message.answer("вљ пёЏ РЎРЅР°С‡Р°Р»Р° РїСЂРёС€Р»Рё РєРѕРЅС‚РµРЅС‚ СЂР°СЃСЃС‹Р»РєРё РёР»Рё /cancel")
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
            [InlineKeyboardButton(text="вЏ­ Р‘РµР· РєРЅРѕРїРѕРє, РґР°Р»СЊС€Рµ", callback_data="bc:nobtn")],
        ]
    )
    await message.answer(
        "вњ… РљРѕРЅС‚РµРЅС‚ РїСЂРёРЅСЏС‚! Р’С‹С€Рµ вЂ” РїСЂРµРІСЊСЋ.\n\n"
        "рџ“ў <b>РЁР°Рі 2/3 вЂ” РєРЅРѕРїРєРё</b>\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        "РџСЂРёС€Р»Рё РєРЅРѕРїРєРё РїРѕСЃС‚СЂРѕС‡РЅРѕ:\n"
        "<code>РўРµРєСЃС‚ РєРЅРѕРїРєРё | https://СЃСЃС‹Р»РєР°.ru</code>\n\n"
        f"рџЋЇ РџРѕР»СѓС‡Р°С‚РµР»РµР№: <b>{targets}</b>\n\n"
        "<i>РР»Рё Р¶РјРё В«Р‘РµР· РєРЅРѕРїРѕРєВ»</i>\n/cancel вЂ” РѕС‚РјРµРЅР°",
        reply_markup=kb,
    )


def confirm_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="рџљЂ Р—РђРџРЈРЎРўРРўР¬ Р РђРЎРЎР«Р›РљРЈ", callback_data="bc:go")],
            [InlineKeyboardButton(text="вњЏпёЏ РР·РјРµРЅРёС‚СЊ РєРЅРѕРїРєРё", callback_data="bc:editbtn")],
            [InlineKeyboardButton(text="вќЊ РћС‚РјРµРЅР°", callback_data="bc:cancel")],
        ]
    )


async def finish_confirm(target, state: FSMContext, buttons: list, edit: bool) -> None:
    data = await state.get_data()
    with db_connect() as c:
        targets = c.execute(
            "SELECT COUNT(*) FROM users WHERE user_id NOT IN (SELECT user_id FROM banned)"
        ).fetchone()[0]

    text = (
        "рџ“‹ <b>Р’РЎРЃ Р“РћРўРћР’Рћ Рљ Р—РђРџРЈРЎРљРЈ</b> В· С€Р°Рі 3/3\n"
        "в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€в”€\n"
        f"рџЋЇ РџРѕР»СѓС‡Р°С‚РµР»РµР№: <b>{targets}</b>\n"
        f"рџ” РљРЅРѕРїРѕРє: <b>{len(buttons)}</b>\n\n"
        "<i>РџСЂРµРІСЊСЋ РІС‹С€Рµ в¬†пёЏ РџСЂРѕРІРµСЂСЊ РµС‰С‘ СЂР°Р·!</i>"
    )
    await state.update_data(
        buttons=[{"text": b.text, "url": b.url} for b in buttons],
    )
    if edit:
        await target.edit_text(text, reply_markup=confirm_kb())
    else:
        await target.answer(text, reply_markup=confirm_kb())


async def bc_nobtn_impl(callback: CallbackQuery, state: FSMContext) -> None:
    await callback.answer()
    await finish_confirm(callback.message, state, [], edit=True)


@dp.callback_query(F.data == "bc:nobtn", Bcast.buttons, IsAdmin())
async def bc_nobtn(callback: CallbackQuery, state: FSMContext) -> None:
    await bc_nobtn_impl(callback, state)


@dp.message(Bcast.buttons, F.text)
async def bcast_buttons(message: Message, state: FSMContext) -> None:
    if message.text.startswith("/"):
        await message.answer("вљ пёЏ РџСЂРёС€Р»Рё РєРЅРѕРїРєРё С„РѕСЂРјР°С‚Р° <code>РўРµРєСЃС‚ | https://СЃСЃС‹Р»РєР°</code>, РЅР°Р¶РјРё В«Р‘РµР· РєРЅРѕРїРѕРєВ» РёР»Рё /cancel")
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
            "вљ пёЏ РќРµ РїРѕРЅСЏР» СЃС‚СЂРѕРєРё:\n" + "\n".join(f"<code>{esc(e)}</code>" for e in errors[:3]) +
            "\n\nР¤РѕСЂРјР°С‚: <code>РўРµРєСЃС‚ | https://СЃСЃС‹Р»РєР°</code>"
        )
        return
    if not buttons:
        await message.answer("рџ¤” РџСѓСЃС‚Рѕ. РџСЂРёС€Р»Рё С…РѕС‚СЏ Р±С‹ РѕРґРЅСѓ РєРЅРѕРїРєСѓ РёР»Рё Р¶РјРё В«Р‘РµР· РєРЅРѕРїРѕРєВ».")
        return
    buttons = buttons[:10]
    kb = InlineKeyboardMarkup(inline_keyboard=[[b] for b in buttons])
    await message.answer("рџ” РџСЂРµРґРїСЂРѕСЃРјРѕС‚СЂ РєРЅРѕРїРѕРє:", reply_markup=kb)
    await finish_confirm(message, state, buttons, edit=False)


@dp.callback_query(F.data == "bc:go", IsAdmin())
async def bc_go(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    data = await state.get_data()
    if "src_chat" not in data:
        await callback.answer("Р§РµСЂРЅРѕРІРёРє РїРѕС‚РµСЂСЏРЅ вЂ” РЅР°С‡РЅРё Р·Р°РЅРѕРІРѕ С‡РµСЂРµР· /admin", show_alert=True)
        return
    await callback.answer("рџљЂ РџРѕРµС…Р°Р»Рё!")
    buttons = [InlineKeyboardButton(text=b["text"], url=b["url"]) for b in data.get("buttons", [])]
    src_chat, src_msg = data["src_chat"], data["src_msg"]
    await state.clear()
    asyncio.create_task(run_broadcast(bot, callback.from_user.id, src_chat, src_msg, buttons))


@dp.callback_query(F.data == "bc:editbtn", Bcast.buttons)
async def bc_editbtn(callback: CallbackQuery, state: FSMContext) -> None:
    await callback.answer()
    await callback.message.edit_text(
        "вњЏпёЏ РџСЂРёС€Р»Рё РЅРѕРІС‹Р№ РЅР°Р±РѕСЂ РєРЅРѕРїРѕРє:\n<code>РўРµРєСЃС‚ | https://СЃСЃС‹Р»РєР°</code>\n\n/cancel вЂ” РѕС‚РјРµРЅР°",
    )
    await state.set_state(Bcast.buttons)


@dp.callback_query(F.data == "bc:cancel")
async def bc_cancel(callback: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await callback.answer("РћС‚РјРµРЅРµРЅРѕ")
    await callback.message.edit_text(ADMIN_HOME, reply_markup=admin_menu_kb())


@dp.callback_query(F.data.startswith("mode:"))
async def on_mode(callback: CallbackQuery) -> None:
    mode = 1 if callback.data.endswith("doc") else 0
    set_send_mode(callback.from_user.id, mode)
    await callback.answer("РќР°СЃС‚СЂРѕР№РєР° СЃРѕС…СЂР°РЅРµРЅР° вњ…")
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
        await callback.message.answer("рџ“Ћ РџСЂРѕСЃС‚Рѕ РїСЂРёС€Р»Рё РјРЅРµ С„РѕС‚Рѕ РёР»Рё С„Р°Р№Р» вЂ” СЏ СЃСЂР°Р·Сѓ РЅР°С‡РЅСѓ СЃРєР°РЅРёСЂРѕРІР°РЅРёРµ!")
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
        await callback.answer("вЊ› Р”Р°РЅРЅС‹Рµ СѓСЃС‚Р°СЂРµР»Рё вЂ” РѕС‚РїСЂР°РІСЊ С„Р°Р№Р» Р·Р°РЅРѕРІРѕ", show_alert=True)
        return

    await callback.answer()
    stage = await callback.message.edit_text("рџ§№ <b>РЎС‚РёСЂР°СЋ С†РёС„СЂРѕРІС‹Рµ СЃР»РµРґС‹вЂ¦</b>\n\nв¬›в¬›в¬›в¬›в¬›")

    data = entry["data"]
    kind = entry["kind"]
    name = entry["name"]

    try:
        removed_lines = []
        if kind == "image":
            exif = get_exif(Image.open(io.BytesIO(data)))
            removed_lines.append(f"в–«пёЏ {count_fields(exif)} СЃРєСЂС‹С‚С‹С… РїРѕР»РµР№")
            if fmt_value("Model", exif.get("Model")):
                removed_lines.insert(0, "в–«пёЏ РґР°РЅРЅС‹Рµ РєР°РјРµСЂС‹ рџ“±")
            if isinstance(exif.get("GPSInfo"), dict) and gps_to_decimal(exif["GPSInfo"]):
                removed_lines.insert(0, "в–«пёЏ GPS-РєРѕРѕСЂРґРёРЅР°С‚С‹ рџ“Ќ")
            clean_data, filename = strip_image(data)
        elif kind == "pdf":
            _report, summary = analyze_pdf(data)
            removed_lines.append(f"в–«пёЏ ~{summary['total']} РјРµС‚Р°РїРѕР»РµР№")
            clean_data, filename = clean_pdf(data)
        elif kind == "audio":
            removed_lines.append("в–«пёЏ РІСЃРµ Р°СѓРґРёРѕ-С‚РµРіРё рџЋ§")
            clean_data, filename = clean_audio(data, name or "audio.mp3")
        else:
            raise ValueError("not cleanable")
    except Exception:
        logging.exception("clean failed")
        await stage.edit_text("рџ’Ґ <b>Р§С‚Рѕ-С‚Рѕ РїРѕС€Р»Рѕ РЅРµ С‚Р°Рє</b>\n\nРџРѕРїСЂРѕР±СѓР№ РґСЂСѓРіРѕР№ С„РѕСЂРјР°С‚ С„Р°Р№Р»Р°")
        return

    checklist = "\n".join(removed_lines[:4])
    caption = (
        "вњ… <b>Р¤Р°Р№Р» РѕС‡РёС‰РµРЅ!</b>\n\n"
        f"<blockquote>РЎС‚РµСЂС‚Рѕ:\n{esc(checklist)}</blockquote>\n"
        "РўРµРїРµСЂСЊ РѕРЅ РЅРёС‡РµРіРѕ Рѕ С‚РµР±Рµ РЅРµ СЂР°СЃСЃРєР°Р¶РµС‚ рџ”’"
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
        await callback.answer("вЊ› Р”Р°РЅРЅС‹Рµ СѓСЃС‚Р°СЂРµР»Рё вЂ” РѕС‚РїСЂР°РІСЊ С„Р°Р№Р» Р·Р°РЅРѕРІРѕ", show_alert=True)
        return
    try:
        details = build_details(get_exif(Image.open(io.BytesIO(entry["data"]))))
    except Exception:
        details = None
    if not details:
        await callback.answer("Р”РѕРїРѕР»РЅРёС‚РµР»СЊРЅС‹С… РїРѕР»РµР№ РЅРµС‚", show_alert=True)
        return
    await callback.answer()
    await callback.message.answer(
        "рџ“– <b>РџРѕР»РЅС‹Р№ РґР°РјРї РјРµС‚Р°РґР°РЅРЅС‹С…</b>\n"
        f"<pre>{details}</pre>",
        link_preview_options=LinkPreviewOptions(is_disabled=True),
    )


async def handle_file(message: Message, bot: Bot) -> None:
    user = message.from_user
    touch_user(user.id, user.full_name, user.username)

    if is_banned(user.id):
        await message.answer("рџљ« Р”РѕСЃС‚СѓРї Р·Р°РєСЂС‹С‚.")
        return

    status = await message.answer(
        "рџ”Ћ <i>РЎРєР°РЅРёСЂСѓСЋ С„Р°Р№Р»вЂ¦</i>",
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
        if message.photo or mime.startswith("image/") or lower_name.endswith(IMAGE_EXTS):
            image = Image.open(io.BytesIO(data))
            image.load()
            entry["kind"] = "image"
            report, summary, coords = build_report(image, len(data), source_name)
            markup = build_markup(key, coords, summary["has_details"])
            note = ""
            if compressed:
                note = "\n\n<i>вљ пёЏ Telegram СѓР¶Рµ СЃР¶Р°Р» СЌС‚Рѕ С„РѕС‚Рѕ Рё СЃС‚С‘СЂ С‡Р°СЃС‚СЊ РґР°РЅРЅС‹С….\nРћС‚РїСЂР°РІСЊ С„Р°Р№Р»РѕРј (рџ“Ћ) вЂ” СѓРІРёР¶Сѓ РЅР°СЃС‚РѕСЏС‰РёР№ EXIF</i>"
            bump_stat(user.id, "scanned")
            if coords:
                bump_stat(user.id, "gps_hits")
            await status.edit_text(report + note, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif mime == "application/pdf" or lower_name.endswith(".pdf"):
            report, _summary = analyze_pdf(data)
            entry["kind"] = "pdf"
            markup = build_markup(key, None, False, kind="pdf")
            bump_stat(user.id, "scanned")
            await status.edit_text(report, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif lower_name.endswith(OFFICE_EXTS):
            report = analyze_office(data, source_name or "document")
            bump_stat(user.id, "scanned")
            await status.edit_text(report + "\n\n<i>рџ§№ РћС‡РёСЃС‚РєР° РґРѕРєСѓРјРµРЅС‚РѕРІ СЃРєРѕСЂРѕвЂ¦</i>", link_preview_options=LinkPreviewOptions(is_disabled=True))
        elif mime.startswith("audio/") or lower_name.endswith(AUDIO_EXTS):
            result = analyze_audio(data, source_name or "audio")
            if result is None:
                size_line = f"рџ“„ <b>{esc(source_name)}</b>\nрџ’ѕ {human_size(len(data))}\nрџЏ· MIME: {esc(mime or 'РЅРµРёР·РІРµСЃС‚РЅРѕ')}"
                await status.edit_text(size_line + "\n\nрџ¤· РќРµ СЃРјРѕРі СЂР°Р·РѕР±СЂР°С‚СЊ С‚РµРіРё СЌС‚РѕРіРѕ Р°СѓРґРёРѕ.")
                return
            report, has_tags = result
            entry["kind"] = "audio"
            markup = build_markup(key, None, False, kind="audio")
            bump_stat(user.id, "scanned")
            await status.edit_text(report, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))
        else:
            size_line = f"рџ“„ <b>{esc(source_name)}</b>\nрџ’ѕ {human_size(len(data))}\nрџЏ· MIME: {esc(mime or 'РЅРµРёР·РІРµСЃС‚РЅРѕ')}"
            await status.edit_text(size_line + "\n\nрџ¤· РњРµС‚Р°РґР°РЅРЅС‹Рµ РґР»СЏ СЌС‚РѕРіРѕ С‚РёРїР° СЏ РїРѕРєР° РЅРµ С‡РёС‚Р°СЋ.\nРџРѕРїСЂРѕР±СѓР№ РёР·РѕР±СЂР°Р¶РµРЅРёРµ, PDF, Р°СѓРґРёРѕ РёР»Рё РґРѕРєСѓРјРµРЅС‚ Office.")
            return

        pending[key] = entry
    except Exception:
        logging.exception("analyze failed")
        await status.edit_text("рџµ <b>РќРµ СЃРјРѕРі РїСЂРѕС‡РёС‚Р°С‚СЊ СЌС‚РѕС‚ С„Р°Р№Р»</b>\n\nРџСЂРёС€Р»Рё РёР·РѕР±СЂР°Р¶РµРЅРёРµ, PDF, Р°СѓРґРёРѕ РёР»Рё РґРѕРєСѓРјРµРЅС‚ Office.")


@dp.message(F.photo)
async def on_photo(message: Message, bot: Bot) -> None:
    await handle_file(message, bot)


@dp.message(F.document)
async def on_document(message: Message, bot: Bot) -> None:
    await handle_file(message, bot)


@dp.message()
async def on_unknown(message: Message) -> None:
    await message.answer(
        "рџ¤” РќРµ РїРѕРЅРёРјР°СЋ.\n\nРџСЂРёС€Р»Рё С„РѕС‚Рѕ РёР»Рё С„Р°Р№Р» (рџ“Ћ) РґР»СЏ СЃРєР°РЅРёСЂРѕРІР°РЅРёСЏ,\nРёР»Рё РѕС‚РєСЂРѕР№ РјРµРЅСЋ С‡РµСЂРµР· /start"
    )


async def main() -> None:
    os.makedirs(DB_DIR, exist_ok=True)
    load_admins()
    with db_connect():
        pass
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await bot.delete_webhook(drop_pending_updates=True)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
