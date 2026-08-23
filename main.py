import html
import io
import logging
import os
import secrets
import time
from datetime import datetime

import pillow_heif
from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ChatAction, ParseMode
from aiogram.filters import Command, CommandStart
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

pillow_heif.register_heif_opener()

BOT_TOKEN = os.getenv("BOT_TOKEN")

logging.basicConfig(level=logging.INFO)

dp = Dispatcher()

pending: dict[str, dict] = {}
PENDING_TTL = 1800
MAX_PENDING = 200

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


def esc(value) -> str:
    return html.escape(str(value))


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
    return {k: v for k, v in exif.items() if v not in (None, "")}


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
    bar = "🔴" * level + "⚪" * (5 - level) if level >= 4 else "🟡" * level + "⚪" * (5 - level) if level >= 2 else "🟢" * max(level, 1) + "⚪" * (5 - max(level, 1))
    if level == 0:
        bar = "🟢🟢🟢🟢🟢"
    return (
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"<b>УРОВЕНЬ РИСКА:</b> {label}\n"
        f"{bar}\n"
        f"<i>{hint}</i>"
    )


def human_size(n: int) -> str:
    if n >= 1024 * 1024:
        return f"{n / 1024 / 1024:.1f} МБ"
    return f"{n / 1024:.0f} КБ"


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
        lines.append(
            f"📍 <b>ГЕОЛОКАЦИЯ:</b> {lat:.5f}, {lon:.5f}"
        )

    total = count_fields(exif)
    lines.append("")
    lines.append(risk_block(level))

    summary = {
        "total": total,
        "has_gps": coords is not None,
        "has_camera": bool(fmt_value("Model", exif.get("Model"))),
        "has_date": bool(fmt_value("DateTimeOriginal", exif.get("DateTimeOriginal"))),
        "has_details": build_details(exif) is not None,
    }
    return "\n".join(lines), summary, coords


def build_markup(key: str, coords, has_details: bool) -> InlineKeyboardMarkup:
    rows = []
    if coords:
        lat, lon = coords
        rows.append([InlineKeyboardButton(text="📍 Открыть на карте", url=f"https://maps.google.com/?q={lat},{lon}")])
    rows.append([InlineKeyboardButton(text="🧹 Очистить всё", callback_data=f"clean:{key}")])
    if has_details:
        rows.append([InlineKeyboardButton(text="📖 Все данные", callback_data=f"all:{key}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def prune_pending() -> None:
    now = time.time()
    stale = [k for k, v in pending.items() if now - v["ts"] > PENDING_TTL]
    for k in stale:
        pending.pop(k, None)
    while len(pending) > MAX_PENDING:
        pending.pop(next(iter(pending)))


def strip_metadata(data: bytes):
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


START_TEXT = (
    "🔍 <b>KUDEX META</b>\n"
    "<blockquote>Каждое фото рассказывает о тебе\nбольше, чем ты думаешь 👀</blockquote>\n\n"
    "Пришли файл — и я вытащу всё скрытое:\n\n"
    "📱 Камера и устройство\n"
    "📅 Точная дата и время снимка\n"
    "📍 Место съёмки с точностью до метра\n"
    "💻 Программа обработки\n"
    "⚙️ ISO · диафрагма · выдержка\n\n"
    "А потом одной кнопкой сотру все следы 🧹"
)

HELP_TEXT = (
    "📖 <b>Как это работает</b>\n\n"
    "<b>1.</b> Пришли фото <u>файлом</u> (📎 → Файл)\n"
    "<b>2.</b> Получи карточку со всеми скрытыми данными\n"
    "<b>3.</b> Жми «🧹 Очистить всё» — забирай чистый файл\n\n"
    "<b>Поддерживаю:</b> JPG · PNG · WEBP · HEIC"
)


async def handle_image(message: Message, bot: Bot) -> None:
    status = await message.answer("🔎 <i>Сканирую файл…</i>", link_preview_options=LinkPreviewOptions(is_disabled=True))

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

    try:
        image = Image.open(io.BytesIO(data))
        image.load()
    except Exception:
        await status.edit_text("😵 <b>Не смог прочитать этот файл</b>\n\nПришли изображение: JPG, PNG, WEBP или HEIC")
        return

    prune_pending()
    key = secrets.token_urlsafe(16)
    pending[key] = {"ts": time.time(), "data": data}

    report, summary, coords = build_report(image, len(data), source_name)
    markup = build_markup(key, coords, summary["has_details"])

    note = ""
    if compressed:
        note = "\n\n<i>⚠️ Telegram уже сжал это фото и стёр часть данных.\nОтправь файлом (📎) — увижу настоящий EXIF</i>"

    await status.edit_text(report + note, reply_markup=markup, link_preview_options=LinkPreviewOptions(is_disabled=True))


@dp.message(CommandStart())
async def cmd_start(message: Message) -> None:
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✨ Поделиться ботом", url="https://t.me/share/url?url=https://t.me/KudexMeta_bot&text=Узнаю всё о твоих фото и стираю метаданные")],
        ]
    )
    await message.answer(START_TEXT, reply_markup=kb)


@dp.message(Command("help"))
async def cmd_help(message: Message) -> None:
    await message.answer(HELP_TEXT)


@dp.message(F.photo)
async def on_photo(message: Message, bot: Bot) -> None:
    await handle_image(message, bot)


@dp.message(F.document)
async def on_document(message: Message, bot: Bot) -> None:
    doc = message.document
    mime = doc.mime_type or ""
    if mime.startswith("image/") or (doc.file_name or "").lower().endswith(
        (".jpg", ".jpeg", ".png", ".webp", ".heic", ".heif", ".bmp", ".tiff")
    ):
        await handle_image(message, bot)
    else:
        await message.answer(
            "🤷 <b>Это не картинка</b>\n\n"
            f"📄 {esc(doc.file_name)} · {human_size(doc.file_size or 0)}\n\n"
            "Я работаю с изображениями: JPG · PNG · WEBP · HEIC"
        )


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
    try:
        exif = get_exif(Image.open(io.BytesIO(data)))
        removed = count_fields(exif)
        has_gps = isinstance(exif.get("GPSInfo"), dict) and gps_to_decimal(exif["GPSInfo"]) is not None
        has_camera = bool(fmt_value("Model", exif.get("Model")))
        clean_data, filename = strip_metadata(data)
    except Exception:
        await stage.edit_text("💥 <b>Что-то пошло не так</b>\n\nПопробуй другой формат файла")
        return

    removed_lines = [f"▫️ {removed} скрытых полей"]
    if has_camera:
        removed_lines.insert(0, "▫️ данные камеры 📱")
    if has_gps:
        removed_lines.insert(0, "▫️ GPS-координаты 📍")

    checklist = "\n".join(removed_lines[:4])
    await callback.message.answer_document(
        BufferedInputFile(clean_data, filename=filename),
        caption=(
            "✅ <b>Файл очищен!</b>\n\n"
            f"<blockquote>Стерто:\n{esc(checklist)}</blockquote>\n"
            "Теперь он ничего о тебе не расскажет 🔒"
        ),
    )
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
        image = Image.open(io.BytesIO(entry["data"]))
        details = build_details(get_exif(image))
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


@dp.callback_query(F.data == "noop")
async def on_noop(callback: CallbackQuery) -> None:
    await callback.answer()


async def main() -> None:
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await bot.delete_webhook(drop_pending_updates=True)
    await dp.start_polling(bot)


if __name__ == "__main__":
    import asyncio

    asyncio.run(main())
