import io
import logging
import os
import secrets
from datetime import datetime

import pillow_heif
from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)
from PIL import Image
from PIL.ExifTags import GPSTAGS, TAGS

pillow_heif.register_heif_opener()

BOT_TOKEN = os.getenv("BOT_TOKEN")

logging.basicConfig(level=logging.INFO)

dp = Dispatcher()

pending: dict[str, bytes] = {}

EXIF_FIELDS = {
    "Make": "Производитель",
    "Model": "Модель",
    "DateTimeOriginal": "Дата съёмки",
    "DateTime": "Дата изменения",
    "ISOSpeedRatings": "ISO",
    "FNumber": "Диафрагма",
    "ExposureTime": "Выдержка",
    "FocalLength": "Фокусное расстояние",
    "LensModel": "Объектив",
    "Software": "ПО",
}

def clean_kb(key: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🧹 Очистить метаданные", callback_data=f"clean:{key}")],
        ]
    )


def get_exif(image: Image.Image) -> dict:
    try:
        raw = image.getexif()
    except Exception:
        return {}
    exif = {}
    if not raw:
        return exif
    for tag_id, value in raw.items():
        tag = TAGS.get(tag_id, tag_id)
        exif[tag] = value
    ifd = raw.get_ifd(0x8769)
    for tag_id, value in ifd.items():
        tag = TAGS.get(tag_id, tag_id)
        exif[tag] = value
    gps_ifd = raw.get_ifd(0x8825)
    if gps_ifd:
        gps = {GPSTAGS.get(k, k): v for k, v in gps_ifd.items()}
        exif["GPSInfo"] = gps
    return exif


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


def format_value(tag: str, value) -> str:
    if value is None or value == "":
        return None
    if isinstance(value, bytes):
        try:
            value = value.decode(errors="ignore").strip("\x00")
        except Exception:
            return None
    if tag == "FNumber":
        return f"f/{float(value[0]) / float(value[1]):.1f}" if isinstance(value, tuple) else f"f/{float(value):.1f}"
    if tag == "ExposureTime":
        try:
            val = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
            return f"1/{round(1 / val)} с" if val < 1 else f"{val} с"
        except Exception:
            return None
    if tag == "FocalLength":
        mm = float(value[0]) / float(value[1]) if isinstance(value, tuple) else float(value)
        return f"{mm:g} мм"
    if tag in ("DateTimeOriginal", "DateTime", "DateTimeDigitized"):
        try:
            dt = datetime.strptime(str(value), "%Y:%m:%d %H:%M:%S")
            return dt.strftime("%d.%m.%Y %H:%M:%S")
        except Exception:
            return str(value)
    text = str(value).strip()
    return text or None


def build_metadata_text(image: Image.Image, file_size: int, source_name: str | None) -> str:
    lines = [f"<b>📋 Метаданные файла</b>"]

    name = source_name or "photo"
    lines.append(f"\n📄 <b>Имя:</b> {name}")
    lines.append(f"🖼 <b>Формат:</b> {image.format or '?'}")
    lines.append(f"📐 <b>Разрешение:</b> {image.width}×{image.height}")
    lines.append(f"💾 <b>Размер:</b> {file_size / 1024:.1f} КБ")

    exif = get_exif(image)

    shown = set()
    personal_lines = []
    for tag, title in EXIF_FIELDS.items():
        value = format_value(tag, exif.get(tag))
        if value:
            icon = {"Make": "🏭", "Model": "📱", "DateTimeOriginal": "📅", "DateTime": "📅",
                    "ISOSpeedRatings": "💡", "FNumber": "🔘", "ExposureTime": "⏱",
                    "FocalLength": "🔭", "LensModel": "🔭", "Software": "💻"}.get(title, "•")
            personal_lines.append(f"{icon} <b>{title}:</b> {value}")
            shown.add(tag)

    if personal_lines:
        lines.append("\n<b>📷 Съёмка</b>")
        lines.extend(personal_lines)

    coords = None
    gps = exif.get("GPSInfo")
    if isinstance(gps, dict):
        coords = gps_to_decimal(gps)
    if coords:
        lat, lon = coords
        lines.append("\n<b>📍 Геолокация</b>")
        lines.append(f"🌐 Широта: {lat:.6f}")
        lines.append(f"🌐 Долгота: {lon:.6f}")
        lines.append(f'🗺 <a href="https://maps.google.com/?q={lat},{lon}">Открыть на карте</a>')

    extra_tags = len(exif)
    hidden_count = 0
    for tag in exif:
        if isinstance(exif[tag], dict):
            hidden_count += len(exif[tag])
        elif isinstance(exif[tag], bytes):
            hidden_count += 1
    lines.append("\n<b>🔒 Скрытые данные</b>")
    if exif:
        lines.append(f"⚠️ Найдено EXIF-полей: {extra_tags}")
        if coords:
            lines.append("🚨 Файл содержит ваши координаты!")
    else:
        lines.append("✅ EXIF-данные не найдены — файл уже чистый")

    return "\n".join(lines)


def strip_metadata(data: bytes) -> tuple[bytes, str]:
    image = Image.open(io.BytesIO(data))
    clean = Image.new(image.mode, image.size)
    clean.putdata(list(image.getdata()))
    buf = io.BytesIO()
    fmt = (image.format or "JPEG").upper()
    if fmt == "JPG":
        fmt = "JPEG"
    save_kwargs = {}
    if fmt == "JPEG":
        save_kwargs.update(quality=95, subsampling=0)
        clean.save(buf, "JPEG", **save_kwargs)
        return buf.getvalue(), "cleaned.jpg"
    if fmt == "PNG":
        clean.save(buf, "PNG")
        return buf.getvalue(), "cleaned.png"
    if fmt == "WEBP":
        clean.save(buf, "WEBP", quality=95)
        return buf.getvalue(), "cleaned.webp"
    clean.convert("RGB").save(buf, "JPEG", quality=95)
    return buf.getvalue(), "cleaned.jpg"


async def handle_image(message: Message, bot: Bot) -> None:
    status = await message.answer("🔍 Читаю метаданные…")

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
        await status.edit_text("❌ Не удалось прочитать изображение. Поддерживаются JPG, PNG, WEBP, HEIC.")
        return

    key = secrets.token_urlsafe(16)
    pending[key] = data

    note = ""
    if message.photo and compressed:
        note = "\n\nℹ️ Telegram уже сжал фото и удалил часть EXIF. Отправь файлом (📎), чтобы увидеть настоящие метаданные."

    text = build_metadata_text(image, len(data), source_name) + note
    await status.edit_text(text, disable_web_page_preview=True, reply_markup=clean_kb(key))


@dp.message(CommandStart())
async def cmd_start(message: Message) -> None:
    await message.answer(
        "<b>KudexMeta</b> — узнай всё о своём файле 🔍\n\n"
        "Пришли мне <b>фото или файл</b>, и я покажу:\n"
        "• 📷 Данные камеры и настройки съёмки\n"
        "• 📅 Дату съёмки\n"
        "• 📍 Геолокацию (если есть)\n"
        "• 📐 Разрешение и размер\n\n"
        "Затем одной кнопкой можно <b>очистить все скрытые метаданные</b> 🧹\n\n"
        "⚠️ Лучше отправлять файлом (📎 → Файл), так сохранится полный EXIF."
    )


@dp.message(Command("help"))
async def cmd_help(message: Message) -> None:
    await message.answer(
        "<b>Как пользоваться</b>\n\n"
        "1️⃣ Пришли фото или файл (изображение)\n"
        "2️⃣ Получи отчёт с метаданными\n"
        "3️⃣ Нажми «🧹 Очистить метаданные» — получишь чистую копию без EXIF\n\n"
        "Поддержка: JPG, PNG, WEBP, HEIC"
    )


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
        size_kb = (doc.file_size or 0) / 1024
        await message.answer(
            f"📄 <b>{doc.file_name}</b>\n"
            f"💾 Размер: {size_kb:.1f} КБ\n"
            f"🏷 MIME: {mime or 'неизвестно'}\n\n"
            "Глубокие метаданные поддерживаются только для изображений "
            "(JPG, PNG, WEBP, HEIC)."
        )


@dp.callback_query(F.data.startswith("clean:"))
async def on_clean(callback: CallbackQuery, bot: Bot) -> None:
    key = callback.data.split(":", 1)[1]
    data = pending.pop(key, None)
    if data is None:
        await callback.answer("Данные устарели, отправь файл заново", show_alert=True)
        return

    await callback.answer("🧹 Очищаю…")
    msg = await callback.message.answer("🧹 Удаляю метаданные…")

    try:
        clean_data, filename = strip_metadata(data)
    except Exception:
        await msg.edit_text("❌ Не удалось очистить файл. Попробуй другой формат.")
        return

    await callback.message.answer_document(
        BufferedInputFile(clean_data, filename=filename),
        caption="✅ Готово! Все метаданные удалены.\n\nУдалено: EXIF, GPS-координаты, данные камеры, дата съёмки.",
    )
    await msg.delete()


async def main() -> None:
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await dp.start_polling(bot)


if __name__ == "__main__":
    import asyncio

    asyncio.run(main())
