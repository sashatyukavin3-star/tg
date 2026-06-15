"""Telegram-бот с инлайн-кнопками — Vercel serverless webhook."""
from __future__ import annotations
import ast, asyncio, json, logging, os, re, sys, time, tempfile
from collections import defaultdict
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from typing import Optional

from telegram import (Update, InlineKeyboardButton, InlineKeyboardMarkup,
                      BotCommand)
from telegram.ext import (Application, CommandHandler, MessageHandler,
                          CallbackQueryHandler, ContextTypes, filters)
from telegram.constants import ParseMode, ChatAction
from openai import OpenAI, APIError

log = logging.getLogger("bot")
logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")

# ── Конфиг ────────────────────────────────────────────────────────────────
TOKEN    = os.environ.get("TG_BOT_TOKEN", "")
PROVIDER = os.environ.get("AI_PROVIDER", "llm7").lower()
PROVIDERS = {
    "llm7":       {"url": "https://api.llm7.io/v1",
                   "key_env": "LLM7_API_KEY", "model": "gpt-4o-mini",     "label": "LLM7 🆓"},
    "openrouter": {"url": "https://openrouter.ai/api/v1",
                   "key_env": "OPENROUTER_API_KEY", "model": "deepseek/deepseek-chat:free", "label": "OpenRouter"},
    "groq":       {"url": "https://api.groq.com/openai/v1",
                   "key_env": "GROQ_API_KEY", "model": "llama-3.3-70b-versatile", "label": "Groq ⚡"},
    "gemini":     {"url": "https://generativelanguage.googleapis.com/v1beta/openai/",
                   "key_env": "GEMINI_API_KEY", "model": "gemini-2.5-flash", "label": "Gemini"},
}
_p    = PROVIDERS.get(PROVIDER, PROVIDERS["llm7"])
AIKEY = os.environ.get(_p["key_env"], "none" if PROVIDER == "llm7" else "")
MODEL = os.environ.get("AI_MODEL", _p["model"])
LABEL = _p["label"]

# ── Состояния и история ────────────────────────────────────────────────────
_hist:  dict[int, list[dict]] = defaultdict(list)
_ts:    dict[int, float]      = {}
_state: dict[int, str]        = {}          # "" | "sqli" | "chat"
MAX_H, TTL = 20, 10800

def _get_hist(uid: int) -> list[dict]:
    if uid in _ts and time.monotonic() - _ts[uid] > TTL:
        _hist.pop(uid, None); _ts.pop(uid, None)
    return _hist.setdefault(uid, [])

def _push(uid: int, msg: dict):
    h = _get_hist(uid); h.append(msg); _ts[uid] = time.monotonic()
    if len(h) > MAX_H: _hist[uid] = h[-MAX_H:]

def _state_set(uid: int, s: str): _state[uid] = s
def _state_get(uid: int) -> str:  return _state.get(uid, "")

# ── ИИ ────────────────────────────────────────────────────────────────────
_client: Optional[OpenAI] = (
    OpenAI(api_key=AIKEY, base_url=_p["url"], timeout=55.0) if AIKEY else None
)
SYSTEM = ("Ты — ИИ-ассистент, специалист по кибербезопасности и программированию. "
          "Отвечай по-русски, чётко и по делу. Код — в блоках с подсветкой синтаксиса.")

def ai_chat(messages: list[dict]) -> str:
    if not _client:
        return "⚠️ Нет ИИ-ключа. Задай `AI_PROVIDER=llm7` (без ключа)"
    try:
        r = _client.chat.completions.create(
            model=MODEL,
            messages=[{"role": "system", "content": SYSTEM}] + messages[-MAX_H:])
        return r.choices[0].message.content or "(пустой ответ)"
    except APIError as e:
        return f"⚠️ API ошибка: {str(e)[:200]}"

# ── SQLi детектор ─────────────────────────────────────────────────────────
SQL_RE = re.compile(
    r"\b(SELECT|INSERT|UPDATE|DELETE|DROP|UNION|WHERE|FROM|INTO|EXECUTE)\b", re.I)

def _sql(t: str) -> bool: return bool(SQL_RE.search(t))

def _fstr_text(n: ast.JoinedStr) -> str:
    return "".join(v.value if isinstance(v, ast.Constant) else "{}" for v in n.values)

def _binop_text(n: ast.BinOp) -> str:
    parts: list[str] = []
    def _c(x):
        if isinstance(x, ast.BinOp) and isinstance(x.op, ast.Add): _c(x.left); _c(x.right)
        elif isinstance(x, ast.Constant): parts.append(str(x.value))
    _c(n); return "".join(parts)

class _V(ast.NodeVisitor):
    def __init__(self, src: list[str]):
        self.src = src; self.findings: list[dict] = []
    def _snip(self, n): return self.src[n.lineno-1].strip() if 0 < n.lineno <= len(self.src) else ""
    def visit_JoinedStr(self, n):
        if _sql(_fstr_text(n)) and any(isinstance(v, ast.FormattedValue) for v in n.values):
            self.findings.append({"line": n.lineno, "rule": "f‑строка с SQL", "snip": self._snip(n),
                                   "fix": 'execute("... WHERE x=?", (val,))'})
        self.generic_visit(n)
    def visit_BinOp(self, n):
        if isinstance(n.op, ast.Add) and _sql(_binop_text(n)):
            self.findings.append({"line": n.lineno, "rule": "конкатенация + SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы"})
        elif isinstance(n.op, ast.Mod) and isinstance(n.left, ast.Constant) and _sql(str(n.left.value)):
            self.findings.append({"line": n.lineno, "rule": "% форматирование SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы"})
        self.generic_visit(n)
    def visit_Call(self, n):
        if (isinstance(n.func, ast.Attribute) and n.func.attr == "format"
                and isinstance(n.func.value, ast.Constant) and _sql(str(n.func.value.value))):
            self.findings.append({"line": n.lineno, "rule": ".format() в SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы"})
        self.generic_visit(n)

def detect_sqli(code: str) -> list[dict]:
    try: tree = ast.parse(code)
    except SyntaxError as e:
        return [{"line": e.lineno or 0, "rule": "Синтаксическая ошибка", "snip": str(e.msg), "fix": ""}]
    v = _V(code.splitlines()); v.visit(tree)
    seen: set = set()
    return [f for f in v.findings if (k := (f["rule"], f["line"])) not in seen and not seen.add(k)]  # type: ignore

def sqli_report(findings: list[dict], code: str) -> str:
    if not findings:
        base = "✅ *SQL-инъекций не обнаружено*\n\nКод выглядит безопасно 👍"
    else:
        lines = [f"🔴 *Найдено уязвимостей: {len(findings)}*\n"]
        for f in findings:
            lines += [f"┌ *Строка {f['line']}* — {f['rule']}",
                      f"│ `{f['snip'][:80]}`",
                      f"└ Фикс: _{f['fix']}_", ""]
        base = "\n".join(lines)
    if not _client:
        return base
    prompt = (("Уязвимости:\n" + "\n".join(f"- стр {f['line']}: {f['rule']}" for f in findings)
               if findings else "Уязвимостей не найдено.") +
              f"\n\nКод:\n```python\n{code[:2000]}\n```\n\n"
              "Коротко: объясни риски и покажи исправленный вариант.")
    ai = ai_chat([{"role": "user", "content": prompt}])
    return base + "\n\n🧠 *ИИ-анализ:*\n" + ai

# ── Клавиатуры ────────────────────────────────────────────────────────────
def kb_main() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔍 Проверить SQLi", callback_data="mode_sqli"),
         InlineKeyboardButton("🤖 ИИ-чат",         callback_data="mode_chat")],
        [InlineKeyboardButton("📊 Статус",          callback_data="status"),
         InlineKeyboardButton("🧹 Очистить чат",    callback_data="clear")],
    ])

def kb_back() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🔄 Ещё раз", callback_data="mode_sqli"),
        InlineKeyboardButton("🏠 Меню",    callback_data="menu"),
    ]])

def kb_chat_back() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🏠 Меню", callback_data="menu"),
        InlineKeyboardButton("🧹 Очистить", callback_data="clear"),
    ]])

# ── Обработчики ───────────────────────────────────────────────────────────
WELCOME = (
    "👾 *Security Bot*\n\n"
    "Анализирую код на SQL-инъекции и общаюсь как ИИ.\n\n"
    "Выбери режим 👇"
)

async def cmd_start(u: Update, c: ContextTypes.DEFAULT_TYPE):
    _state_set(u.effective_user.id, "")
    await u.message.reply_text(
        f"{WELCOME}\n\n🧠 ИИ: *{LABEL}* {'✅' if _client else '❌'}",
        parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

async def on_callback(u: Update, c: ContextTypes.DEFAULT_TYPE):
    q   = u.callback_query
    uid = u.effective_user.id
    await q.answer()
    data = q.data

    if data == "menu":
        _state_set(uid, "")
        await q.edit_message_text(
            f"{WELCOME}\n\n🧠 ИИ: *{LABEL}* {'✅' if _client else '❌'}",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

    elif data == "mode_sqli":
        _state_set(uid, "sqli")
        await q.edit_message_text(
            "🔍 *Режим SQLi-анализа*\n\n"
            "Отправь Python-код или `.py` файл — проверю на уязвимости.\n\n"
            "_Или напиши /sqli <код> прямо сюда_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("🏠 Отмена", callback_data="menu")]]))

    elif data == "mode_chat":
        _state_set(uid, "chat")
        await q.edit_message_text(
            "🤖 *ИИ-чат активирован*\n\n"
            "Задавай вопросы по безопасности, коду, реверсу — отвечу.\n\n"
            "_Просто пиши сообщения_",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_chat_back())

    elif data == "status":
        await q.edit_message_text(
            f"⚙️ *Статус бота*\n\n"
            f"🌐 Режим: webhook (Vercel)\n"
            f"🧠 Провайдер: `{PROVIDER}` — {LABEL}\n"
            f"🤖 Модель: `{MODEL}`\n"
            f"🔑 Ключ: {'✅ есть' if _client else '❌ нет'}\n"
            f"💬 Сообщений в памяти: {len(_get_hist(uid))}",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("🏠 Меню", callback_data="menu")]]))

    elif data == "clear":
        _hist.pop(uid, None); _ts.pop(uid, None); _state_set(uid, "")
        await q.edit_message_text(
            "🧹 *Чат очищен*\n\nИстория сброшена.",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

async def handle_doc(u: Update, c: ContextTypes.DEFAULT_TYPE):
    """Принимает .py файлы и проверяет на SQLi."""
    doc   = u.message.document
    fname = (doc.file_name or "").strip()

    # Проверяем расширение явно
    if not fname.lower().endswith(".py"):
        await u.message.reply_text(
            "📎 Принимаю только `.py` файлы для SQLi-анализа.\n"
            "Пришли Python-файл!",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())
        return

    await u.message.reply_text(f"📥 Получил `{fname}`, анализирую…",
                                parse_mode=ParseMode.MARKDOWN)

    # Скачиваем во временный файл
    try:
        tg_file = await doc.get_file()
        tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".py",
                                          dir="/tmp")
        tmp.close()
        await tg_file.download_to_drive(tmp.name)
    except Exception as e:
        await u.message.reply_text(f"❌ Не удалось скачать файл: `{e}`",
                                    parse_mode=ParseMode.MARKDOWN)
        return

    try:
        code = Path(tmp.name).read_text(encoding="utf-8", errors="replace")
        if not code.strip():
            await u.message.reply_text("❌ Файл пустой.")
            return
        findings = detect_sqli(code)
        report   = sqli_report(findings, code)
        await u.message.reply_text(
            f"📄 *{fname}* — {len(code.splitlines())} строк\n\n" + report,
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_back())
    except Exception as e:
        log.exception("ошибка анализа файла")
        await u.message.reply_text(f"❌ Ошибка анализа: `{e}`",
                                    parse_mode=ParseMode.MARKDOWN)
    finally:
        Path(tmp.name).unlink(missing_ok=True)

async def cmd_sqli(u: Update, c: ContextTypes.DEFAULT_TYPE):
    parts = (u.message.text or "").split(" ", 1)
    code  = parts[1].strip() if len(parts) > 1 else ""
    if not code:
        _state_set(u.effective_user.id, "sqli")
        await u.message.reply_text(
            "🔍 Жду код для проверки — напиши его следующим сообщением\n"
            "или пришли `.py` файл.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("🏠 Отмена", callback_data="menu")]]))
        return
    await u.message.reply_text("⏳ Анализирую…")
    await u.message.reply_text(
        sqli_report(detect_sqli(code), code),
        parse_mode=ParseMode.MARKDOWN, reply_markup=kb_back())

async def handle_text(u: Update, c: ContextTypes.DEFAULT_TYPE):
    uid  = u.effective_user.id
    text = u.message.text
    mode = _state_get(uid)

    # Если ждём SQLi-код
    if mode == "sqli":
        _state_set(uid, "")
        await u.message.reply_text("⏳ Анализирую…")
        await u.message.reply_text(
            sqli_report(detect_sqli(text), text),
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_back())
        return

    # ИИ-чат (режим chat или просто текст)
    _push(uid, {"role": "user", "content": text})
    await c.bot.send_chat_action(u.effective_chat.id, ChatAction.TYPING)
    reply = ai_chat(list(_get_hist(uid)))
    _push(uid, {"role": "assistant", "content": reply})
    await u.message.reply_text(
        reply[:3900], parse_mode=ParseMode.MARKDOWN,
        reply_markup=kb_chat_back())

# ── Vercel handler ─────────────────────────────────────────────────────────
_app: Optional[Application] = None
_ready = False

async def _get_app() -> Application:
    global _app, _ready
    if not _ready:
        _app = Application.builder().token(TOKEN).updater(None).build()
        _app.add_handler(CommandHandler("start", cmd_start))
        _app.add_handler(CommandHandler("sqli",  cmd_sqli))
        _app.add_handler(CallbackQueryHandler(on_callback))
        _app.add_handler(MessageHandler(
            filters.Document.ALL, handle_doc))
        _app.add_handler(MessageHandler(
            filters.TEXT & ~filters.COMMAND, handle_text))
        await _app.initialize()
        await _app.bot.set_my_commands([
            BotCommand("start", "Главное меню"),
            BotCommand("sqli",  "Проверить код на SQLi"),
        ])
        _ready = True
    return _app

async def _process(data: dict):
    app = await _get_app()
    await app.process_update(Update.de_json(data, app.bot))

class handler(BaseHTTPRequestHandler):
    def do_POST(self):
        try:
            body = json.loads(self.rfile.read(
                int(self.headers.get("Content-Length", 0))))
            asyncio.run(_process(body))
            self._ok(b"ok")
        except Exception as e:
            log.exception("update error")
            self._ok(f"err:{e}".encode())

    def do_GET(self):
        self._ok(b"Bot is alive. POST /api/webhook for updates.")

    def _ok(self, body: bytes):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers(); self.wfile.write(body)

    def log_message(self, *a): pass
