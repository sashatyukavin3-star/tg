"""Telegram-бот — Vercel serverless. Использует Bot напрямую без Application."""
from __future__ import annotations
import ast, asyncio, json, logging, os, re, time, tempfile
from collections import defaultdict
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from typing import Optional

from telegram import (Bot, Update, InlineKeyboardButton,
                      InlineKeyboardMarkup, BotCommand)
from telegram.constants import ParseMode, ChatAction
from openai import OpenAI, APIError

log = logging.getLogger("bot")
logging.basicConfig(level=logging.INFO)

# ── Конфиг ───────────────────────────────────────────────────────────────
TOKEN    = os.environ.get("TG_BOT_TOKEN", "")
PROVIDER = os.environ.get("AI_PROVIDER", "llm7").lower()
_P = {
    "llm7":       {"url": "https://api.llm7.io/v1",       "key": "LLM7_API_KEY",        "model": "gpt-4o-mini",               "label": "LLM7 🆓"},
    "openrouter": {"url": "https://openrouter.ai/api/v1", "key": "OPENROUTER_API_KEY",   "model": "deepseek/deepseek-chat:free","label": "OpenRouter"},
    "groq":       {"url": "https://api.groq.com/openai/v1","key": "GROQ_API_KEY",        "model": "llama-3.3-70b-versatile",   "label": "Groq ⚡"},
    "gemini":     {"url": "https://generativelanguage.googleapis.com/v1beta/openai/",
                                                           "key": "GEMINI_API_KEY",       "model": "gemini-2.5-flash",          "label": "Gemini"},
}.get(PROVIDER, {"url":"https://api.llm7.io/v1","key":"LLM7_API_KEY","model":"gpt-4o-mini","label":"LLM7 🆓"})

AIKEY = os.environ.get(_P["key"], "none" if PROVIDER == "llm7" else "")
MODEL = os.environ.get("AI_MODEL", _P["model"])
LABEL = _P["label"]

# ── Состояние (в памяти, warm-контейнер) ─────────────────────────────────
_hist:  dict[int, list[dict]] = defaultdict(list)
_ts:    dict[int, float]      = {}
_state: dict[int, str]        = {}
MAX_H, TTL = 20, 10800

def _get_hist(uid: int) -> list[dict]:
    if uid in _ts and time.monotonic() - _ts[uid] > TTL:
        _hist.pop(uid, None); _ts.pop(uid, None)
    return _hist.setdefault(uid, [])

def _push(uid: int, msg: dict):
    h = _get_hist(uid); h.append(msg); _ts[uid] = time.monotonic()
    if len(h) > MAX_H: _hist[uid] = h[-MAX_H:]

def state(uid: int, s: str | None = None) -> str:
    if s is not None: _state[uid] = s
    return _state.get(uid, "")

# ── ИИ ───────────────────────────────────────────────────────────────────
_ai: Optional[OpenAI] = OpenAI(api_key=AIKEY, base_url=_P["url"], timeout=55.0) if AIKEY else None
SYS = ("Ты — ИИ-ассистент, специалист по кибербезопасности. "
       "Отвечай по-русски, чётко. Код — в блоках с подсветкой.")

def ai(messages: list[dict]) -> str:
    if not _ai: return "⚠️ Нет ключа. Задай `AI_PROVIDER=llm7` (без ключа!)"
    try:
        r = _ai.chat.completions.create(
            model=MODEL, messages=[{"role":"system","content":SYS}]+messages[-MAX_H:])
        return r.choices[0].message.content or "(пустой ответ)"
    except APIError as e: return f"⚠️ API: {str(e)[:200]}"

# ── SQLi детектор ─────────────────────────────────────────────────────────
_SQL = re.compile(r"\b(SELECT|INSERT|UPDATE|DELETE|DROP|UNION|WHERE|FROM|INTO|EXECUTE)\b", re.I)

def _has_sql(t: str) -> bool: return bool(_SQL.search(t))

def _ftext(n: ast.JoinedStr) -> str:
    return "".join(v.value if isinstance(v, ast.Constant) else "{}" for v in n.values)

def _btext(n: ast.BinOp) -> str:
    p: list[str] = []
    def _c(x):
        if isinstance(x, ast.BinOp) and isinstance(x.op, ast.Add): _c(x.left); _c(x.right)
        elif isinstance(x, ast.Constant): p.append(str(x.value))
    _c(n); return "".join(p)

class _Vis(ast.NodeVisitor):
    def __init__(self, src):
        self.src = src; self.f: list[dict] = []
    def _s(self, n): return self.src[n.lineno-1].strip() if 0 < n.lineno <= len(self.src) else ""
    def visit_JoinedStr(self, n):
        if _has_sql(_ftext(n)) and any(isinstance(v, ast.FormattedValue) for v in n.values):
            self.f.append({"line":n.lineno,"rule":"f‑строка с SQL","snip":self._s(n),"fix":'execute("...WHERE x=?",(val,))'})
        self.generic_visit(n)
    def visit_BinOp(self, n):
        if isinstance(n.op, ast.Add) and _has_sql(_btext(n)):
            self.f.append({"line":n.lineno,"rule":"конкатенация + SQL","snip":self._s(n),"fix":"Параметризованные запросы"})
        elif isinstance(n.op, ast.Mod) and isinstance(n.left,ast.Constant) and _has_sql(str(n.left.value)):
            self.f.append({"line":n.lineno,"rule":"% форматирование SQL","snip":self._s(n),"fix":"Параметризованные запросы"})
        self.generic_visit(n)
    def visit_Call(self, n):
        if (isinstance(n.func,ast.Attribute) and n.func.attr=="format"
                and isinstance(n.func.value,ast.Constant) and _has_sql(str(n.func.value.value))):
            self.f.append({"line":n.lineno,"rule":".format() с SQL","snip":self._s(n),"fix":"Параметризованные запросы"})
        self.generic_visit(n)

def scan(code: str) -> list[dict]:
    try: tree = ast.parse(code)
    except SyntaxError as e:
        return [{"line":e.lineno or 0,"rule":"Синтаксическая ошибка","snip":str(e.msg),"fix":""}]
    v = _Vis(code.splitlines()); v.visit(tree)
    seen: set = set()
    return [f for f in v.f if (k:=(f["rule"],f["line"])) not in seen and not seen.add(k)]  # type: ignore

def sqli_text(findings: list[dict], code: str) -> str:
    if not findings:
        base = "✅ *SQL-инъекций не найдено*\n\nКод выглядит безопасно 👍"
    else:
        rows = [f"🔴 *Найдено: {len(findings)} уязвимости*\n"]
        for f in findings:
            rows += [f"┌ *Строка {f['line']}* — {f['rule']}",
                     f"│ `{f['snip'][:80]}`",
                     f"└ _{f['fix']}_",""]
        base = "\n".join(rows)
    if not _ai: return base
    prompt = (("Уязвимости:\n"+"\n".join(f"- стр {f['line']}: {f['rule']}" for f in findings) if findings else "Уязвимостей нет.")+
              f"\n\nКод:\n```python\n{code[:1500]}\n```\nКоротко: риски и исправленный вариант.")
    return base + "\n\n🧠 *ИИ-анализ:*\n" + ai([{"role":"user","content":prompt}])

# ── Клавиатуры ────────────────────────────────────────────────────────────
def kb_main():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔍 Проверить SQLi", callback_data="sqli"),
         InlineKeyboardButton("🤖 ИИ-чат",         callback_data="chat")],
        [InlineKeyboardButton("📊 Статус",          callback_data="status"),
         InlineKeyboardButton("🧹 Очистить",        callback_data="clear")],
    ])

def kb_after_sqli():
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🔄 Проверить ещё", callback_data="sqli"),
        InlineKeyboardButton("🏠 Меню",           callback_data="menu"),
    ]])

def kb_chat():
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🏠 Меню",    callback_data="menu"),
        InlineKeyboardButton("🧹 Очистить", callback_data="clear"),
    ]])

def kb_back():
    return InlineKeyboardMarkup([[InlineKeyboardButton("🏠 Меню", callback_data="menu")]])

WELCOME = ("👾 *Security Bot*\n\n"
           "Анализирую код на SQL‑инъекции и общаюсь как ИИ.\n\n"
           "Выбери режим 👇")

# ── Обработчики (принимают Update + Bot напрямую) ────────────────────────
async def do_start(u: Update, bot: Bot):
    state(u.effective_user.id, "")
    await u.message.reply_text(
        f"{WELCOME}\n\n🧠 ИИ: *{LABEL}* {'✅' if _ai else '❌'}",
        parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

async def do_callback(u: Update, bot: Bot):
    q   = u.callback_query
    uid = u.effective_user.id
    await q.answer()          # ← убирает спиннер на кнопке
    d   = q.data

    if d == "menu":
        state(uid, "")
        await q.edit_message_text(
            f"{WELCOME}\n\n🧠 ИИ: *{LABEL}* {'✅' if _ai else '❌'}",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

    elif d == "sqli":
        state(uid, "sqli")
        await q.edit_message_text(
            "🔍 *Режим SQLi‑анализа*\n\n"
            "Отправь Python‑код или пришли `.py` файл.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("🏠 Отмена", callback_data="menu")]]))

    elif d == "chat":
        state(uid, "chat")
        await q.edit_message_text(
            "🤖 *ИИ‑чат*\n\nЗадавай вопросы по безопасности и коду.",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_chat())

    elif d == "status":
        await q.edit_message_text(
            f"⚙️ *Статус*\n\n"
            f"🌐 Режим: webhook (Vercel)\n"
            f"🧠 `{PROVIDER}` — {LABEL}\n"
            f"🤖 `{MODEL}`\n"
            f"🔑 {'✅ есть' if _ai else '❌ нет'}\n"
            f"💬 В памяти: {len(_get_hist(uid))} сообщ.",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_back())

    elif d == "clear":
        _hist.pop(uid, None); _ts.pop(uid, None); state(uid, "")
        await q.edit_message_text(
            "🧹 *Чат очищен*", parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())

async def do_doc(u: Update, bot: Bot):
    doc   = u.message.document
    fname = doc.file_name or ""

    if not fname.lower().endswith(".py"):
        await u.message.reply_text(
            "📎 Принимаю только `.py` файлы.\nПришли Python‑файл!",
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_main())
        return

    msg = await u.message.reply_text(f"📥 Получил `{fname}`, анализирую…",
                                      parse_mode=ParseMode.MARKDOWN)
    tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".py", dir="/tmp")
    tmp.close()
    try:
        tg_file = await bot.get_file(doc.file_id)
        await tg_file.download_to_drive(tmp.name)
        code = Path(tmp.name).read_text(encoding="utf-8", errors="replace")
        if not code.strip():
            await msg.edit_text("❌ Файл пустой.")
            return
        findings = scan(code)
        result   = sqli_text(findings, code)
        await msg.edit_text(
            f"📄 *{fname}* — {len(code.splitlines())} строк\n\n" + result,
            parse_mode=ParseMode.MARKDOWN, reply_markup=kb_after_sqli())
    except Exception as e:
        log.exception("doc error")
        await msg.edit_text(f"❌ Ошибка: `{e}`", parse_mode=ParseMode.MARKDOWN)
    finally:
        Path(tmp.name).unlink(missing_ok=True)

async def do_text(u: Update, bot: Bot):
    uid  = u.effective_user.id
    text = u.message.text or ""
    s    = state(uid)

    if text.startswith("/start"):
        await do_start(u, bot); return
    if text.startswith("/sqli"):
        code = text[5:].strip()
        if code:
            wait = await u.message.reply_text("⏳ Анализирую…")
            result = sqli_text(scan(code), code)
            await wait.edit_text(result, parse_mode=ParseMode.MARKDOWN, reply_markup=kb_after_sqli())
        else:
            state(uid, "sqli")
            await u.message.reply_text(
                "🔍 Пришли код следующим сообщением или `.py` файл.",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("🏠 Отмена", callback_data="menu")]]))
        return

    if s == "sqli":
        state(uid, "")
        wait = await u.message.reply_text("⏳ Анализирую…")
        result = sqli_text(scan(text), text)
        await wait.edit_text(result, parse_mode=ParseMode.MARKDOWN, reply_markup=kb_after_sqli())
        return

    # ИИ-чат
    _push(uid, {"role":"user","content":text})
    await bot.send_chat_action(u.effective_chat.id, ChatAction.TYPING)
    reply = ai(list(_get_hist(uid)))
    _push(uid, {"role":"assistant","content":reply})
    await u.message.reply_text(reply[:3900], parse_mode=ParseMode.MARKDOWN, reply_markup=kb_chat())

# ── Диспетчер ─────────────────────────────────────────────────────────────
async def dispatch(data: dict):
    """Создаём Bot на каждый запрос — нет проблем с event loop."""
    bot    = Bot(token=TOKEN)
    update = Update.de_json(data, bot)

    try:
        if update.callback_query:
            await do_callback(update, bot)
        elif update.message:
            if update.message.document:
                await do_doc(update, bot)
            elif update.message.text:
                await do_text(update, bot)
    finally:
        # Закрываем httpx-сессию чисто
        try: await bot.shutdown()
        except Exception: pass

# ── Vercel HTTP handler ────────────────────────────────────────────────────
class handler(BaseHTTPRequestHandler):
    def do_POST(self):
        try:
            body = json.loads(self.rfile.read(int(self.headers.get("Content-Length",0))))
            asyncio.run(dispatch(body))
            self._out(b"ok")
        except Exception as e:
            log.exception("dispatch error"); self._out(f"err:{e}".encode())

    def do_GET(self):
        self._out(b"Bot is alive.")

    def _out(self, b: bytes):
        self.send_response(200)
        self.send_header("Content-Type","text/plain")
        self.end_headers(); self.wfile.write(b)

    def log_message(self, *a): pass
