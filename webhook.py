"""
Telegram-бот — Vercel serverless webhook.
Один файл, никаких внешних пакетов кроме python-telegram-bot и openai.
"""

from __future__ import annotations
import ast, asyncio, json, logging, os, re, sys, time
from collections import defaultdict
from http.server import BaseHTTPRequestHandler
from typing import Optional

from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, ContextTypes, filters
from openai import OpenAI, APIError

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("bot")

# ── Конфиг ────────────────────────────────────────────────────────────────
TOKEN    = os.environ.get("TG_BOT_TOKEN", "")
PROVIDER = os.environ.get("AI_PROVIDER", "llm7").lower()
PROVIDERS = {
    "llm7":        {"url": "https://api.llm7.io/v1",              "key_env": "LLM7_API_KEY",        "model": "gpt-4o-mini",                       "label": "LLM7 (бесплатно)"},
    "openrouter":  {"url": "https://openrouter.ai/api/v1",        "key_env": "OPENROUTER_API_KEY",   "model": "deepseek/deepseek-chat:free",        "label": "OpenRouter"},
    "groq":        {"url": "https://api.groq.com/openai/v1",      "key_env": "GROQ_API_KEY",         "model": "llama-3.3-70b-versatile",            "label": "Groq"},
    "gemini":      {"url": "https://generativelanguage.googleapis.com/v1beta/openai/", "key_env": "GEMINI_API_KEY", "model": "gemini-2.5-flash", "label": "Gemini"},
}
_p    = PROVIDERS.get(PROVIDER, PROVIDERS["llm7"])
AIKEY = os.environ.get(_p["key_env"], "none" if PROVIDER == "llm7" else "")
MODEL = os.environ.get("AI_MODEL", _p["model"])
LABEL = _p["label"]

# ── История диалогов (в памяти, сбрасывается при cold start) ─────────────
_hist: dict[int, list[dict]] = defaultdict(list)
_ts:   dict[int, float]      = {}
MAX_H, TTL = 20, 10800

def _get(uid: int) -> list[dict]:
    if uid in _ts and time.monotonic() - _ts[uid] > TTL:
        _hist.pop(uid, None); _ts.pop(uid, None)
    return _hist.setdefault(uid, [])

def _push(uid: int, msg: dict):
    h = _get(uid); h.append(msg); _ts[uid] = time.monotonic()
    if len(h) > MAX_H: _hist[uid] = h[-MAX_H:]

# ── ИИ-движок ─────────────────────────────────────────────────────────────
_client: Optional[OpenAI] = OpenAI(api_key=AIKEY, base_url=_p["url"], timeout=55.0) if AIKEY else None

SYSTEM = ("Ты — ИИ-ассистент, специалист по безопасности и программированию. "
          "Отвечай по-русски, кратко и по делу. Код — в блоках с подсветкой.")

def ai_chat(messages: list[dict]) -> str:
    if not _client:
        return "⚠️ Нет ключа. Задай AI_PROVIDER=llm7 (ключ не нужен!)"
    try:
        r = _client.chat.completions.create(
            model=MODEL,
            messages=[{"role": "system", "content": SYSTEM}] + messages[-MAX_H:],
        )
        return r.choices[0].message.content or "(пустой ответ)"
    except APIError as e:
        return f"⚠️ API ошибка: {str(e)[:200]}"

# ── SQLi детектор (AST, без temp-файлов) ─────────────────────────────────
SQL_RE = re.compile(r"\b(SELECT|INSERT|UPDATE|DELETE|DROP|UNION|WHERE|FROM|INTO)\b", re.I)

def _sql(text: str) -> bool:
    return bool(SQL_RE.search(text))

def _fstr_text(node: ast.JoinedStr) -> str:
    return "".join(v.value if isinstance(v, ast.Constant) else "{}" for v in node.values)

def _binop_text(node: ast.BinOp) -> str:
    parts: list[str] = []
    def _c(n):
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Add):
            _c(n.left); _c(n.right)
        elif isinstance(n, ast.Constant):
            parts.append(str(n.value))
    _c(node); return "".join(parts)

class _V(ast.NodeVisitor):
    def __init__(self, src: list[str]):
        self.src = src; self.findings: list[dict] = []

    def _snip(self, n): return self.src[n.lineno-1].strip() if 0 < n.lineno <= len(self.src) else ""

    def visit_JoinedStr(self, n):
        if _sql(_fstr_text(n)) and any(isinstance(v, ast.FormattedValue) for v in n.values):
            self.findings.append({"line": n.lineno, "rule": "f-строка с SQL", "snip": self._snip(n),
                                   "fix": 'execute("SELECT ... WHERE x=?", (val,))'})
        self.generic_visit(n)

    def visit_BinOp(self, n):
        if isinstance(n.op, ast.Add) and _sql(_binop_text(n)):
            self.findings.append({"line": n.lineno, "rule": "конкатенация + с SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы (?)"})
        elif isinstance(n.op, ast.Mod) and isinstance(n.left, ast.Constant) and _sql(str(n.left.value)):
            self.findings.append({"line": n.lineno, "rule": "% форматирование SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы (?)"})
        self.generic_visit(n)

    def visit_Call(self, n):
        if (isinstance(n.func, ast.Attribute) and n.func.attr == "format"
                and isinstance(n.func.value, ast.Constant) and _sql(str(n.func.value.value))):
            self.findings.append({"line": n.lineno, "rule": ".format() в SQL", "snip": self._snip(n),
                                   "fix": "Используй параметризованные запросы (?)"})
        self.generic_visit(n)

def detect_sqli(code: str) -> list[dict]:
    try:
        tree = ast.parse(code)
    except SyntaxError as e:
        return [{"line": e.lineno or 0, "rule": "Синтаксическая ошибка", "snip": str(e.msg), "fix": ""}]
    v = _V(code.splitlines())
    v.visit(tree)
    seen: set[tuple] = set()
    return [f for f in v.findings if (k := (f["rule"], f["line"])) not in seen and not seen.add(k)]  # type: ignore

def format_sqli(findings: list[dict], code: str) -> str:
    if not findings:
        static = "✅ SQL-инъекций не обнаружено!"
    else:
        lines = [f"🔴 Найдено уязвимостей: {len(findings)}\n"]
        for f in findings:
            lines += [f"*Строка {f['line']}* — {f['rule']}", f"`{f['snip']}`", f"Фикс: {f['fix']}", ""]
        static = "\n".join(lines)

    if not _client:
        return static

    prompt = (f"Уязвимости найдены:\n" +
              "\n".join(f"- строка {f['line']}: {f['rule']}" for f in findings) +
              f"\n\nКод:\n```python\n{code[:2000]}\n```\n\n"
              "Объясни коротко почему опасно и покажи исправленный код.")
    ai = ai_chat([{"role": "user", "content": prompt}])
    return static + "\n\n🧠 *ИИ-объяснение:*\n" + ai

# ── Обработчики Telegram ───────────────────────────────────────────────────
async def cmd_start(u: Update, c: ContextTypes.DEFAULT_TYPE):
    await u.message.reply_text(
        f"👋 Привет, {u.effective_user.first_name}!\n\n"
        f"🧠 ИИ: {LABEL} {'✅' if _client else '❌'}\n\n"
        "• Пиши текст — чат с ИИ\n"
        "• `/sqli <код>` — проверить на SQLi\n"
        "• Пришли `.py` файл — проверю его\n"
        "• `/clear` — сбросить диалог\n"
        "• `/status` — статус",
        parse_mode="Markdown"
    )

async def cmd_status(u: Update, c: ContextTypes.DEFAULT_TYPE):
    await u.message.reply_text(
        f"⚙️ *Статус*\n"
        f"Режим: webhook (Vercel)\n"
        f"Провайдер: `{PROVIDER}` — {LABEL}\n"
        f"Модель: `{MODEL}`\n"
        f"ИИ: {'готов 💚' if _client else 'нет ключа ⚠️'}",
        parse_mode="Markdown"
    )

async def cmd_clear(u: Update, c: ContextTypes.DEFAULT_TYPE):
    _hist.pop(u.effective_user.id, None); _ts.pop(u.effective_user.id, None)
    await u.message.reply_text("🧹 Контекст очищен.")

async def cmd_sqli(u: Update, c: ContextTypes.DEFAULT_TYPE):
    parts = (u.message.text or "").split(" ", 1)
    code  = parts[1] if len(parts) > 1 else (u.message.reply_to_message.text if u.message.reply_to_message else "")
    if not code:
        await u.message.reply_text("Использование: `/sqli <код>`", parse_mode="Markdown"); return
    await u.message.reply_text("🔍 Анализирую…")
    result = format_sqli(detect_sqli(code), code)
    await u.message.reply_text(result[:3900], parse_mode="Markdown")

async def handle_doc(u: Update, c: ContextTypes.DEFAULT_TYPE):
    import tempfile; from pathlib import Path
    doc = u.message.document; fname = (doc.file_name or "").lower()
    if not fname.endswith(".py"):
        await u.message.reply_text("Присылай `.py` файлы для проверки на SQLi.", parse_mode="Markdown"); return
    f = await (await doc.get_file()).download_to_drive(
        tempfile.NamedTemporaryFile(delete=False, suffix=".py").name)
    try:
        code = Path(str(f)).read_text(encoding="utf-8", errors="replace")
        await u.message.reply_text("🔍 Проверяю файл…")
        result = format_sqli(detect_sqli(code), code)
        await u.message.reply_text(result[:3900], parse_mode="Markdown")
    finally:
        Path(str(f)).unlink(missing_ok=True)

async def handle_text(u: Update, c: ContextTypes.DEFAULT_TYPE):
    uid = u.effective_user.id; text = u.message.text
    _push(uid, {"role": "user", "content": text})
    await c.bot.send_chat_action(u.effective_chat.id, "typing")
    reply = ai_chat(list(_get(uid)))
    _push(uid, {"role": "assistant", "content": reply})
    await u.message.reply_text(reply[:3900])

# ── Vercel handler ────────────────────────────────────────────────────────
_app: Optional[Application] = None
_ready = False

async def _get_app() -> Application:
    global _app, _ready
    if not _ready:
        _app = Application.builder().token(TOKEN).updater(None).build()
        _app.add_handler(CommandHandler("start",  cmd_start))
        _app.add_handler(CommandHandler("status", cmd_status))
        _app.add_handler(CommandHandler("clear",  cmd_clear))
        _app.add_handler(CommandHandler("sqli",   cmd_sqli))
        _app.add_handler(MessageHandler(filters.Document.ALL, handle_doc))
        _app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
        await _app.initialize()
        _ready = True
    return _app

async def _process(data: dict):
    app = await _get_app()
    await app.process_update(Update.de_json(data, app.bot))

class handler(BaseHTTPRequestHandler):
    def do_POST(self):
        try:
            body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))))
            asyncio.run(_process(body))
            self._ok(b"ok")
        except Exception as e:
            log.exception("update error"); self._ok(f"err:{e}".encode())

    def do_GET(self):
        self._ok(b"Bot is alive. POST /api/webhook for updates.")

    def _ok(self, body: bytes):
        self.send_response(200); self.send_header("Content-Type", "text/plain"); self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a): pass
