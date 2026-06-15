from http.server import BaseHTTPRequestHandler
import json, os, urllib.request

class handler(BaseHTTPRequestHandler):
    def do_GET(self):
        token = os.environ.get("TG_BOT_TOKEN", "")
        if not token:
            return self._j(400, {"error": "TG_BOT_TOKEN не задан"})
        host = self.headers.get("X-Forwarded-Host") or self.headers.get("Host", "")
        url  = f"https://{host}/api/webhook"
        req  = urllib.request.Request(
            f"https://api.telegram.org/bot{token}/setWebhook",
            data=json.dumps({"url": url, "allowed_updates": ["message"]}).encode(),
            headers={"Content-Type": "application/json"}, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=10) as r:
                res = json.loads(r.read())
        except Exception as e:
            return self._j(500, {"error": str(e)})
        self._j(200 if res.get("ok") else 400,
                {"webhook": url, "telegram": res})

    def _j(self, code, data):
        body = json.dumps(data, ensure_ascii=False, indent=2).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.end_headers(); self.wfile.write(body)

    def log_message(self, *a): pass
