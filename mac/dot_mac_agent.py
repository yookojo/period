#!/usr/bin/env python3
"""Dot's helper on a Mac: lets a Dot (on the owner's PC, or a Dot running on this Mac) work on this Mac.

Owner 2026-11-11: "i also want it so it can be accessible on my macbook too, and it can control my macbook as well",
and a friend with only a MacBook should get their own Dot. This small service is the Mac's hands: run a shell
command, run AppleScript, screenshot, click/type/press keys, open apps or links, read/write files.

Security:
- Listens on the Tailscale address only (100.x.y.z) or 127.0.0.1, never on Wi-Fi/LAN interfaces.
- Every request needs the token in ~/.dot_mac/token (made at install, chmod 600) as "Authorization: Bearer <token>".
- It has no policy of its own beyond that: the Dot calling it runs every action through pd_policy first (money,
  sending messages and drastic commands wait for the owner's OK).
- Logs every action (not its output) to ~/.dot_mac/agent.log.

macOS asks once for Screen Recording (screenshots) and Accessibility (clicks/keys) for the Python running this.

  python3 dot_mac_agent.py serve [--host 100.x.y.z] [--port 8790]
  python3 dot_mac_agent.py info          the address + token to pair with (pd_mac.py pair ...)
Python 3.9+, standard library only (clicks use cliclick if installed, else pyautogui if installed, else AppleScript).
"""
import base64
import hmac
import json
import os
import shutil
import socket
import subprocess
import sys
import tempfile
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HOME = Path.home() / ".dot_mac"
TOKEN = HOME / "token"
LOG = HOME / "agent.log"
PORT = 8790
MAX_OUT = 200_000
VERSION = "1"


def log(msg):
    HOME.mkdir(exist_ok=True)
    with open(LOG, "a", encoding="utf-8") as f:
        f.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg[:300].replace("\n", " ") + "\n")


def token():
    HOME.mkdir(exist_ok=True)
    if not TOKEN.exists():
        import secrets
        TOKEN.write_text(secrets.token_urlsafe(32), encoding="utf-8")
        os.chmod(TOKEN, 0o600)
    return TOKEN.read_text(encoding="utf-8").strip()


def tailscale_ip():
    for exe in ("tailscale", "/Applications/Tailscale.app/Contents/MacOS/Tailscale", "/usr/local/bin/tailscale",
                "/opt/homebrew/bin/tailscale"):
        try:
            out = subprocess.run([exe, "ip", "-4"], capture_output=True, text=True, timeout=5).stdout.strip()
            if out.startswith("100."):
                return out.splitlines()[0]
        except (OSError, subprocess.SubprocessError):
            continue
    return None


def _run(argv, timeout=120, stdin=None):
    r = subprocess.run(argv, capture_output=True, text=True, timeout=timeout, input=stdin)
    return {"code": r.returncode, "stdout": r.stdout[-MAX_OUT:], "stderr": r.stderr[-20_000:]}


# --- actions --------------------------------------------------------------------------------------------------------

def a_ping(a):
    return {"ok": True, "version": VERSION, "host": socket.gethostname(), "user": os.environ.get("USER"),
            "mac": sys.platform == "darwin"}


def a_run(a):
    cmd = str(a.get("command") or "")
    return _run(["/bin/zsh", "-lc", cmd], timeout=min(int(a.get("timeout") or 120), 1800))


def a_applescript(a):
    return _run(["/usr/bin/osascript", "-e", str(a.get("script") or "")], timeout=min(int(a.get("timeout") or 60), 600))


def a_screenshot(a):
    fd, p = tempfile.mkstemp(suffix=".png")
    os.close(fd)
    try:
        r = _run(["/usr/sbin/screencapture", "-x", "-t", "png", p], timeout=30)
        if r["code"] != 0 or not os.path.getsize(p):
            return {"error": "screenshot failed (grant Screen Recording to this Python in System Settings > Privacy)",
                    **r}
        return {"png_b64": base64.b64encode(Path(p).read_bytes()).decode()}
    finally:
        os.unlink(p)


def _click_tool():
    return shutil.which("cliclick")


def a_click(a):
    x, y = int(a["x"]), int(a["y"])
    double = bool(a.get("double"))
    if _click_tool():
        return _run([_click_tool(), ("dc:" if double else "c:") + f"{x},{y}"], timeout=15)
    try:
        import pyautogui
        pyautogui.click(x, y, clicks=2 if double else 1)
        return {"code": 0}
    except ImportError:
        return {"error": "install cliclick (brew install cliclick) or pyautogui to click"}


def _esc(s):
    return str(s).replace("\\", "\\\\").replace('"', '\\"')


def a_type(a):
    return _run(["/usr/bin/osascript", "-e", f'tell application "System Events" to keystroke "{_esc(a.get("text", ""))}"'],
                timeout=60)


KEYCODES = {"enter": 36, "return": 36, "tab": 48, "space": 49, "delete": 51, "backspace": 51, "escape": 53, "esc": 53,
            "left": 123, "right": 124, "down": 125, "up": 126}


def a_key(a):
    """{"key": "cmd+shift+4"} or {"key": "enter"}."""
    parts = [p.strip().lower() for p in str(a.get("key") or "").split("+") if p.strip()]
    mods = [m for m in parts if m in ("cmd", "command", "shift", "option", "alt", "ctrl", "control")]
    keys = [k for k in parts if k not in mods]
    names = {"cmd": "command down", "command": "command down", "shift": "shift down", "option": "option down",
             "alt": "option down", "ctrl": "control down", "control": "control down"}
    using = (" using {" + ", ".join(names[m] for m in mods) + "}") if mods else ""
    if not keys:
        return {"error": "no key"}
    k = keys[0]
    body = f"key code {KEYCODES[k]}" if k in KEYCODES else f'keystroke "{_esc(k)}"'
    return _run(["/usr/bin/osascript", "-e", f'tell application "System Events" to {body}{using}'], timeout=15)


def a_open(a):
    t = str(a.get("target") or "")
    argv = ["/usr/bin/open", "-a", t] if a.get("app") else ["/usr/bin/open", t]
    return _run(argv, timeout=30)


def a_files(a):
    op, p = a.get("op"), Path(os.path.expanduser(str(a.get("path") or "~")))
    if op == "list":
        return {"entries": sorted(((e.name + ("/" if e.is_dir() else "")) for e in p.iterdir()), key=str.lower)[:2000]}
    if op == "read":
        data = p.read_bytes()[: int(a.get("max_bytes") or 2_000_000)]
        return {"b64": base64.b64encode(data).decode(), "size": p.stat().st_size}
    if op == "write":
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(base64.b64decode(a.get("b64") or ""))
        return {"ok": True, "size": p.stat().st_size}
    if op == "stat":
        st = p.stat()
        return {"size": st.st_size, "mtime": st.st_mtime, "dir": p.is_dir()}
    return {"error": f"unknown op {op}"}


ACTIONS = {"ping": a_ping, "run": a_run, "applescript": a_applescript, "screenshot": a_screenshot, "click": a_click,
           "type": a_type, "key": a_key, "open": a_open, "files": a_files}


class Handler(BaseHTTPRequestHandler):
    server_version = "DotMac/" + VERSION

    def log_message(self, *a):
        pass

    def _send(self, code, obj):
        data = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_POST(self):
        auth = self.headers.get("Authorization", "")
        if not hmac.compare_digest(auth.encode(), f"Bearer {self.server.token}".encode()):
            log(f"refused (bad token) from {self.client_address[0]}")
            return self._send(401, {"error": "bad token"})
        name = self.path.strip("/").split("?")[0]
        fn = ACTIONS.get(name)
        if not fn:
            return self._send(404, {"error": f"no action {name}"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            args = json.loads(self.rfile.read(n) or b"{}") if n else {}
            log(f"{name} {json.dumps({k: v for k, v in args.items() if k != 'b64'})[:200]}")
            return self._send(200, fn(args))
        except subprocess.TimeoutExpired:
            return self._send(200, {"error": "timed out"})
        except Exception as e:
            return self._send(200, {"error": f"{e.__class__.__name__}: {e}"})


def serve(host=None, port=PORT):
    host = host or tailscale_ip() or "127.0.0.1"
    if not (host.startswith("100.") or host in ("127.0.0.1", "localhost")):
        raise SystemExit("refusing to listen outside Tailscale/localhost: " + host)
    srv = ThreadingHTTPServer((host, port), Handler)
    srv.token = token()
    log(f"serving on {host}:{port}")
    print(f"Dot Mac helper on http://{host}:{port}", flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a or a[0] == "serve":
        h = a[a.index("--host") + 1] if "--host" in a else None
        p = int(a[a.index("--port") + 1]) if "--port" in a else PORT
        serve(h, p)
    elif a[0] == "info":
        print(json.dumps({"host": tailscale_ip() or "127.0.0.1", "port": PORT, "token": token()}))
    else:
        print(__doc__)
