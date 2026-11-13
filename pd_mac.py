"""Dot works on a Mac through its helper (mac/dot_mac_agent.py), over Tailscale.

Owner 2026-11-11: Dot should be usable from his MacBook and able to control it; a friend with only a MacBook should
get their own Dot (the same helper is that Dot's hands on its own Mac). The helper only checks a token; every action
here goes through pd_policy first (pd_policy.needs_human -> policy() below): drastic shell commands, sending messages
or mail, and anything that spends money wait for the owner's OK, as on the PC.

  python pd_mac.py pair HOST TOKEN [--name "My MacBook"]   store the helper's address + token (keyring)
  python pd_mac.py status                                           is the Mac reachable?
  python pd_mac.py unpair

Tools (registered into period.TOOL_MAP by register(); the guide goes into the system prompt when paired):
  mac_run {command, timeout}   mac_applescript {script}   mac_screenshot {}   mac_click {x, y, double}
  mac_type {text}   mac_key {key}   mac_open {target, app}   mac_files {op: list|read|write|stat, path, ...}
"""
import base64
import json
import re
import sys
import tempfile
import time
from pathlib import Path

import requests

CONF = Path.home() / ".period_dots" / "mac.json"
KEYRING = ("Period", "mac:token")
SHOTS = Path(tempfile.gettempdir()) / "dot_mac_shots"
_ping = {"t": 0.0, "ok": False}


def _conf():
    try:
        return json.loads(CONF.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def _token():
    try:
        import keyring
        return keyring.get_password(*KEYRING)
    except Exception:
        return None


def call(action, args=None, timeout=130):
    c, tok = _conf(), _token()
    if not c or not tok:
        raise RuntimeError("no Mac is paired with this Dot (python pd_mac.py pair HOST TOKEN)")
    r = requests.post(f"http://{c['host']}:{c.get('port', 8790)}/{action}", json=args or {},
                      headers={"Authorization": f"Bearer {tok}"}, timeout=timeout)
    if r.status_code == 401:
        raise RuntimeError("the Mac helper refused the token: pair again")
    return r.json()


def ready(max_age=60):
    """Paired and answering (cached): the guide and tools only show up when the Mac is reachable."""
    if not _conf():
        return False
    if time.time() - _ping["t"] < max_age:
        return _ping["ok"]
    try:
        ok = bool(call("ping", timeout=4).get("ok"))
    except Exception:
        ok = False
    _ping.update(t=time.time(), ok=ok)
    return ok


def name():
    return (_conf() or {}).get("name") or "the Mac"


# --- policy (called from pd_policy.needs_human for every mac_* tool) -------------------------------------------------

SEND_RX = re.compile(r'tell application "(Messages|Mail|Microsoft Outlook)"[\s\S]*\b(send|make new outgoing message)\b|'
                     r"\bimessage\b.*\bsend\b|\bsend\s+(message|email|mail)\b", re.I)


def policy(tool, args):
    """Why this Mac action needs the owner's OK, or None."""
    import pd_policy
    blob = json.dumps(args or {}, ensure_ascii=False)
    if tool == "mac_run":
        cmd = str((args or {}).get("command") or "")
        crazy = pd_policy.crazy_command(cmd, in_vm=False)  # his real Mac: same bar as his PC
        if crazy:
            return crazy
        if re.search(r"\bosascript\b", cmd) and SEND_RX.search(cmd):
            return "it sends a message or email from the Mac"
        return pd_policy.money_reason(blob, "") if hasattr(pd_policy, "money_reason") else None
    if tool == "mac_applescript":
        if SEND_RX.search(str((args or {}).get("script") or "")):
            return "it sends a message or email from the Mac"
        return pd_policy.money_reason(blob, "")
    if tool in ("mac_click", "mac_type", "mac_key", "mac_open"):
        return pd_policy.money_reason(blob, "")
    if tool == "mac_files" and (args or {}).get("op") == "write":
        p = str((args or {}).get("path") or "")
        if re.search(r"(^|/)(Library/LaunchAgents|\.ssh|\.zshrc|\.bash_profile|/etc/)", p):
            return "it changes the Mac's startup or security files"
    return None


# --- tools --------------------------------------------------------------------------------------------------------

def _say(args, tool):
    try:
        import period as s
        s.console.print(f"  [white]{s.safe_markup(args.get('desc') or tool.replace('_', ' '))}[/white]")
    except Exception:
        pass


def _err(e):
    return f"Error: {e}"


def tool_mac_run(args):
    _say(args, "Running a command on the Mac")
    try:
        r = call("run", {"command": args.get("command", ""), "timeout": args.get("timeout", 120)},
                 timeout=int(args.get("timeout", 120)) + 15)
    except Exception as e:
        return _err(e)
    if r.get("error"):
        return _err(r["error"])
    out = (r.get("stdout") or "") + (("\n[stderr]\n" + r["stderr"]) if r.get("stderr") else "")
    return f"exit {r.get('code')}\n{out[-12000:]}"


def tool_mac_applescript(args):
    _say(args, "Running AppleScript on the Mac")
    try:
        r = call("applescript", {"script": args.get("script", "")})
    except Exception as e:
        return _err(e)
    return _err(r["error"]) if r.get("error") else f"exit {r.get('code')}\n{(r.get('stdout') or '')[-8000:]}" + (
        f"\n[stderr] {r['stderr'][-2000:]}" if r.get("stderr") else "")


def tool_mac_screenshot(args):
    _say(args, "Looking at the Mac's screen")
    try:
        r = call("screenshot", timeout=40)
    except Exception as e:
        return _err(e)
    if not r.get("png_b64"):
        return _err(r.get("error") or "no image")
    SHOTS.mkdir(exist_ok=True)
    p = SHOTS / f"mac_{int(time.time() * 1000)}.png"
    p.write_bytes(base64.b64decode(r["png_b64"]))
    try:
        import period as s
        s._pending_local_images.append(str(p))
    except Exception:
        pass
    return f"Captured {name()}'s screen; it is attached to your next message ({p.name})."


def _simple(action, label):
    def fn(args):
        _say(args, label)
        try:
            r = call(action, {k: v for k, v in args.items() if k != "desc"})
        except Exception as e:
            return _err(e)
        if r.get("error"):
            return _err(r["error"])
        if r.get("code") not in (None, 0):
            return _err((r.get("stderr") or r.get("stdout") or f"exit {r.get('code')}")[-500:])
        return "done"
    return fn


def tool_mac_files(args):
    _say(args, "Working with files on the Mac")
    try:
        r = call("files", {k: v for k, v in args.items() if k != "desc"})
    except Exception as e:
        return _err(e)
    if r.get("error"):
        return _err(r["error"])
    if "b64" in r:
        data = base64.b64decode(r["b64"])
        try:
            return data.decode("utf-8")[:20000] + ("" if r.get("size", 0) <= len(data) else "\n…(cut)")
        except UnicodeDecodeError:
            return f"(binary file, {r.get('size')} bytes)"
    return json.dumps(r, ensure_ascii=False)[:20000]


MAC_TOOLS = {
    "mac_run": tool_mac_run, "mac_applescript": tool_mac_applescript, "mac_screenshot": tool_mac_screenshot,
    "mac_click": _simple("click", "Clicking on the Mac"), "mac_type": _simple("type", "Typing on the Mac"),
    "mac_key": _simple("key", "Pressing keys on the Mac"), "mac_open": _simple("open", "Opening on the Mac"),
    "mac_files": tool_mac_files,
}

GUIDE = """
The owner's Mac ({name}): you can work on it through mac_* tools (it must be awake; if a call errors with a
connection failure, say the Mac is asleep or offline instead of retrying in a loop).
- mac_run {{"command": "ls ~/Desktop", "timeout": 60}}: a zsh command as the owner's user (Homebrew, git, python...).
- mac_applescript {{"script": "tell application \\"Spotify\\" to playpause"}}: control apps (Finder, Safari, Music,
  Spotify, Calendar, Notes, System Events). Sending Messages/Mail needs the owner's OK like anywhere else.
- mac_screenshot {{}}: see the screen (attached to your next message). mac_click {{"x": 100, "y": 200}} uses screen
  points from that picture; mac_type {{"text": "hi"}}; mac_key {{"key": "cmd+space"}} / {{"key": "enter"}}.
- mac_open {{"target": "https://..."}} or {{"target": "Safari", "app": true}}.
- mac_files {{"op": "list"|"read"|"stat", "path": "~/Documents"}}; {{"op": "write", "path": ..., "b64": ...}}.
Prefer mac_run / mac_applescript over clicking: they're faster and exact. This is the owner's own computer: don't
delete or move his files unless he asked.
"""


def guide():
    return GUIDE.format(name=name())


def register(s):
    """Called by period at import: adds the tools (they error politely when no Mac is paired)."""
    s.TOOL_MAP.update(MAC_TOOLS)
    try:
        s.CONFIG_TOKEN_TOOLS.add("mac_screenshot")
    except Exception:
        pass


# --- CLI ------------------------------------------------------------------------------------------------------------

def pair(host, token, label=None):
    import keyring
    keyring.set_password(*KEYRING, token)
    CONF.parent.mkdir(parents=True, exist_ok=True)
    CONF.write_text(json.dumps({"host": host, "port": 8790, "name": label or "the owner's Mac"}), encoding="utf-8")
    _ping["t"] = 0
    return call("ping", timeout=8)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["pair"] and len(a) >= 3:
        lab = a[a.index("--name") + 1] if "--name" in a else None
        print(json.dumps(pair(a[1], a[2], lab)))
    elif a[:1] == ["status"]:
        print("paired:", _conf(), "| reachable:", ready(0))
    elif a[:1] == ["unpair"]:
        CONF.unlink(missing_ok=True)
        try:
            import keyring
            keyring.delete_password(*KEYRING)
        except Exception:
            pass
        print("unpaired")
    else:
        print(__doc__)
