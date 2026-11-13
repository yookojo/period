"""Dot on Discord, the lively parts: screenshots, a live screen while it works,
replays, buttons, slash commands, reactions, voice messages and remote control.

pd_dots.py owns the conversation; this module only talks to Discord and the
screens. Everything here is best effort: a failure is logged, never raised into
a job.
"""
import io
import json
import re
import sys
import threading
import time
import urllib.parse
from collections import deque
from pathlib import Path

LIVE_EVERY_SEC = 6          # how often the live screen message gets a new picture
QUIET_UPDATE_SEC = 20       # a progress text goes out if Dot has said nothing for this long
GRID_COLS, GRID_ROWS = 20, 12
SLASH_VERSION = 4           # bump to re-register the slash commands

PC_TOOLS = ("computer_", "app_do", "app_read", "app_windows", "tab_", "save_screenshot")
VM_TOOLS = ("vm_open", "vm_read", "vm_screenshot", "vm_click", "vm_type", "vm_key", "vm_scroll", "vm_start",
            "vm_fill")


def _d():
    import pd_dots
    return pd_dots


def _api(method, path, **kw):
    return _d().sc()._discord(method, path, **kw)


def _log(where, e):
    print(f"[{where}] {str(e)[:200]}", file=sys.stderr)


def channel_of(chat):
    """'discord:<id>' -> '<id>', anything else -> None."""
    chat = chat or ""
    if chat.startswith("discord:"):
        return chat.split(":", 1)[1]
    if chat == "discord":
        return _d().discord.dm()
    return None


# --- messages ---------------------------------------------------------------------

def buttons(*rows):
    """rows of (label, custom_id, style) -> Discord components. style: 1 blue, 2 grey, 3 green, 4 red."""
    out = []
    for row in rows:
        out.append({"type": 1, "components": [
            {"type": 2, "label": label[:80], "custom_id": cid[:100], "style": style}
            for label, cid, style in row][:5]})
    return out[:5]


def _multipart(payload, files):
    handles, up = [], {}
    payload = dict(payload)
    payload["attachments"] = []
    for i, f in enumerate(list(files)[:10]):
        if isinstance(f, tuple):  # (name, bytes)
            name, data = f
            up[f"files[{i}]"] = (name, io.BytesIO(data))
        else:
            h = open(f, "rb")
            handles.append(h)
            name = Path(f).name
            up[f"files[{i}]"] = (name, h)
        payload["attachments"].append({"id": i, "filename": name})
    return {"data": {"payload_json": json.dumps(payload)}, "files": up}, handles


def post(channel, content="", files=(), components=None, gated=False):
    """Send a message. files: paths or (name, bytes). Returns its id or None.
    To the owner's DM it goes through pd_dots._gate_discord first (gated=True: the caller already did)."""
    if not gated and channel and channel == _d().discord.dm():
        content = _d()._gate_discord(content, files, components)
        if content is None:
            return None
    payload = {"content": (content or "")[:1990]}
    if components is not None:
        payload["components"] = components
    try:
        if files:
            kw, handles = _multipart(payload, files)
            try:
                return (_api("POST", f"/channels/{channel}/messages", **kw) or {}).get("id")
            finally:
                for h in handles:
                    h.close()
        if not payload["content"] and not components:
            return None
        return (_api("POST", f"/channels/{channel}/messages", json=payload) or {}).get("id")
    except Exception as e:
        _log("post", e)
        return None


def edit(channel, msg_id, content=None, files=None, components=None):
    payload = {}
    if content is not None:
        payload["content"] = content[:1990]
    if components is not None:
        payload["components"] = components
    try:
        if files is not None:
            kw, handles = _multipart(payload, files)
            try:
                _api("PATCH", f"/channels/{channel}/messages/{msg_id}", **kw)
            finally:
                for h in handles:
                    h.close()
        else:
            _api("PATCH", f"/channels/{channel}/messages/{msg_id}", json=payload)
        return True
    except Exception as e:
        _log("edit", e)
        return False


def delete(channel, msg_id):
    try:
        _api("DELETE", f"/channels/{channel}/messages/{msg_id}")
    except Exception as e:
        _log("delete", e)


def react(channel, msg_id, emoji, on=True):
    if not channel or not msg_id:
        return
    try:
        _api("PUT" if on else "DELETE",
             f"/channels/{channel}/messages/{msg_id}/reactions/{urllib.parse.quote(emoji)}/@me")
    except Exception as e:
        _log("react", e)


# --- screens -----------------------------------------------------------------------

def grab(which):
    """A PIL image of 'pc' (their screen) or 'vm' (Dot's computer), or None."""
    from PIL import Image
    try:
        if which == "vm":
            import pd_vm
            return Image.open(io.BytesIO(pd_vm.DotPC.screenshot_png())).convert("RGB")
        return _d().sc()._grab_screen_image()
    except Exception as e:
        _log("screenshot", e)
        return None


def jpeg(img, max_edge=1600, quality=70):
    img = img.copy()
    img.thumbnail((max_edge, max_edge))
    buf = io.BytesIO()
    img.save(buf, "JPEG", quality=quality)
    return buf.getvalue()


def send_screenshot(chat, which="pc", caption=None):
    channel = channel_of(chat)
    img = grab(which)
    if img is None:
        msg = ("couldn't get a picture of my computer, it might be off. say \"start your pc\" and try again"
               if which == "vm" else "couldn't grab your screen just now (is the PC locked?)")
        if channel:
            post(channel, msg)
        else:
            _d().send_to(chat, msg)
        return False
    name = f"{'dot-pc' if which == 'vm' else 'your-screen'}-{time.strftime('%H%M%S')}.jpg"
    if channel:
        post(channel, caption if caption is not None else "", files=[(name, jpeg(img))])
    else:  # iMessage: the picture itself, as an attachment
        _d().send_to(chat, caption or "", files=[_d()._save_outgoing(name, jpeg(img))])
    return True


# --- the live card: one message with the screen, refreshed while a job runs --------

class LiveCard:
    """Watches which screen a job is using and keeps one message showing it, with
    a Stop button. Also keeps the frames for "show me how you did that"."""

    def __init__(self, dot):
        self.dot = dot
        self.channel = channel_of(dot.reply_to)
        self.screen = None
        self.status = ""
        self.msg = None
        self.frames = deque(maxlen=90)
        self.started = time.time()
        self.last_tool_at = 0.0
        self._stop = threading.Event()
        self._thread = None
        self._lock = threading.Lock()
        if self.channel:
            threading.Thread(target=self._watch_for_live, daemon=True, name="dot-live-ask").start()

    def enabled(self):
        # A background job (the application lane) posted a fresh screen card for every run: 103 in 3 days
        # (2026-11-09). Its screen only streams when he asks to watch ("live", which sets dot.live).
        if _d()._quiet_background(self.dot) and not getattr(_d().load_dot(self.dot.id) or self.dot, "live", False):
            return False
        return bool(self.channel) and _d().settings().get("live_screen", True)

    def _start(self):
        with self._lock:
            if self._thread is None and not self._stop.is_set():
                self._thread = threading.Thread(target=self._loop, daemon=True, name="dot-live")
                self._thread.start()

    def _watch_for_live(self):
        """They asked to watch ("give me live feed"): stream now, even before a screen is used."""
        while not self._stop.wait(2):
            fresh = _d().load_dot(self.dot.id)
            if fresh is not None and fresh.live:
                if self.screen is None:
                    self.screen = "pc" if _d().computer_mode() == "pc" else "vm"
                self._start()
                return

    def tool(self, name, args):
        """Called before each tool runs."""
        self.last_tool_at = time.time()
        try:
            desc = (args or {}).get("desc") or _d().sc().infer_action_description(name, args or {})
        except Exception:
            desc = ""
        self.status = str(desc or "")[:150]
        which = "vm" if name.startswith(VM_TOOLS) else ("pc" if name.startswith(PC_TOOLS) else None)
        if which and which != self.screen:
            self.screen = which
            if self.enabled():
                self._start()

    def _caption(self, final=False):
        where = "my computer" if self.screen == "vm" else "your screen"
        if final:
            return f"that's {where} where I left it"
        return f"🔴 live on {where}" + (f" · {self.status.lower()}" if self.status else "")

    def _snap(self):
        img = grab(self.screen)
        if img is None:
            return None
        small = img.copy()
        small.thumbnail((720, 720))
        self.frames.append(small)
        return img

    def _loop(self):
        stop_btn = buttons([("Stop", f"stop:{self.dot.id}", 4), ("Replay so far", f"replay:{self.dot.id}", 2)])
        while not self._stop.is_set():
            img = self._snap()
            if img is not None:
                f = [(f"live-{int(time.time() * 1000)}.jpg", jpeg(img, 1280, 60))]
                if self.msg is None:
                    self.msg = post(self.channel, self._caption(), files=f, components=stop_btn)
                else:
                    edit(self.channel, self.msg, content=self._caption(), files=f, components=stop_btn)
            self._stop.wait(LIVE_EVERY_SEC)

    def finish(self):
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=LIVE_EVERY_SEC + 30)
        if self.screen:
            img = self._snap()
            if self.msg and img is not None:
                edit(self.channel, self.msg, content=self._caption(final=True),
                     files=[("final.jpg", jpeg(img, 1280, 70))],
                     components=buttons([("Replay", f"replay:{self.dot.id}", 2)]))
        self.save_frames()

    def save_frames(self):
        if len(self.frames) < 2:
            return
        folder = self.dot.folder / "replay"
        folder.mkdir(parents=True, exist_ok=True)
        for old in folder.glob("*.jpg"):
            old.unlink(missing_ok=True)
        for i, fr in enumerate(self.frames):
            fr.save(folder / f"{i:03d}.jpg", "JPEG", quality=70)


_cards = {}  # dot id -> LiveCard of the run in progress


def make_replay(dot_id):
    """A GIF of the last job's screen, or None."""
    from PIL import Image
    card = _cards.get(dot_id)
    frames = list(card.frames) if card else []
    if len(frames) < 2:
        d = _d().load_dot(dot_id)
        if d:
            frames = [Image.open(p).convert("RGB") for p in sorted((d.folder / "replay").glob("*.jpg"))]
    if len(frames) < 2:
        return None
    step = max(1, len(frames) // 40)
    frames = [f.copy() for f in frames[::step]]
    for f in frames:
        f.thumbnail((640, 640))
    buf = io.BytesIO()
    frames[0].save(buf, "GIF", save_all=True, append_images=frames[1:], duration=700, loop=0, optimize=True)
    return buf.getvalue()


def send_replay(chat, dot_id=None):
    channel = channel_of(chat)
    if dot_id is None:
        mine = [d for d in _d().all_dots() if d.reply_to == chat and
                ((d.folder / "replay").exists() or d.id in _cards)]
        dot_id = max(mine, key=lambda d: d.updated).id if mine else None
    gif = make_replay(dot_id) if dot_id else None
    if not channel:  # iMessage: the GIF as an attachment
        if gif is None:
            return _d().send_to(chat, "I don't have a replay yet. it records when I'm using a screen")
        return _d().send_to(chat, "here's how it went", files=[_d()._save_outgoing("replay.gif", gif)])
    if gif is None:
        post(channel, "I don't have a replay yet. it records when I'm using a screen")
    else:
        post(channel, "here's how it went", files=[("replay.gif", gif)])


# --- remote control by text ----------------------------------------------------------

_control = {}  # chat -> {"which", "msg", "w", "h"}
_COL_LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[:GRID_COLS]


def _grid(img):
    from PIL import ImageDraw, ImageFont
    img = img.copy()
    w, h = img.size
    draw = ImageDraw.Draw(img, "RGBA")
    cw, ch = w / GRID_COLS, h / GRID_ROWS
    try:
        font = ImageFont.truetype("arialbd.ttf", max(12, int(min(cw, ch) / 4)))
    except Exception:
        font = ImageFont.load_default()
    for c in range(1, GRID_COLS):
        draw.line([(c * cw, 0), (c * cw, h)], fill=(255, 0, 80, 110), width=1)
    for r in range(1, GRID_ROWS):
        draw.line([(0, r * ch), (w, r * ch)], fill=(255, 0, 80, 110), width=1)
    for c in range(GRID_COLS):
        for r in range(GRID_ROWS):
            label = f"{_COL_LETTERS[c]}{r + 1}"
            x, y = c * cw + 3, r * ch + 2
            draw.rectangle([x - 1, y - 1, x + len(label) * font.size * 0.62, y + font.size + 1], fill=(0, 0, 0, 120))
            draw.text((x, y), label, fill=(255, 255, 255, 230), font=font)
    return img


CONTROL_BUTTONS = buttons(
    [("⬆️ Scroll", "ctl:scrollup", 2), ("⬇️ Scroll", "ctl:scrolldown", 2), ("⏎ Enter", "ctl:enter", 2),
     ("⎋ Esc", "ctl:esc", 2), ("🔄", "ctl:refresh", 2)],
    [("⇥ Alt+Tab", "ctl:alttab", 2), ("⌫", "ctl:backspace", 2), ("Done", "ctl:done", 4)])


def control_start(chat, which="pc"):
    _control[chat] = {"which": which, "msg": None, "w": 0, "h": 0}
    control_show(chat, intro=True)


def control_show(chat, intro=False):
    st = _control.get(chat)
    channel = channel_of(chat)
    if not st or not channel:
        return
    img = grab(st["which"])
    if img is None:
        post(channel, "can't see that screen right now")
        return
    st["w"], st["h"] = img.size
    caption = ("you're driving 🕹️ say a square to click it (\"C4\", \"double C4\", \"right C4\"), "
               "\"type hello\", \"press ctrl+l\", \"scroll down\", or tell me what to do in words. "
               "\"done\" when you're finished" if intro else "")
    if st["msg"]:
        delete(channel, st["msg"])
    st["msg"] = post(channel, caption, files=[("screen.jpg", jpeg(_grid(img), 1600, 72))],
                     components=CONTROL_BUTTONS)


_CELL = r"([a-%s])\s*(\d{1,2})" % _COL_LETTERS[-1].lower()


def control_handle(chat, text):
    """A text while they're driving. True if it was a control command."""
    st = _control.get(chat)
    if not st:
        return False
    t = text.strip().lower()
    if t in ("done", "exit", "stop", "quit", "stop control", "i'm done", "im done"):
        _control.pop(chat, None)
        post(channel_of(chat), "ok, hands off 👋")
        return True
    m = re.fullmatch(r"(?:(double|dbl|right)\s*(?:click)?\s*|click\s+)?" + _CELL, t)
    try:
        if m:
            col = _COL_LETTERS.lower().index(m.group(2))
            row = int(m.group(3)) - 1
            if not 0 <= row < GRID_ROWS:
                return False
            x = int((col + 0.5) * st["w"] / GRID_COLS)
            y = int((row + 0.5) * st["h"] / GRID_ROWS)
            _do(st["which"], "click", x=x, y=y, kind=m.group(1) or "")
        elif t.startswith("type "):
            _do(st["which"], "type", text=text.strip()[5:])
        elif t.startswith("press "):
            _do(st["which"], "key", keys=t[6:].strip())
        elif re.fullmatch(r"scroll\s+(up|down)(\s+\d+)?", t):
            parts = t.split()
            _do(st["which"], "scroll", amount=(int(parts[2]) if len(parts) > 2 else 5) * (1 if parts[1] == "down" else -1))
        elif t in ("refresh", "again", "screen"):
            pass
        else:
            return False
    except Exception as e:
        post(channel_of(chat), f"that didn't work: {str(e)[:150]}")
    time.sleep(0.8)
    control_show(chat)
    return True


def control_button(chat, action):
    keys = {"enter": "enter", "esc": "esc", "alttab": "alt+tab", "backspace": "backspace"}
    if action == "done":
        return control_handle(chat, "done")
    st = _control.get(chat)
    if not st:
        return False
    if action in keys:
        _do(st["which"], "key", keys=keys[action])
    elif action in ("scrollup", "scrolldown"):
        _do(st["which"], "scroll", amount=5 if action == "scrolldown" else -5)
    time.sleep(0.6)
    control_show(chat)
    return True


_VM_KEYS = {"enter": "Return", "esc": "Escape", "backspace": "BackSpace", "tab": "Tab", "alt+tab": "alt+Tab"}


def _do(which, action, x=0, y=0, kind="", text="", keys="", amount=0):
    if which == "vm":
        import pd_vm
        pc = pd_vm.DotPC
        if action == "click":
            pc.click(x, y, button="right" if kind == "right" else "left", double=kind in ("double", "dbl"))
        elif action == "type":
            pc.type_text(text)
        elif action == "key":
            pc.key(" ".join(_VM_KEYS.get(k, k) for k in keys.split()))
        elif action == "scroll":
            pc.scroll(x or 640, y or 400, amount)
        return
    pg = _d().sc()._get_pyautogui()
    if action == "click":
        if kind in ("double", "dbl"):
            pg.doubleClick(x, y)
        else:
            pg.click(x, y, button="right" if kind == "right" else "left")
    elif action == "type":
        pg.write(text, interval=0.01)
    elif action == "key":
        for combo in keys.split():
            pg.hotkey(*[k.strip() for k in combo.split("+")])
    elif action == "scroll":
        pg.scroll(-amount * 120)


# --- voice messages ------------------------------------------------------------------

AUDIO_EXT = (".ogg", ".oga", ".opus", ".mp3", ".m4a", ".wav", ".webm", ".aac", ".flac", ".caf")  # .caf: iMessage voice
_whisper = [None]
_whisper_lock = threading.Lock()


def is_audio(path):
    return str(path).lower().endswith(AUDIO_EXT)


def warm_up_voice():
    """Load the speech model ahead of the first voice message (first run downloads it)."""
    try:
        with _whisper_lock:
            if _whisper[0] is None:
                from faster_whisper import WhisperModel
                _whisper[0] = WhisperModel("small.en", device="cpu", compute_type="int8")
    except Exception as e:
        _log("voice", e)


def _decode(path):
    """16 kHz mono samples via ffmpeg (faster-whisper's own decoder breaks on newer PyAV)."""
    import subprocess
    import numpy as np
    out = subprocess.run(["ffmpeg", "-nostdin", "-loglevel", "error", "-i", str(path), "-f", "f32le",
                          "-ac", "1", "-ar", "16000", "-"], capture_output=True, timeout=120,
                         creationflags=0x08000000 if sys.platform == "win32" else 0)
    if out.returncode != 0:
        raise RuntimeError(out.stderr.decode(errors="replace")[-200:])
    return np.frombuffer(out.stdout, dtype=np.float32)


def transcribe(path):
    """Speech in an audio file -> text ('' if nothing was heard)."""
    audio = _decode(path)
    with _whisper_lock:
        if _whisper[0] is None:
            from faster_whisper import WhisperModel
            _whisper[0] = WhisperModel("small.en", device="cpu", compute_type="int8")
        segments, _info = _whisper[0].transcribe(audio, beam_size=3, vad_filter=True)
        return " ".join(s.text.strip() for s in segments).strip()


# --- slash commands and button clicks --------------------------------------------------

SLASH_COMMANDS = [
    {"name": "screen", "description": "See a screen right now",
     "options": [{"type": 3, "name": "which", "description": "whose screen", "required": False,
                  "choices": [{"name": "my PC", "value": "pc"}, {"name": "Dot's computer", "value": "vm"}]}]},
    {"name": "status", "description": "What Dot is doing right now"},
    {"name": "stop", "description": "Stop everything Dot is doing"},
    {"name": "replay", "description": "A GIF of how the last job went"},
    {"name": "control", "description": "Drive a screen yourself by tapping squares",
     "options": [{"type": 3, "name": "which", "description": "whose screen", "required": False,
                  "choices": [{"name": "my PC", "value": "pc"}, {"name": "Dot's computer", "value": "vm"}]}]},
    {"name": "brief", "description": "Your brief right now: schedule, deadlines, email"},
    {"name": "inbox", "description": "Anything important in your email?"},
    {"name": "notify", "description": "Turn Dot's heads-ups on or off",
     "options": [{"type": 3, "name": "what", "description": "which heads-ups", "required": True,
                  "choices": [{"name": "important emails", "value": "inbox"},
                              {"name": "texts (iMessage)", "value": "texts"},
                              {"name": "deadlines", "value": "deadlines"},
                              {"name": "morning brief", "value": "brief"},
                              {"name": "live screen while working", "value": "live_screen"}]},
                 {"type": 5, "name": "on", "description": "on or off", "required": True}]},
    {"name": "computer", "description": "Which computer Dot may use",
     "options": [{"type": 3, "name": "use", "description": "where Dot works", "required": True,
                  "choices": [{"name": "only Dot's own computer (I'm using mine)", "value": "vm"},
                              {"name": "my PC", "value": "pc"},
                              {"name": "whichever fits", "value": "auto"}]}]},
]
for _c in SLASH_COMMANDS:
    _c.update(type=1, integration_types=[0], contexts=[0, 1])


def app_id():
    st = _d().settings()
    if st.get("app_id"):
        return st["app_id"]
    aid = (_api("GET", "/oauth2/applications/@me") or {}).get("id")
    if aid:
        st = _d().settings()
        st["app_id"] = aid
        _d().save_settings(st)
    return aid


def register_commands():
    st = _d().settings()
    if st.get("slash_version") == SLASH_VERSION:
        return
    try:
        _api("PUT", f"/applications/{app_id()}/commands", json=SLASH_COMMANDS)
        st = _d().settings()
        st["slash_version"] = SLASH_VERSION
        _d().save_settings(st)
    except Exception as e:
        _log("slash commands", e)


def _respond(i, kind, content=None, components=None, flags=None, modal=None):
    data = {}
    if content is not None:
        data["content"] = content[:1990]
    if components is not None:
        data["components"] = components
    if flags:
        data["flags"] = flags
    body = {"type": kind}
    if modal is not None:
        body["data"] = modal
    elif data:
        body["data"] = data
    try:
        _api("POST", f"/interactions/{i['id']}/{i['token']}/callback", json=body)
    except Exception as e:
        _log("interaction", e)


def _followup(i, content="", files=()):
    path = f"/webhooks/{app_id()}/{i['token']}"
    try:
        if files:
            kw, handles = _multipart({"content": content}, files)
            try:
                _api("POST", path, **kw)
            finally:
                for h in handles:
                    h.close()
        else:
            _api("POST", path, json={"content": content or "👍"})
    except Exception as e:
        _log("followup", e)


def on_interaction(i):
    """A slash command, button click or form from the user's DM."""
    d = _d()
    user = (i.get("user") or (i.get("member") or {}).get("user") or {})
    if user.get("id") != d.settings().get("discord_user"):
        return _respond(i, 4, "sorry, I only work for my person", flags=64)
    d.owner_tapped()
    chat = "discord:" + (i.get("channel_id") or d.discord.dm())
    kind = i.get("type")
    data = i.get("data") or {}
    try:
        if kind == 2:
            return _slash(i, chat, data.get("name"), {o["name"]: o.get("value") for o in data.get("options") or []})
        if kind == 3:
            return _button(i, chat, data.get("custom_id") or "")
        if kind == 5:
            return _modal(i, chat, data)
    except Exception as e:
        _log("interaction", e)
        _respond(i, 4, "hmm, that didn't work on my end")


def _slash(i, chat, name, opts):
    d = _d()
    if name == "screen":
        _respond(i, 5)
        img = grab(opts.get("which") or "pc")
        if img is None:
            return _followup(i, "couldn't get that screen right now")
        return _followup(i, "", files=[("screen.jpg", jpeg(img))])
    if name == "replay":
        _respond(i, 5)
        mine = [x for x in d.all_dots() if (x.folder / "replay").exists() or x.id in _cards]
        gif = make_replay(max(mine, key=lambda x: x.updated).id) if mine else None
        return _followup(i, "here's how it went" if gif else "no replay yet, it records when I use a screen",
                         files=[("replay.gif", gif)] if gif else ())
    if name == "control":
        _respond(i, 4, "taking a look…")
        threading.Thread(target=control_start, args=(chat, opts.get("which") or "pc"), daemon=True).start()
        return
    if name == "status":
        return _respond(i, 4, d.status_text(chat))
    if name == "stop":
        return _respond(i, 4, d.stop_all(chat))
    if name == "notify":
        what, on = opts.get("what"), bool(opts.get("on"))
        d.set_notify(what, on)
        label = {"inbox": "important emails", "texts": "your texts", "deadlines": "deadline nudges",
                 "brief": "the morning brief", "live_screen": "the live screen"}.get(what, what)
        return _respond(i, 4, f"{label}: {'on 👍' if on else 'off'}")
    if name == "computer":
        return _respond(i, 4, d.set_computer_mode(opts.get("use") or "auto") or "hm, didn't get that")
    if name in ("brief", "inbox"):
        _respond(i, 4, "pulling it together, gimme a sec" if name == "brief" else "checking your email…")
        text = "give me my brief right now" if name == "brief" else "anything important in my email?"
        d.enqueue("discord", chat, text)
        return
    _respond(i, 4, "I don't know that one yet")


def _button(i, chat, cid):
    d = _d()
    kind, _, rest = cid.partition(":")
    content = (i.get("message") or {}).get("content", "")
    if kind == "ok":  # yes/no on a held action: ok:<job>:<y|n>[:<question id>]
        dot_id, ans, qid = (rest.split(":") + ["", ""])[:3]
        dot = d.load_dot(dot_id)
        if not dot or dot.asking != "ok" or (qid and dot.qid and qid != dot.qid):
            # A button from an older question (or one already answered) never answers a newer one.
            return _respond(i, 7, content + "\n→ that one's old, it isn't waiting on this anymore", components=[])
        dot.add_message("you", "yes" if ans == "y" else "no")
        d._update(dot, answer="yes" if ans == "y" else "no")
        return _respond(i, 7, content + ("\n→ going ahead ✅" if ans == "y" else "\n→ skipped that ❌"), components=[])
    if kind == "ans":  # Yes/No on a job's question: ans:<job>:<question id>:<text>
        dot_id, qid, text = (rest.split(":", 2) + ["", ""])[:3]
        dot = d.load_dot(dot_id)
        if not dot or dot.status != "waiting" or dot.asking != "question" or qid != dot.qid:
            return _respond(i, 7, content + "\n→ that one's old, it isn't waiting on this anymore", components=[])
        _respond(i, 7, content + f"\n→ {text}", components=[])
        dot.add_message("you", text)
        dot.push_followup(text)
        d._update(dot, status="queued", question=None, asking="", answer=None, next_run=d._now(),
                  runs_this_goal=0, wait_wakes=0)
        d._wake.set()
        return
    if kind == "say":  # a quick reply button: same as texting it
        dot_id, _, text = rest.partition(":")
        _respond(i, 7, components=[])
        d.enqueue("discord", chat, text)
        return
    if kind == "more":  # keep going on a job that checked in, maybe a different way
        dot_id, _, how = rest.partition(":")
        dot = d.load_dot(dot_id)
        _respond(i, 7, components=[])
        if not dot or dot.status == "working":
            return
        if dot.status == "stopped":  # a stopped job is never brought back by an old button
            return d.send_to(chat, "that one's stopped. tell me if you want it started again")
        dot.push_followup("That approach wasn't working. Try a different way." if how == "other"
                          else "Keep going and finish it.")
        d._update(dot, force=True, status="queued", next_run=d._now(), question=None, asking="",
                  answer=None, runs_this_goal=0)
        return d.send_to(chat, "on it 👍")
    if kind == "stop":
        dot = d.load_dot(rest)
        if dot and dot.status in d.ACTIVE:
            d.kill_task(dot.id)
        _respond(i, 7, components=[])
        return d.send_to(chat, "ok, stopped")
    if kind == "replay":
        _respond(i, 5)
        gif = make_replay(rest)
        return _followup(i, "here's how it went" if gif else "not enough to show yet",
                         files=[("replay.gif", gif)] if gif else ())
    if kind == "ctl":
        _respond(i, 6)
        threading.Thread(target=control_button, args=(chat, rest), daemon=True).start()
        return
    if kind in ("mail", "text", "due"):
        import pd_dotwatch
        return pd_dotwatch.on_button(i, chat, kind, rest)
    _respond(i, 6)


def _modal(i, chat, data):
    import pd_dotwatch
    return pd_dotwatch.on_modal(i, chat, data)
