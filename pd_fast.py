"""Fast paths: the owner's everyday asks done in code, with no model turn.

Speed is the owner's biggest complaint, and the limit is the remote backend's ~6 sends a
minute, not the tools. Before this, "put the volume to like 28%" cost a quick
brain send (~5 s), a job process, and two Opus turns (~25 s, 2 sends) for a
0.03 s change. The week of 10/19 had 6 volume jobs, 5 LED-strip jobs (one took
20 sends and changed the mouse instead of the strip), and 6 weather / price /
Hacker News look-ups.

Three levels, cheapest first:
1. `answer(text)`: a text that is plainly one of these commands (word lists,
   not guesses; anything with a word it doesn't know falls through) is done
   right away in the daemon. 0 sends, about a second.
2. The quick brain's "fast" key: typo'd or wordy versions ("sync the lgiths to
   the music") come back as a command like "lights music", run by `run_spec`.
   1 send, no job. If the command fails, the text becomes a normal job.
3. `prefetch_block(dot, relay)`: a job's first look-ups (the quick brain's
   "look" list, or the morning brief's calendar / Canvas / Gradescope / unread
   mail) run before its first send, while the MCP servers start, so the first
   model turn starts with the answers instead of spending a send asking for them.

Nothing here buys, sends, deletes or posts anything: it changes the PC's
sound, the room LED strip (localhost:5330), and reads public weather / price /
Hacker News data and the owner's own mail and calendar (read-only tools).
Every use is logged to fast.jsonl so speed_report can count what it saved.
"""
import io
import json
import os
import re
import sys
import threading
import time
import urllib.parse
from pathlib import Path

DOTS_DIR = Path(os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))
LEDS = os.environ.get("PERIOD_DOT_LEDS", "http://127.0.0.1:5330")
HOME_PLACE = ("remote", 37.4275, -122.1697)  # weather with no place named
ON = os.environ.get("PERIOD_DOT_FAST", "").lower() not in ("off", "0", "no")
MAX_LINES = 3  # a burst of up to this many plain commands is done together


def _log_path():
    return Path(os.environ.get("PERIOD_DOTS_DIR", DOTS_DIR)) / "fast.jsonl"


def _log(**row):
    try:
        path = _log_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(dict(t=round(time.time(), 1), **row), ensure_ascii=False) + "\n")
    except Exception:
        pass


# --- reading the text --------------------------------------------------------

FILLER = {
    "also", "and", "ok", "okay", "yo", "hey", "pls", "plz", "please", "dot", "can", "could", "would",
    "will", "you", "u", "ya", "just", "now", "rn", "right", "so", "thanks", "thx", "ty", "for", "me",
    "quick", "real", "quickly", "asap", "the", "my", "a", "to", "at", "it", "it's", "its", "like",
    "about", "around", "be", "of", "is", "are", "what", "what's", "whats", "how", "how's", "hows",
    "currently", "set", "put", "turn", "make", "change", "switch", "get", "bring", "go", "im", "i'm",
    "i", "want", "need", "too", "them", "they", "their", "it'll", "again", "then", "back", "do",
    "anything", "some", "way", "very", "super", "really", "bro", "bruh", "lol", "ur", "your", "this",
    "that", "there", "up", "down", "?", "all", "way", "%", "percent", "level", "in", "here", "room",
}
NEGATION = {"don't", "dont", "not", "never", "no", "stop", "without", "unless", "don’t"}
_NUM = re.compile(r"^\d{1,3}%?$")

VOLUME_ANCHORS = {"volume", "vol", "sound", "audio", "mute", "unmute", "louder", "quieter", "softer"}
VOLUME_WORDS = VOLUME_ANCHORS | {"up", "down", "max", "maximum", "full", "lower", "raise", "higher",
                                 "by", "pc", "computer", "system", "spotify", "spotify's", "spicetify",
                                 "bit", "lil", "little", "tad", "touch", "slightly", "on", "off", "master",
                                 "laptop"}  # not "speakers"/"headphones": that can mean switching the output
UP_WORDS = {"up", "louder", "raise", "higher"}
DOWN_WORDS = {"down", "lower", "quieter", "softer"}
SMALL_WORDS = {"bit", "lil", "little", "tad", "touch", "slightly"}
SPOTIFY_WORDS = {"spotify", "spotify's", "spicetify"}

LIGHT_ANCHORS = {"lights", "light", "leds", "led", "strip", "lighting"}
EFFECTS = ["flow", "rainbow", "breathe", "candle", "ocean", "sunset", "aurora", "party"]
COLORS = {"red": [255, 0, 0], "orange": [255, 100, 0], "yellow": [255, 200, 0], "green": [0, 255, 0],
          "blue": [0, 0, 255], "purple": [140, 0, 255], "violet": [140, 0, 255], "pink": [255, 40, 150],
          "white": [255, 255, 255], "warm": [255, 140, 60], "cyan": [0, 255, 255], "teal": [0, 200, 160],
          "magenta": [255, 0, 255], "gold": [255, 170, 0]}
NIGHT_LOOK = {"on": True, "mode": "color", "color": [255, 90, 20], "brightness": 12}
LIGHT_WORDS = LIGHT_ANCHORS | set(EFFECTS) | set(COLORS) | {
    "on", "off", "mode", "effect", "color", "colour", "brightness", "bright", "brighter", "dim", "dimmer",
    "dimmed", "music", "sync", "synced", "beat", "beats", "night", "nighttime", "flash", "flashing",
    "kill", "shut", "status", "doing", "state", "showing", "full", "max", "low", "half", "reactive",
    "with", "song", "songs", "spotify", "lit", "set", "by", "colors", "colours", "rgb", "back"}
LIGHT_QUESTION = {"what", "what's", "whats", "how", "how's", "hows", "are", "is", "status", "doing", "state",
                  "showing", "?"}


def _norm(text):
    t = (text or "").lower().replace("’", "'").replace("‘", "'")
    t = re.sub(r"[\"“”*_~`]", "", t)
    return re.sub(r"\s+", " ", t).strip()


def _tokens(line):
    return re.findall(r"\d{1,3}(?:\.\d+)?%?|[a-z][a-z']*|\?", line)


def _volume(words):
    if not VOLUME_ANCHORS & set(words):
        return None
    if any(w not in FILLER and w not in VOLUME_WORDS and not _NUM.match(w) for w in words):
        return None
    if NEGATION & set(words):
        return None
    nums = [int(w.rstrip("%")) for w in words if _NUM.match(w)]
    if len(nums) > 1 or any(n > 100 for n in nums):
        return None
    n = nums[0] if nums else None
    app = "spotify" if SPOTIFY_WORDS & set(words) else ""
    up, down = bool(UP_WORDS & set(words)), bool(DOWN_WORDS & set(words))
    if "unmute" in words:
        return {"do": "volume", "app": app, "unmute": True, "level": n}
    if "mute" in words:
        return None if n is not None or up or down else {"do": "volume", "app": app, "mute": True}
    if up and down:
        return None
    if n is not None:
        if "by" in words and (up or down):
            return {"do": "volume", "app": app, "delta": n if up else -n}
        return {"do": "volume", "app": app, "level": n}
    if up or down:
        step = 5 if SMALL_WORDS & set(words) else 10
        return {"do": "volume", "app": app, "delta": step if up else -step}
    if {"max", "maximum", "full"} & set(words):
        return {"do": "volume", "app": app, "level": 100}
    if {"what", "what's", "whats", "how", "?", "level"} & set(words):
        return {"do": "volume", "app": app, "status": True}
    return None


def _lights(words):
    ws = set(words)
    if not LIGHT_ANCHORS & ws:
        return None
    if any(w not in FILLER and w not in LIGHT_WORDS and w not in NEGATION and not _NUM.match(w) for w in words):
        return None
    if "spotify" in ws and not ({"music", "sync", "synced", "beat", "beats"} & ws):
        return None  # "lights" + spotify without music sync: unclear
    effects = [e for e in EFFECTS if e in ws] + (["party"] if {"flash", "flashing"} & ws and "party" not in ws else [])
    colors = [c for c in COLORS if c in ws]
    if colors == ["warm", "white"] or colors == ["white", "warm"]:
        colors = ["warm"]
    music = bool({"music", "sync", "synced", "beat", "beats", "reactive"} & ws)
    night = bool({"night", "nighttime"} & ws)
    off = bool({"off", "kill", "shut"} & ws)
    nums = [int(w.rstrip("%")) for w in words if _NUM.match(w)]
    acts = len(effects) + len(colors) + music + night
    asked = words[0] in LIGHT_QUESTION or "?" in ws or bool({"status", "doing", "state", "showing"} & ws)
    if NEGATION & ws or (asked and not acts and not nums and not {"dim", "dimmer", "brighter"} & ws):
        # "what are my lights doing, dont change them", "are the lights on?"
        return {"do": "lights", "status": True} if asked else None
    if len(nums) > 1 or any(n > 100 for n in nums) or acts > 1 or len(effects) > 1 or len(colors) > 1:
        return None
    if off:
        return None if acts or nums or "on" in ws else {"do": "lights", "set": {"on": False}}
    look = {"on": True}
    if night:
        look.update(NIGHT_LOOK)
    elif music:
        look["mode"] = "music"
    elif effects:
        look.update(mode="effect", effect=effects[0])
    elif colors:
        look.update(mode="color", color=COLORS[colors[0]])
    bright = None
    if nums:
        bright = max(1, nums[0])
    elif {"full", "max"} & ws and ("bright" in ws or "brightness" in ws or not acts):
        bright = 100
    elif "half" in ws:
        bright = 50
    elif "low" in ws:
        bright = 20
    rel = "dimmer" if {"dim", "dimmer", "dimmed"} & ws else "brighter" if "brighter" in ws else ""
    if bright is not None:
        look["brightness"] = bright
    out = {"do": "lights", "set": look}
    if rel and bright is None and not night:
        out["relative"] = rel
    if len(look) == 1 and not rel and "on" not in ws and "lit" not in ws:
        return None  # nothing to do that it understood
    return out


_LEAD = r"^(?:(?:yo|hey|and|also|ok|okay|so|pls|please|dot|quick|real quick)[ ,]+)*"
_TAIL = r"(?:\s+(?:today|rn|right now|now|outside|too|tho|then|pls|please|again|real quick))*\s*[?.!]*$"
WEATHER_RE = re.compile(
    _LEAD + r"(?:(?:what'?s|whats|what is|how'?s|hows|how is|check|get|tell me|give me|show me)\s+)?(?:the\s+)?"
    r"(?:weather|forecast|temp|temperature)(?:\s+like)?(?:\s+(?:(?:in|at|for|near|of)\s+)?(?P<place>[a-z][a-z .,'-]{1,40}?))?"
    + _TAIL)
_COINS = {"bitcoin": "bitcoin", "btc": "bitcoin", "ethereum": "ethereum", "eth": "ethereum", "solana": "solana",
          "dogecoin": "dogecoin", "doge": "dogecoin", "xrp": "ripple"}
PRICE_RE = re.compile(
    _LEAD + r"(?:(?:what'?s|whats|what is|how much is|how'?s|hows|check|get|price of|price)\s+)?(?:the\s+)?"
    r"(?:price\s+(?:of\s+)?)?(?P<coin>bitcoin|btc|ethereum|eth|solana|dogecoin|doge|xrp)(?:'s)?(?:\s+price)?"
    r"(?:\s+(?:at|trading at|doing|worth|going for|sitting at))?" + _TAIL)
HN_RE = re.compile(
    _LEAD + r"(?:(?:find|get|check|what'?s|whats|what is|show me|send me|tell me)\s+)?(?:the\s+|me\s+the\s+)?"
    r"(?:(?:top|#1|number one|first)\s+(?:post|story|thing|link)\s+on\s+(?:hacker\s*news|hn)|top\s+hn(?:\s+post)?|hn)"
    + _TAIL)
_NOT_PLACE = {"today", "rn", "now", "outside", "here", "right now"}
_FORECAST_WORDS = {"tomorrow", "tonight", "weekend", "later", "next", "this", "week", "going", "gonna", "be",
                   "will", "my", "trip", "should", "when", "if", "like", "on", "during", "for"}
GREETING_RE = re.compile(r"^(?:yo|hey|hi|hello|ok|okay|so|dot|yo dot|hey dot)[!.,? ]*$")


def parse_line(line):
    """One line of their text -> a command dict, or None when it isn't plainly one."""
    t = _norm(line).strip(" ,")
    if not t or len(t) > 120:
        return None
    m = WEATHER_RE.match(t)
    if m:
        place = (m.group("place") or "").strip(" ,.'")
        if place in _NOT_PLACE or place.startswith(("here", "outside")):
            place = ""
        words = place.split()
        if len(words) > 4 or set(words) & _FORECAST_WORDS:
            return None  # a forecast or a question about plans: the quick brain's
        return {"do": "weather", "place": place}
    m = PRICE_RE.match(t)
    if m:
        return {"do": "price", "coin": _COINS[m.group("coin")]}
    if HN_RE.match(t):
        return {"do": "hn"}
    words = _tokens(t)
    if not words or len(words) > 16:
        return None
    return _volume(words) or _lights(words)


def parse(text):
    """Their whole text -> a list of commands, or None unless every part of it is one."""
    if not ON:
        return None
    lines = [l for l in (text or "").strip().splitlines() if l.strip()]
    if not lines or "[they sent a file" in (text or ""):
        return None
    cmds = []
    for line in lines:
        if GREETING_RE.match(_norm(line)):
            continue
        cmd = parse_line(line)
        if cmd is None:
            return None
        cmds.append(cmd)
    return cmds if 0 < len(cmds) <= MAX_LINES else None


# --- doing it ----------------------------------------------------------------

def _http(method, url, body=None, timeout=6):
    # requests (certifi's certificates): urllib's store on this PC has an expired root (10/26).
    import requests
    r = requests.request(method, url, json=body, timeout=timeout,
                         headers={"User-Agent": "Dot/1.0 (personal assistant)"})
    r.raise_for_status()
    return r.json() if r.content else None


class _Speakers:
    """The default output device's master volume (Windows Core Audio through pycaw), about 30 ms."""

    def __init__(self):
        import comtypes
        try:
            comtypes.CoInitialize()
        except OSError:
            pass  # already initialized on this thread
        from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
        dev = AudioUtilities.GetSpeakers()
        ev = getattr(dev, "EndpointVolume", None)
        if ev is None:  # older pycaw
            from ctypes import POINTER, cast
            from comtypes import CLSCTX_ALL
            ev = cast(dev.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None), POINTER(IAudioEndpointVolume))
        self._ev = ev

    def get(self):
        return round(self._ev.GetMasterVolumeLevelScalar() * 100), bool(self._ev.GetMute())

    def set_level(self, pct):
        self._ev.SetMasterVolumeLevelScalar(max(0, min(100, pct)) / 100.0, None)

    def set_mute(self, on):
        self._ev.SetMute(1 if on else 0, None)


class _AppVolume:
    """One app's own volume slider (Spotify), so other apps stay as they are."""

    def __init__(self, exe):
        import comtypes
        try:
            comtypes.CoInitialize()
        except OSError:
            pass
        from pycaw.pycaw import AudioUtilities
        self._vols = [s.SimpleAudioVolume for s in AudioUtilities.GetAllSessions()
                      if s.Process and s.Process.name().lower() == exe.lower()]
        if not self._vols:
            raise LookupError(f"{exe} isn't playing any sound")

    def get(self):
        v = self._vols[0]
        return round(v.GetMasterVolume() * 100), bool(v.GetMute())

    def set_level(self, pct):
        for v in self._vols:
            v.SetMasterVolume(max(0, min(100, pct)) / 100.0, None)

    def set_mute(self, on):
        for v in self._vols:
            v.SetMute(1 if on else 0, None)


def speakers(app=""):
    return _AppVolume("Spotify.exe") if app == "spotify" else _Speakers()


def _own_thread(fn, *args, timeout=10):
    """Run fn on a short-lived thread: COM (Core Audio) set-up never touches the daemon's threads."""
    box = {}

    def go():
        try:
            box["out"] = fn(*args)
        except BaseException as e:
            box["err"] = e
    th = threading.Thread(target=go, daemon=True, name="dot-fast")
    th.start()
    th.join(timeout)
    if th.is_alive():
        raise TimeoutError("took too long")
    if "err" in box:
        raise box["err"]
    return box.get("out")


def do_volume(cmd):
    return _own_thread(_do_volume, cmd)


def _do_volume(cmd):
    dev = speakers(cmd.get("app", ""))
    what = "spotify" if cmd.get("app") == "spotify" else "volume"
    was, muted = dev.get()
    if cmd.get("status"):
        return f"{what}'s at {was}%" + (" but muted" if muted else "")
    if cmd.get("mute"):
        dev.set_mute(True)
        now, m = dev.get()
        if not m:
            raise RuntimeError("mute didn't stick")
        return f"muted ({what} stays at {now}% underneath)"
    target = cmd.get("level")
    if target is None and cmd.get("delta") is not None:
        target = max(0, min(100, was + int(cmd["delta"])))
    if target is not None:
        dev.set_level(int(target))
    unmuted = False
    if muted and (cmd.get("unmute") or target is not None):
        dev.set_mute(False)  # a new level they asked for should be heard
        unmuted = True
    now, m = dev.get()
    if target is not None and abs(now - int(target)) > 1:
        raise RuntimeError(f"asked for {target}%, reads {now}%")
    if cmd.get("unmute") and target is None:
        if m:
            return ""  # still muted: let the slow way look into it
        return f"unmuted, {what}'s at {now}%" if unmuted else f"it wasn't muted, {what}'s at {now}%"
    moved = "" if was == now else f" (was {was}%)"
    return f"{what}'s at {now}% now{moved}" + (", and unmuted" if unmuted else "")


def _light_words(s):
    st = s.get("settings") or {}
    if not st.get("on", True):
        return "off"
    mode = st.get("mode")
    if mode == "music":
        look = "synced to the music"
    elif mode == "effect":
        look = f"on {st.get('effect')}"
    else:
        rgb = st.get("color") or []
        name = next((n for n, c in COLORS.items() if c == rgb), None)
        look = name or ("#%02x%02x%02x" % tuple(rgb) if len(rgb) == 3 else "a solid color")
    return f"{look} at {st.get('brightness', 100)}% brightness"


def do_lights(cmd):
    if cmd.get("status"):
        s = _http("GET", f"{LEDS}/api/state")
        out = f"your lights are {_light_words(s)}"
        if not s.get("connected", True):
            out += " (the strip isn't connected right now, so it's dark)"
        left = int(s.get("sleep_left") or 0)
        if left:
            out += f", turning off in {max(1, left // 60)} min"
        return out
    body = dict(cmd["set"])
    if cmd.get("relative"):
        cur = int(((_http("GET", f"{LEDS}/api/state").get("settings")) or {}).get("brightness") or 100)
        body["brightness"] = max(5, cur // 2) if cmd["relative"] == "dimmer" else min(100, cur + 30)
    s = _http("POST", f"{LEDS}/api/set", body)
    st = s.get("settings") or {}
    for k, v in body.items():
        if st.get(k) != v:
            raise RuntimeError(f"lights didn't take {k}")
    if body.get("on") is False:
        out = "lights off"
    elif body == NIGHT_LOOK:
        out = "lights are a dim warm orange for the night"
    else:
        out = f"lights are {_light_words(s)} now"
    if not s.get("connected", True):
        out += ", but the strip isn't connected right now so you won't see it yet"
    return out


_WMO = {0: "clear", 1: "mostly clear", 2: "partly cloudy", 3: "overcast", 45: "foggy", 48: "foggy",
        51: "light drizzle", 53: "drizzle", 55: "heavy drizzle", 56: "freezing drizzle", 57: "freezing drizzle",
        61: "light rain", 63: "rain", 65: "heavy rain", 66: "freezing rain", 67: "freezing rain",
        71: "light snow", 73: "snow", 75: "heavy snow", 77: "snow grains", 80: "light showers",
        81: "showers", 82: "heavy showers", 85: "snow showers", 86: "heavy snow showers",
        95: "thunderstorms", 96: "thunderstorms with hail", 99: "thunderstorms with hail"}


def do_weather(cmd):
    place = cmd.get("place") or ""
    if place:
        q = urllib.parse.quote(place.split(",")[0].strip())
        g = _http("GET", f"https://geocoding-api.open-meteo.com/v1/search?name={q}&count=1&language=en&format=json")
        hits = (g or {}).get("results") or []
        if not hits:
            raise LookupError(f"no place called {place}")
        h = hits[0]
        where = [h.get("name") or place] + [x for x in (h.get("admin1"), h.get("country")) if x and x != h.get("name")]
        name, lat, lon = ", ".join(where[:2]), h["latitude"], h["longitude"]
    else:
        name, lat, lon = HOME_PLACE
    w = _http("GET", "https://api.open-meteo.com/v1/forecast?" + urllib.parse.urlencode({
        "latitude": lat, "longitude": lon, "timezone": "auto", "temperature_unit": "fahrenheit",
        "wind_speed_unit": "mph", "forecast_days": 1,
        "current": "temperature_2m,apparent_temperature,weather_code,wind_speed_10m",
        "daily": "temperature_2m_max,temperature_2m_min,precipitation_probability_max"}))
    cur, day = w["current"], w.get("daily") or {}
    f = round(cur["temperature_2m"])
    c = round((cur["temperature_2m"] - 32) * 5 / 9)
    out = (f"{name.lower()} right now: {f}°F ({c}°C), feels like {round(cur['apparent_temperature'])}°F, "
           f"{_WMO.get(int(cur.get('weather_code') or 0), 'mixed')}, wind {round(cur.get('wind_speed_10m') or 0)} mph")
    try:
        hi, lo = round(day["temperature_2m_max"][0]), round(day["temperature_2m_min"][0])
        rain = day.get("precipitation_probability_max", [None])[0]
        out += f". today {lo}-{hi}°F" + (f", {rain}% chance of rain" if rain and rain >= 10 else "")
    except (KeyError, IndexError, TypeError):
        pass
    return out


def do_price(cmd):
    coin = cmd["coin"]
    p = _http("GET", "https://api.coingecko.com/api/v3/simple/price?" + urllib.parse.urlencode(
        {"ids": coin, "vs_currencies": "usd", "include_24hr_change": "true"}))[coin]
    usd, ch = p["usd"], p.get("usd_24h_change")
    money = f"${usd:,.0f}" if usd >= 100 else f"${usd:,.4g}"
    name = {"ripple": "xrp"}.get(coin, coin)
    trend = "" if ch is None else " (about flat over the last 24h)" if abs(ch) < 0.05 else         f" ({'up' if ch > 0 else 'down'} {abs(ch):.1f}% in the last 24h)"
    return f"{name}'s at {money}{trend}"


def do_hn(_cmd):
    ids = _http("GET", "https://hacker-news.firebaseio.com/v0/topstories.json") or []
    if not ids:
        raise LookupError("no stories")
    it = _http("GET", f"https://hacker-news.firebaseio.com/v0/item/{ids[0]}.json")
    link = f"https://news.ycombinator.com/item?id={it['id']}"
    out = f"top on hacker news right now: \"{it.get('title', '')}\" ({it.get('score', 0)} points, " \
          f"{it.get('descendants', 0)} comments)"
    return out + (f"\n{it['url']}\ncomments: {link}" if it.get("url") else f"\n{link}")


DOERS = {"volume": do_volume, "lights": do_lights, "weather": do_weather, "price": do_price, "hn": do_hn}


def run(cmds, via="text", text=""):
    """Do every command; returns the reply, or None if any of them failed (the
    caller then does it the slow way, so nothing they asked for is dropped)."""
    out, t0 = [], time.time()
    for cmd in cmds:
        try:
            said = DOERS[cmd["do"]](cmd)
        except Exception as e:
            _log(via=via, cmds=cmds, ok=False, err=str(e)[:200], sec=round(time.time() - t0, 2), text=text[:120])
            print(f"[fast] {cmd.get('do')}: {e}", file=sys.stderr)
            return None
        if not said:
            _log(via=via, cmds=cmds, ok=False, err="nothing to say", sec=round(time.time() - t0, 2))
            return None
        out.append(said)
    _log(via=via, cmds=cmds, ok=True, sec=round(time.time() - t0, 2), text=text[:120])
    return "\n".join(out)


def answer(text):
    """The reply for a text that's plainly an everyday command, done already; else None."""
    cmds = parse(text)
    if cmds:
        return run(cmds, "text", text)
    return autotool_answer(text)


def autotool_answer(text):
    """A kept speed-reflex script (pd_autotool, e.g. "when are my interviews due?" from the mail index) answers
    the whole text; None when none does, or it can't right now (stale index), so the normal way answers."""
    if not ON or not text or "[they sent a file" in text:
        return None
    t0 = time.time()
    try:
        import pd_autotool
        out, name = pd_autotool.fast_answer(text)
    except Exception as e:
        print(f"[fast] autotool: {e}", file=sys.stderr)
        return None
    if out:
        _log(via="autotool", cmds=[{"do": name}], ok=True, sec=round(time.time() - t0, 2), text=text[:120])
    return out or None


def run_spec(spec, text=""):
    """The quick brain's "fast" command ("volume 28", "lights music", "weather tokyo"), done; else None."""
    specs = spec if isinstance(spec, list) else [spec]
    cmds = []
    for one in specs[:MAX_LINES]:
        cmd = parse_line(str(one or ""))
        if cmd is None:
            _log(via="brain", spec=str(one)[:80], ok=False, err="not a command", text=text[:120])
            return None
        cmds.append(cmd)
    return run(cmds, "brain", text) if cmds else None


# --- look-ups done before a job's first send ---------------------------------

LOOK_TOOLS = {"mail": "mail_search", "email": "mail_search", "calendar": "calendar_list",
              "canvas": "canvas_upcoming", "gradescope": "gradescope_assignments",
              "web": "web_search", "search": "web_search", "page": "web_fetch", "url": "web_fetch"}
MAX_LOOKS = 3
SIDE_ALWAYS = {"mail_search", "calendar_list"}  # read-only; run on side threads with the web look-ups
# A job about deadlines / interviews / what's due also gets the mail index's deadline digest (pd_index).
DEADLINE_RE = re.compile(r"\b(due|deadline|interview|assessment|oa|coding (test|challenge)|what do i (have|need) "
                         r"to do|whats? due|offer|recruit\w*|application status|hear back)\b", re.I)
DIGEST_CHARS = 3500
PER_RESULT = 3500
TOTAL = 10000  # input tokens barely move latency; a missing result costs a whole send
BRIEF_CALLS = [
    ("calendar_list", {"days": 1, "desc": "Checking what's on today"}),
    ("canvas_upcoming", {"days": 3, "desc": "Checking what's due in the next few days"}),
    ("gradescope_assignments", {"days": 7, "desc": "Checking Gradescope deadlines"}),
    ("mail_search", {"query": "in:inbox is:unread newer_than:1d", "count": 25, "desc": "Looking for new unread emails"}),
]


def look_calls(looks):
    """The quick brain's "look" list -> [(tool, args)]: 'mail: from:capitalone', 'calendar: 7',
    'canvas', 'web: cs 101 midterm room', 'page: https://...'."""
    if isinstance(looks, str):
        looks = [looks]
    calls = []
    for item in (looks or [])[:MAX_LOOKS]:
        kind, _, arg = str(item or "").partition(":")
        kind, arg = kind.strip().lower(), arg.strip()
        tool = LOOK_TOOLS.get(kind)
        if tool == "mail_search" and arg:
            calls.append((tool, {"query": arg, "count": 25, "desc": "Searching your email"}))
        elif tool == "calendar_list":
            days = int(re.sub(r"\D", "", arg) or 7)
            calls.append((tool, {"days": max(1, min(31, days)), "desc": "Looking at your calendar"}))
        elif tool == "canvas_upcoming":
            calls.append((tool, {"days": 7, "desc": "Checking what's due"}))
        elif tool == "gradescope_assignments":
            calls.append((tool, {"days": 14, "desc": "Checking Gradescope"}))
        elif tool == "web_search" and arg:
            calls.append((tool, {"query": arg, "desc": "Searching the web"}))
        elif tool == "web_fetch" and arg.startswith(("http://", "https://")):
            calls.append(("web_fetch", {"url": arg, "desc": "Reading the page"}))
    return calls


def _call_tool(s, name, args, quiet=False):
    fn = getattr(s, "TOOL_MAP", {}).get(name)
    if fn is None:
        return None
    quiet = quiet and hasattr(s, "_console_override")
    if quiet:  # a side thread: its prints would interleave with the job's log
        from rich.console import Console
        s._console_override.console = Console(file=io.StringIO())
    try:
        out = fn(dict(args))
        if name in ("calendar_list", "mail_search") and "rejected by callee" in str(out):
            time.sleep(1.5)  # Outlook was busy (seen at 8:00 on 10/23): one quiet retry
            out = fn(dict(args))
        return out
    except Exception as e:
        return f"Error: {e}"
    finally:
        if quiet:
            s._console_override.console = None


def run_calls(s, calls, gate=None):
    """[(tool, args)] -> [(tool, args, result)], skipping any the job's gate refuses.
    All of them run side by side, mail and calendar included (2026-11-05: a mail search
    and the calendar one after the other cost their sum; each tool opens its own Outlook
    COM connection on its own thread, and a busy Outlook gets one quiet retry)."""
    allowed = []
    for name, args in calls:
        if gate is not None:
            try:
                if gate(name, args):
                    continue
            except Exception:
                continue
        if name in getattr(s, "OUTSIDE_TOOLS", ()) and getattr(s, "remote_only", lambda: False)():
            continue
        allowed.append((name, args))
    side = (set(getattr(s, "PARALLEL_SAFE_TOOLS", ())) & {"web_search", "web_fetch", "canvas_upcoming",
                                                           "gradescope_assignments"}) | SIDE_ALWAYS
    results, threads = {}, []
    for i, (name, args) in enumerate(allowed):
        if name in side:
            th = threading.Thread(target=lambda i=i, n=name, a=args: results.__setitem__(i, _call_tool(s, n, a, True)),
                                  daemon=True, name="dot-prefetch")
            th.start()
            threads.append(th)
    for i, (name, args) in enumerate(allowed):
        if name not in side:
            results[i] = _call_tool(s, name, args)
    deadline = time.time() + 90
    for th in threads:
        th.join(max(0.0, deadline - time.time()))
    return [(name, args, results.get(i)) for i, (name, args) in enumerate(allowed) if results.get(i) is not None]


def prefetch_block(dot, relay=None, s=None, first=True):
    """Text to add to a job's prompt with its first look-ups already done, or ""."""
    if not ON:
        return ""
    idx = _index()
    if idx is not None:
        try:  # the mail index's hidden sync process (pd_index): started if it isn't running, never waited on
            idx.ensure_running()
        except Exception:
            pass
    brief = getattr(dot, "kind", "") == "brief"
    calls = BRIEF_CALLS if brief else (look_calls(getattr(dot, "look", None)) if first else [])
    about = " ".join(str(x) for x in [getattr(dot, "goal", "")] + list(getattr(dot, "look", None) or [])
                     if isinstance(x, str))
    want_digest = first and not brief and idx is not None and bool(DEADLINE_RE.search(about))
    scripted = []
    if first:
        try:  # kept speed-reflex scripts whose ask is part of this job ("...and when are my interviews due")
            import pd_autotool
            scripted = pd_autotool.prefetch(getattr(dot, "goal", "") or "")
        except Exception as e:
            print(f"[fast] autotool prefetch: {e}", file=sys.stderr)
    if not calls and not want_digest and not scripted:
        return ""
    if s is None:
        import period as s
    t0 = time.time()
    gate = getattr(relay, "gate", None)
    served, live, hits, age = _from_index(idx, s, calls, gate)
    digest = None
    if want_digest:
        try:
            digest = idx.deadline_digest(limit_chars=DIGEST_CHARS, s=s)
        except Exception:
            digest = None
        if digest and age is None:
            age = _index_age(idx, s)
    done = run_calls(s, live, gate=gate) if live else []
    if served:  # back in the order they were asked for
        order = {id(a): i for i, (_n, a) in enumerate(calls)}
        done = sorted(served + done, key=lambda d: order.get(id(d[1]), 99))
    if not done and not digest and not scripted:
        return ""
    if brief:
        head = (f"[Time for the morning brief ({time.strftime('%A %b %d')}). Everything it needs was fetched just "
                "now, below. Write it straight from this: don't call calendar_list, canvas_upcoming, "
                "gradescope_assignments or mail_search again. Open an email (mail_read) only when its line here "
                "isn't enough to tell whether it needs them.]")
    else:
        head = ("[ALREADY LOOKED UP FOR YOU just now, before you started. Use these instead of running the same "
                "searches again; look further only if they don't have what you need. If these already answer what they asked, answer in this first reply; when you do need more, ask for every look-up you need in one reply, not one per reply.]")
    digest_part = ""
    if digest:
        digest_part = "▸ deadlines (from Dot's mail index)\n" + str(digest).strip()[:DIGEST_CHARS]
    parts, used = [head], len(digest_part)  # the digest is counted inside TOTAL first, so it's never cut off
    for name, args, result in done:
        shown = {k: v for k, v in args.items() if k != "desc"}
        text = str(result).strip()
        text = text[:PER_RESULT] + (" …(cut)" if len(text) > PER_RESULT else "")
        if used + len(text) > TOTAL:
            text = text[:max(0, TOTAL - used)] + " …(cut)"
        used += len(text)
        parts.append(f"▸ {name} {json.dumps(shown, ensure_ascii=False)}\n{text}")
        if relay is not None:
            try:
                relay.evidence.append(f"{name}({json.dumps(shown)[:300]}) -> {text[:500]}")
            except Exception:
                pass
    if digest_part:
        parts.append(digest_part)
        if relay is not None:
            try:
                relay.evidence.append(f"deadline_digest(mail index) -> {digest_part[:500]}")
            except Exception:
                pass
    for name, said in scripted:
        parts.append(f"▸ {name} (Dot's own script over the mail index and calendar, checked against past answers; "
                     f"use it as the answer for this part, open an email only for what it doesn't say)\n"
                     f"{str(said).strip()[:PER_RESULT]}")
        if relay is not None:
            try:
                relay.evidence.append(f"{name}(autotool) -> {str(said)[:500]}")
            except Exception:
                pass
    _log(via="prefetch", job=getattr(dot, "id", ""), kind=getattr(dot, "kind", ""), ok=True,
         tools=[n for n, _a, _r in done] + (["deadlines"] if digest_part else []) + [n for n, _s in scripted],
         sec=round(time.time() - t0, 2), index_hits=hits, index_age_s=age)
    return "\n" + "\n\n".join(parts) + "\n"


def _index():
    """pd_index, or None if it can't be imported (then everything runs live, as before it existed)."""
    try:
        import pd_index
        return pd_index
    except Exception:
        return None


def _index_age(idx, s):
    try:
        return idx.mail_age_s(s)
    except Exception:
        return None


def _from_index(idx, s, calls, gate):
    """Serve mail_search / calendar_list from the mail index when it's fresh and has the answer.
    -> (served [(tool, args, result)], still to run live [(tool, args)], index_hits, index_age_s).
    Any error, a stale index, or a query it can't translate: that call runs live, exactly as before."""
    if idx is None:
        return [], list(calls), 0, None
    served, live, hits, age = [], [], 0, None
    for name, args in calls:
        result = None
        try:
            if name == "mail_search":
                result = idx.search(args.get("query", ""), args.get("count", 25), s=s)
                if result is not None:
                    hits += int(getattr(idx, "last_hits", [0])[0] or 0)
                    age = getattr(idx, "last_hits", [0, None])[1]
            elif name == "calendar_list":
                result = idx.agenda(args.get("days", 7), s=s)
        except Exception:
            result = None
        if result is None:
            live.append((name, args))
            continue
        if gate is not None:  # the job's gate still decides, as for a live call
            try:
                if gate(name, args):
                    continue
            except Exception:
                continue
        served.append((name, args, result))
    return served, live, hits, age


def stats(days=7, now=None):
    """What the fast paths did lately: hits by route, failures, and the sends / time they saved."""
    now = time.time() if now is None else now
    try:
        rows = [json.loads(l) for l in _log_path().read_text(encoding="utf-8").splitlines() if l.strip()]
    except (OSError, ValueError):
        rows = []
    rows = [r for r in rows if isinstance(r, dict) and r.get("t", 0) >= now - days * 86400]
    hits = {"text": 0, "brain": 0, "prefetch": 0}
    fails = 0
    for r in rows:
        if r.get("ok"):
            hits[r.get("via", "text")] = hits.get(r.get("via", "text"), 0) + 1
        else:
            fails += 1
    # Measured on 10/25: a volume/lights job was 1 quick-brain send + 2-3 job sends, ~30 s
    # from text to answer. Text route: all of it. Brain route: the job (2 sends, ~25 s).
    # Prefetch: the first job turn spent asking for the look-ups (1 send, ~12 s).
    sends = hits["text"] * 3 + hits["brain"] * 2 + hits["prefetch"]
    secs = hits["text"] * 28 + hits["brain"] * 25 + hits["prefetch"] * 12
    return {"days": days, "hits": hits, "failed": fails, "sends_saved": sends, "seconds_saved": secs}
