"""Dot gets faster at things it has done before.

While a job runs, every screen step (clicks, typing, screenshots, page reads on
the Dot PC, the user's PC or their Chrome tabs) is timed and filed under where
it happened: a web page (site + path) or a Windows app. When one place eats
too many steps or minutes, the next tool result carries a speed check telling
the model to stop poking and find a faster way, and to write it down as a
LEARNED: line. Those lines go to lessons.md like any other lesson.

The next time a job lands on that site or app, the lessons about it ride along
on that first tool result, right when they're useful, instead of hoping they
were in the last 3000 characters of the prompt. Slow spots that never got a
lesson are remembered too (speed.jsonl), so the next visit starts by looking
for the faster way.
"""
import json
import re
import sys
import time
from pathlib import Path
from urllib.parse import urlparse

DOTS_DIR = Path.home() / ".period_dots"
SPEED_LOG = DOTS_DIR / "speed.jsonl"
TELEMETRY_LOG = Path.home() / ".period_telemetry" / "requests.jsonl"

SLOW_STEPS = 8        # this many screen steps in one place = slow
SLOW_SEC = 120        # or this long, once it's taken at least SLOW_MIN_STEPS
SLOW_MIN_STEPS = 4
HINT_LESSONS = 6      # lessons shown when it arrives somewhere it's been before
SEND_GAP = 1.5        # a gap this long between tool calls means the model took another turn (a send)
GAP_CAP = 20          # thinking time counted per gap, at most (longer is waiting, not working)
SITE_KEEP = 3         # newest lessons kept per site in a job's prompt (older ones are usually superseded)

NOT_SCREEN = {"vm_run", "vm_files", "vm_start", "vm_claude", "save_screenshot", "tab_list"}
# Web hosts' generic parts, which say nothing about the site.
_GENERIC = {"www", "com", "org", "net", "io", "co", "edu", "gov", "app", "ai", "us", "uk",
            "boards", "job-boards", "jobs", "apply", "careers", "m", "en", "login", "auth", "accounts"}
_GENERIC |= {"remote"}  # the user's school: in every other lesson, says nothing about the site
_ALIASES = {"mail.google.com": "gmail", "docs.google.com": "google docs", "drive.google.com": "google drive",
            "calendar.google.com": "google calendar", "open.spotify.com": "spotify"}
# Job-board hosts are filed under the board, whatever company subdomain they carry
# (remote.wd1.myworkdayjobs.com -> workday).
_HOST_SUFFIX = {"ashbyhq.com": "ashby", "myworkdayjobs.com": "workday", "myworkday.com": "workday",
                "greenhouse.io": "greenhouse", "lever.co": "lever", "smartrecruiters.com": "smartrecruiters",
                "linkedin.com": "linkedin", "workable.com": "workable", "icims.com": "icims"}
_STOP = {"the", "and", "for", "with", "that", "this", "from", "your", "their", "them", "they", "what",
         "when", "into", "then", "just", "make", "find", "help", "please", "want", "need", "user",
         "user's", "about", "some", "every", "have", "will", "like", "keep", "going"}
_URL_IN = re.compile(r"https?://[^\s)'\"<>]+")
# Where a result says it is: "Opened https://..." at the start, or "Now on https://...".
_RESULT_URL = re.compile(r"^\s*Opened\s+(https?://[^\s)'\"<>]+)|(?:^|[.!]\s+|\n)Now on\s+(https?://[^\s)'\"<>]+)")


def is_screen_tool(name):
    return name not in NOT_SCREEN and name.startswith(("computer_", "vm_", "tab_", "browser_", "app_",
                                                        "mcp_windows_"))


def _foreground_app():
    """The exe name of the window in front on Windows ("Spotify"), or ""."""
    if sys.platform != "win32":
        return ""
    try:
        import ctypes
        from ctypes import wintypes
        user32, k32 = ctypes.windll.user32, ctypes.windll.kernel32
        pid = wintypes.DWORD()
        user32.GetWindowThreadProcessId(user32.GetForegroundWindow(), ctypes.byref(pid))
        h = k32.OpenProcess(0x1000, False, pid.value)  # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return ""
        try:
            buf, size = ctypes.create_unicode_buffer(520), wintypes.DWORD(520)
            if k32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(size)):
                return Path(buf.value).stem
        finally:
            k32.CloseHandle(h)
    except Exception:
        pass
    return ""


def site_words(where):
    """What lessons about a place would mention: "job-boards.greenhouse.io/x" -> ["greenhouse"]."""
    host = where.split("/", 1)[0].lower().split(":")[0]
    if host in _ALIASES:
        return [_ALIASES[host]]
    for suffix, name in _HOST_SUFFIX.items():
        if host == suffix or host.endswith("." + suffix):
            return [name]
    if "." not in host:
        return [host] if host else []  # an app name
    return [w for w in host.split(".") if w not in _GENERIC and len(w) > 2 and not re.fullmatch(r"wd\d+", w)][:2]


def goal_sites(goal):
    """The sites a job's goal is about: hosts of the URLs in it, plus job boards it names."""
    goal = goal or ""
    sites = []
    for url in _URL_IN.findall(goal):
        sites += site_words(urlparse(url).netloc)
    low = goal.lower()
    for name in sorted(set(_HOST_SUFFIX.values()) | set(_ALIASES.values())):
        if re.search(r"\b" + re.escape(name), low):
            sites.append(name)
    return list(dict.fromkeys(s for s in sites if s))


def _lessons(text=None):
    if text is not None:
        return [l[2:].strip() for l in text.splitlines() if l.startswith("- ")]
    try:
        text = (DOTS_DIR / "lessons.md").read_text(encoding="utf-8")
    except FileNotFoundError:
        return []
    return [l[2:].strip() for l in text.splitlines() if l.startswith("- ")]


def lessons_about(words, limit=HINT_LESSONS):
    if not words:
        return []
    pats = [re.compile(r"\b" + re.escape(w), re.I) for w in words]
    hits = [l for l in _lessons() if any(p.search(l) for p in pats)]
    return hits[-limit:]  # newest last, and newer ones tend to replace older


def pick_lessons(goal, budget=3000, text=None):
    """The lessons worth putting in a job's prompt: the ones about the sites this
    job is about first (the newest SITE_KEEP per site; older ones about the same
    site are usually what a newer one corrected), then ones sharing its words,
    then the newest. Replaces taking the file's last 3000 characters, which hid
    everything older (most of what it had learned)."""
    lines = _lessons(text)
    sites = goal_sites(goal)
    words = {w.strip(".'-") for w in re.findall(r"[a-z0-9][a-z0-9'.-]{3,}", (goal or "").lower())}
    words = {w for w in words if w and w not in _STOP and w not in _GENERIC and w not in sites}
    site_pats = {s: re.compile(r"\b" + re.escape(s), re.I) for s in sites}
    word_pats = [re.compile(r"\b" + re.escape(w), re.I) for w in words]
    site_hits, dropped = {}, set()
    for s, pat in site_pats.items():
        about = [i for i, l in enumerate(lines) if pat.search(l)]
        dropped |= set(about[:-SITE_KEEP])  # superseded by the newer ones about the same site
        for i in about[-SITE_KEEP:]:
            site_hits[i] = site_hits.get(i, 0) + 1
    dropped -= set(site_hits)  # still among the newest for another site it's about

    def score(i):
        return 10 * site_hits.get(i, 0) + sum(1 for p in word_pats if p.search(lines[i]))
    ranked = sorted((i for i in range(len(lines)) if i not in dropped),
                    key=lambda i: (score(i) > 0, score(i), i), reverse=True)
    keep, used = set(), 0
    for i in ranked:
        cost = len(lines[i]) + 3
        if used + cost > budget:
            continue
        keep.add(i)
        used += cost
    return "\n".join(f"- {lines[i]}" for i in sorted(keep))


def _slow_spots(words):
    """Past slow places with no lesson written about them."""
    try:
        rows = [json.loads(r) for r in SPEED_LOG.read_text(encoding="utf-8").splitlines()[-400:] if r.strip()]
    except (FileNotFoundError, ValueError):
        return []
    out = [r for r in rows if r.get("slow") and not r.get("learned")
           and any(w in r.get("where", "").lower() for w in words)]
    return out[-2:]


def _fmt(sec):
    sec = int(sec)
    return f"{sec}s" if sec < 60 else f"{sec // 60}m {sec % 60:02d}s"


class Coach:
    """One per run. `after(name, args, result, seconds)` is period's
    _tool_after_hook: it returns a note to add to the tool's result, or None."""

    def __init__(self, job_id=""):
        self.job_id = job_id
        self.where = ""          # where the current stretch of screen work is
        self.steps = 0
        self.secs = 0.0
        self.misses = 0          # steps that failed (didn't find the button, etc.)
        self.started = 0.0
        self.nudged = 0
        self.seen = set()        # places it's already been given hints for this run
        self.slow_places = []    # the stretches that were slow, for speed.jsonl
        self.tools = 0           # tool calls in this stretch (several can share one send)
        self.tool_secs = 0.0     # seconds the tools themselves took in this stretch
        self.sends = 0           # model turns (sends) in the whole run
        self._last_end = None    # when the previous tool call finished
        self._last_turn = None   # caller-given turn id, when it has one
        self._clock = time.time

    # -- where is it working? ------------------------------------------------
    def _place(self, name, args, result):
        # Only where it *went*: the url it was told to open, or the page a result
        # says it's on. Any other URL in the args or the page text is just content.
        url = str((args or {}).get("url") or "")
        if not url.startswith(("http://", "https://")):
            url = ""
        if not url and isinstance(result, str):
            m = _RESULT_URL.search(result[:600])
            url = (m.group(1) or m.group(2)) if m else ""
        if url:
            u = urlparse(url)
            path = "/".join(u.path.strip("/").split("/")[:3])
            return f"{u.netloc.lower()}/{path}".rstrip("/")
        if name.startswith(("computer_", "app_", "mcp_windows_")):
            app = str((args or {}).get("app") or "") or _foreground_app()
            return app.lower()
        return self.where  # vm_click, tab_click...: still on the page it was on

    # -- the hook -------------------------------------------------------------
    def _new_send(self, seconds, turn):
        """Whether this tool call came from a new model turn, and the thinking gap
        before it. With no turn id from the caller, a gap of SEND_GAP or more
        between calls means a new turn (calls from one reply run back to back)."""
        now = self._clock()
        start = now - max(0.0, float(seconds or 0))
        gap = 0.0 if self._last_end is None else max(0.0, start - self._last_end)
        if turn is not None:
            new = turn != self._last_turn
            self._last_turn = turn
        else:
            new = self._last_end is None or gap >= SEND_GAP
        self._last_end = now
        return new, gap

    def after(self, name, args, result, seconds, turn=None):
        new_send, gap = self._new_send(seconds, turn)  # every tool call moves the clock
        if new_send:
            self.sends += 1
        if not is_screen_tool(name):
            return None
        place = self._place(name, args, result)
        notes = []
        if place != self.where:
            self._close_stretch()
            self.where, self.steps, self.secs, self.misses, self.nudged = place, 0, 0.0, 0, 0
            self.tools, self.tool_secs = 0, 0.0
            self.started = self._clock()
            new_send = True  # the first step in a new place is its first send there
            hint = self._arrival_hint(place)
            if hint:
                notes.append(hint)
        self.tools += 1
        if new_send:
            self.steps += 1  # steps = sends spent here, not tool calls
        tool_sec = max(0.0, float(seconds or 0))
        self.tool_secs += tool_sec
        self.secs += tool_sec + min(gap, GAP_CAP)  # working time: tools plus (capped) thinking
        if isinstance(result, str) and result.lstrip().startswith("Error"):
            self.misses += 1
        effort = self.steps + self.misses
        slow = effort >= SLOW_STEPS * (self.nudged + 1) or (
            self.steps >= SLOW_MIN_STEPS and self.secs >= SLOW_SEC * (self.nudged + 1))
        if slow and self.nudged < 2:
            self.nudged += 1
            notes.append(self._nudge(name, self.secs))
        return "\n\n".join(notes) or None

    def _arrival_hint(self, place):
        words = site_words(place)
        key = " ".join(words)
        if not key or key in self.seen:
            return None
        self.seen.add(key)
        tips = lessons_about(words)
        slow = _slow_spots(words)
        if not tips and not slow:
            return None
        lines = [f"[What you learned about {key} before; use it]"] + [f"- {t}" for t in tips]
        for r in slow:
            lines.append(f"- last time {r['steps']} steps / {_fmt(r['sec'])} went into {r['where']} "
                         "and no faster way was found. Look for one first (see the speed check rules).")
        return "\n".join(lines)

    def _nudge(self, name, wall):
        on_pc = name.startswith(("computer_", "app_", "mcp_windows_"))
        ways = ("their app's keyboard shortcut or menu accelerator, app_do / Windows UI automation by "
                "control name instead of pixels, a PowerShell or URL-scheme command that does it directly"
                if on_pc else
                "click and fill by text (vm_click {\"text\"}, vm_fill by label) instead of x,y; vm_read "
                "\"links\"/\"fields\" once instead of screenshots; go straight to the URL; the site's own "
                "API or a JSON endpoint; one vm_run Playwright script (connect_over_cdp to 127.0.0.1:9222) "
                "that does the whole form or every repeat in one go; or hand the whole batch to vm_claude, "
                "which works through it without using your message limit")
        again = " This is the second check: the first idea didn't make it fast." if self.nudged > 1 else ""
        return (f"[Speed check] {self.steps} replies and {_fmt(wall)} have gone into "
                f"{self.where or 'this one spot'} ({self.misses} missed).{again} That's slow. Before the "
                f"next click, stop and think of a faster way to get this done, and try it. Ideas: {ways}. "
                "Batch steps you can predict into one reply. When something works noticeably faster, "
                "write one line LEARNED: <site or app>: <the fast way, specific enough to reuse> so "
                "every future job does it that way from the start.")

    def _close_stretch(self):
        if not self.where or not self.steps:
            return
        if self.nudged or self.steps >= SLOW_STEPS:
            self.slow_places.append({"where": self.where, "steps": self.steps, "sec": round(self.secs),
                                     "tool_sec": round(self.tool_secs), "tools": self.tools,
                                     "misses": self.misses})

    def close(self, learned=()):
        """End of the run: log the slow places, marking the ones a lesson now covers."""
        self._close_stretch()
        self.where, self.steps = "", 0
        if not self.slow_places:
            return
        said = " ".join(learned).lower()
        try:
            DOTS_DIR.mkdir(parents=True, exist_ok=True)
            with open(SPEED_LOG, "a", encoding="utf-8") as f:
                for r in self.slow_places:
                    words = site_words(r["where"])
                    r.update(t=round(time.time()), job=self.job_id, slow=True,
                             learned=bool(words) and any(w in said for w in words))
                    f.write(json.dumps(r) + "\n")
        except Exception:
            pass
        self.slow_places = []


# -- the overnight optimizer's reading: where the time and sends went -----------

def _read_jsonl(path, last=5000):
    try:
        lines = Path(path).read_text(encoding="utf-8", errors="replace").splitlines()[-last:]
    except OSError:
        return []
    rows = []
    for line in lines:
        try:
            row = json.loads(line)
        except ValueError:
            continue
        if isinstance(row, dict):
            rows.append(row)
    return rows


def _ts(value):
    """A row's time as epoch seconds: a number, or an ISO timestamp."""
    if isinstance(value, (int, float)):
        return float(value)
    try:
        from datetime import datetime
        return datetime.fromisoformat(str(value).replace("Z", "+00:00")).timestamp()
    except (TypeError, ValueError):
        return 0.0


def speed_report(days=7, top=8, data=False, now=None):
    """Read-only summary of where Dot is slow, for the overnight speed job:
    the slowest places, slow places no lesson covers yet, sends per job, and
    failed requests. Returns plain text (or the dict behind it with data=True)."""
    now = time.time() if now is None else now
    since = now - days * 86400

    places = {}
    for r in _read_jsonl(SPEED_LOG):
        if not r.get("slow") or _ts(r.get("t")) < since:
            continue
        p = places.setdefault(r.get("where", "?"), {"where": r.get("where", "?"), "visits": 0, "sends": 0,
                                                     "sec": 0, "misses": 0, "learned": False, "jobs": set()})
        p["visits"] += 1
        p["sends"] += int(r.get("steps") or 0)
        p["sec"] += int(r.get("sec") or 0)
        p["misses"] += int(r.get("misses") or 0)
        p["learned"] = p["learned"] or bool(r.get("learned"))
        if r.get("job"):
            p["jobs"].add(r["job"])
    lessons = _lessons()
    for p in places.values():
        words = site_words(p["where"])
        p["has_lesson"] = bool(words) and any(re.search(r"\b" + re.escape(w), l, re.I) for w in words for l in lessons)
        p["jobs"] = sorted(p["jobs"])
    slow = sorted(places.values(), key=lambda p: (p["sec"], p["sends"]), reverse=True)
    no_lesson = [p for p in slow if not p["has_lesson"] and not p["learned"]]

    jobs = []
    for f in sorted(Path(DOTS_DIR).glob("*/dot.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8", errors="replace"))
        except (OSError, ValueError):
            continue
        if not isinstance(d, dict) or _ts(d.get("updated") or d.get("created")) < since:
            continue
        jobs.append({"id": d.get("id") or f.parent.name, "label": d.get("label") or d.get("name") or "",
                     "status": d.get("status", ""), "sends": int(d.get("sends") or 0),
                     "runs": int(d.get("runs") or 0), "kind": d.get("kind", "")})
    jobs.sort(key=lambda j: j["sends"], reverse=True)
    finished = [j for j in jobs if j["status"] == "done"]
    total_sends = sum(j["sends"] for j in jobs)

    reqs = [r for r in _read_jsonl(TELEMETRY_LOG, last=20000) if _ts(r.get("timestamp")) >= since]
    fails = {}
    for r in reqs:
        if r.get("success") is False:
            kind = str(r.get("error_type") or "error")
            fails[kind] = fails.get(kind, 0) + 1

    try:  # what the fast paths (pd_fast) did instead of model turns
        import pd_fast
        fast = pd_fast.stats(days, now)
    except Exception:
        fast = None

    out = {"days": days, "slow_places": slow[:top], "no_lesson": no_lesson[:top], "jobs": jobs[:top * 2],
           "fast": fast,
           "job_count": len(jobs), "total_sends": total_sends, "finished_jobs": len(finished),
           "sends_per_finished_job": round(sum(j["sends"] for j in finished) / len(finished), 1) if finished else None,
           "requests": len(reqs), "failures": dict(sorted(fails.items(), key=lambda kv: -kv[1]))}
    if data:
        return out

    lines = [f"Speed report, last {days} days"]
    lines.append("Slowest places (sends / working time / misses, visits):")
    lines += [f"- {p['where']}: {p['sends']} sends, {_fmt(p['sec'])}, {p['misses']} missed, {p['visits']}x"
              + ("" if p["has_lesson"] or p["learned"] else "  [no lesson yet]") for p in slow[:top]] or ["- none logged"]
    lines.append("Slow places with no lesson (best targets for a ~/tools/ script):")
    lines += [f"- {p['where']} ({p['sends']} sends over {p['visits']} visits)" for p in no_lesson[:top]] or ["- none"]
    lines.append(f"Jobs: {len(jobs)}, {total_sends} sends in all; {len(finished)} finished"
                 + (f", {out['sends_per_finished_job']} sends per finished job" if finished else ""))
    lines += [f"- {j['id']} {j['label'][:40]!r} ({j['status']}): {j['sends']} sends over {j['runs']} runs"
              for j in jobs[:top * 2]]
    if fast and (sum(fast["hits"].values()) or fast["failed"]):
        h = fast["hits"]
        lines.append(f"Fast paths: {h['text']} done straight from the text, {h['brain']} by the quick brain "
                     f"without a job, {h['prefetch']} jobs started with their look-ups done; about "
                     f"{fast['sends_saved']} sends and {fast['seconds_saved'] // 60} min saved"
                     f" ({fast['failed']} fell back to the slow way)")
    failed = sum(fails.values())
    lines.append(f"Requests: {len(reqs)}, {failed} failed"
                 + (" (" + ", ".join(f"{k} {v}" for k, v in out["failures"].items()) + ")" if fails else ""))
    return "\n".join(lines)
