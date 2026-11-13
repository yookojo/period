"""Dots: Period agents that keep working after you walk away.

    python pd_dots.py serve            run the daemon (the login task starts it hidden)
    python pd_dots.py restart          close a running daemon and start this one (after code changes)
    python pd_dots.py supervise        run the daemon and restart it if it dies
    python pd_dots.py new "goal"       add a Dot
    python pd_dots.py list
    python pd_dots.py install          start the daemon at login (hidden)
    python pd_dots.py connect-discord  DM Dot on Discord (no Mac needed)
    python pd_dots.py connect-self     text Dot in your own note-to-self chat (your iCloud)
    python pd_dots.py connect-line     or give Dot its own iMessage address (see docs/DOTS.md)
    python pd_dots.py setup-mac        Mac: Claude-only, connect Discord, start at login (mac/install-dot.sh runs it)
    python pd_dots.py doctor           check this install (Claude Code, chat, the Dot PC, login job)
    python pd_dots.py uninstall        Mac: stop Dot and remove its login job

Each Dot has a goal, a status, a log and optionally a schedule. The daemon runs
one at a time through the normal agent loop (run_agent_loop), on the Dot PC
(pd_vm) by default and on this PC when the goal needs your apps or files. It is
the only thing that talks to the server for Dots, so the 6-a-minute limit and
the login token are shared safely.

Ways in and out:
- the Dots page (http://localhost:8767, and your phone over Tailscale): list,
  new Dot, its log, a live view of the Dot PC, Yes/No when it needs you, memory;
- Dot's own iMessage contact (optional): text it a job, it texts back progress,
  questions and results. It only answers the addresses you list, and it only
  ever sees texts sent to its own account, never yours.
"""
import contextlib
import copy
import datetime
import hashlib
import io
import json
import os
import re
import secrets
import shutil
import sys
import threading
import time
import traceback
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
# pd_dotlive / pd_dotwatch `import pd_dots`; run as a script this module is
# __main__, and they must share its state rather than load a second copy.
sys.modules.setdefault("pd_dots", sys.modules[__name__])
import pd_checker  # noqa: E402
import pd_proof  # noqa: E402

# A model from another family double-checks "done/sent" texts and email drafts (PERIOD_DOT_CHECKER=off to disable).
CHECKER_ON = os.environ.get("PERIOD_DOT_CHECKER", "").lower() not in ("off", "0", "no")
DOTS_DIR = Path(os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))
MEMORY_PATH = DOTS_DIR / "memory.md"
SETTINGS_PATH = DOTS_DIR / "settings.json"
KEY_PATH = DOTS_DIR / "key"
PORT = int(os.environ.get("PERIOD_DOTS_PORT", "8767"))
STEPS_PER_RUN = 30
MAX_RUNS_UNTIL_DONE = 2         # runs of one request before it checks in with you
TASK_TIME_LIMIT_SEC = 15 * 60   # one request's working time before it checks in
SAME_CALL_LIMIT = 3             # the exact same action this many times = stuck
JOB_SENDS_PER_MINUTE = 5        # of the server's 6; the last one is kept for answering texts
BURST_SEC = 2.0                 # texts this close together are read as one message
TRAIL_KEEP = 25                 # steps remembered per job
SCREEN_WAIT_SEC = 20            # wait this long for a busy screen, then work around it
QUESTION_TIMEOUT_SEC = 30 * 60  # unanswered questions count as "no"
LINE_POLL_SEC = 5

_LINE_URL = "Period:dotline:url"
_LINE_PW = "Period:dotline:password"

_sc = None


def sc():
    """period.py, loaded once (it is big; the CLI bits don't need it)."""
    global _sc
    if _sc is None:
        import period
        try:
            import pd_claude
            pd_claude.install(period)  # big jobs can go to Claude Code, boxed in
        except Exception as e:
            print(f"[claude] {e}", file=sys.stderr)
        _sc = period
    return _sc


def _live():
    import pd_dotlive
    return pd_dotlive


# --- storage -------------------------------------------------------------------

def _now():
    return time.time()


def _stamp(t=None):
    return datetime.datetime.fromtimestamp(t or _now()).strftime("%b %d %I:%M %p").replace(" 0", " ")


def _write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(f".{os.getpid()}.{threading.get_ident()}.tmp")  # jobs are separate processes
    tmp.write_text(json.dumps(data, indent=2), encoding="utf-8")
    for attempt in range(20):  # Windows refuses a replace while someone has the file open
        try:
            os.replace(tmp, path)
            return
        except PermissionError:
            time.sleep(0.05)
    os.replace(tmp, path)


def settings():
    try:
        return json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_settings(s):
    _write_json(SETTINGS_PATH, s)


def _front_template():
    return FRONT_PROMPT


# --- keeping secrets off disk ------------------------------------------------------
# Sign-in codes, one-time codes and passwords they text Dot are masked before they
# land in front.log, chat.jsonl or a job's saved goal. The job still gets the real
# text once (through its inbox), so it can use the code right away.

_REDACTIONS = (
    # a sign-in code pasted from an OAuth page: two long url-safe tokens joined by '#'
    (re.compile(r"(?<![\w/#?=&.%-])[A-Za-z0-9_-]{16,}#[A-Za-z0-9_-]{16,}(?![\w#])"),
     lambda m: "[code hidden]" if len(m.group(0)) >= 40 else m.group(0)),
    # "code: 482913", "your otp is 1234-5678", "pin 9921" (at least 4 digits; not zip/area/error codes)
    (re.compile(r"(?i)(?<!zip )(?<!area )(?<!postal )(?<!country )(?<!error )(?<!status )(?<!source )"
                r"\b(code|otp|pin|passcode)\b(\s*(?:is\s+|was\s+|[:=#]\s*|\s))"
                r"(?=(?:[A-Za-z-]*\d){4})[A-Za-z0-9-]{4,12}\b"),
     lambda m: m.group(1) + m.group(2) + "[code hidden]"),
    # "password: hunter2", "vnc pw is abc123"
    (re.compile(r"(?i)\b(password|passwd|pwd|pw)\b(\s*(?:is\s+|was\s+|[:=]\s*))(?!\[hidden\])[^\s\"'<>,;]+"),
     lambda m: m.group(1) + m.group(2) + "[hidden]"),
)


def redact(text):
    """Mask codes and passwords in text that's about to be saved. Ordinary text
    and links are left alone."""
    if not text or not isinstance(text, str):
        return text
    for pattern, repl in _REDACTIONS:
        text = pattern.sub(repl, text)
    return text


_store_lock = threading.RLock()
_file_locks = {}  # dot id -> [open lock file, depth] while this process holds it


@contextlib.contextmanager
def _dot_lock(dot_id):
    """Hold a Dot's dot.json for a read-change-write, across processes too (each
    job is its own process, and the daemon saves the same file): a lock file
    next to it. Re-entrant within this process; gives up waiting after 10 s
    rather than hang a job."""
    with _store_lock:
        held = _file_locks.get(dot_id)
        if held:
            held[1] += 1
            try:
                yield
            finally:
                held[1] -= 1
            return
        folder = DOTS_DIR / dot_id
        fh = None
        if folder.is_dir():  # never re-create a deleted Dot's folder
            try:
                fh = open(folder / "dot.lock", "a+b")
                deadline = time.time() + 10
                while True:
                    try:
                        if sys.platform == "win32":
                            import msvcrt
                            fh.seek(0)
                            msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
                        else:
                            import fcntl
                            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                        break
                    except OSError:
                        if time.time() > deadline:
                            print(f"[lock] {dot_id} stayed locked, going on without it", file=sys.stderr)
                            fh.close()
                            fh = None
                            break
                        time.sleep(0.02)
            except OSError:
                fh = None
        _file_locks[dot_id] = [fh, 1]
        try:
            yield
        finally:
            _file_locks.pop(dot_id, None)
            if fh is not None:
                try:
                    if sys.platform == "win32":
                        import msvcrt
                        fh.seek(0)
                        msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
                    else:
                        import fcntl
                        fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
                fh.close()


class Dot:
    FIELDS = dict(id="", name="", goal="", status="queued", computer="auto", schedule="",
                  model="", created=0.0, updated=0.0, next_run=0.0, runs=0, runs_this_goal=0,
                  conv_id=None, parent_id=None, summary="", question=None, asking="", answer=None,
                  source="page", reply_to="", messages=[], kind="chat", current="", pid=0, step="",
                  started=0.0, label="", context="", trail=[], sends=0, live=False, trigger="", api_errors=0,
                  # qid: which question it's waiting on (buttons carry it); asked_at: when it asked
                  qid="", asked_at=0.0, last_q="", last_q_at=0.0, told_at=0.0, wait_wakes=0,
                  sends_per_minute=0,  # 0 = JOB_SENDS_PER_MINUTE
                  nudges=0,  # autonomous job: times in a row it got un-stuck without asking them
                  unread_alerted=0.0,  # the unread message it already warned them about (its arrival time)
                  idle_runs=0,  # endless job: stretches in a row that found nothing to do
                  empty_runs=0,  # runs in a row that ran no tool at all on work that needs them (audit 11-10)
                  spin_runs=0,  # any job, lanes and endless ones too: runs in a row that called no tool (11-11)
                  look=[])  # look-ups the quick brain said it needs first, run before its first send (pd_fast)

    def __init__(self, **kw):
        for k, v in self.FIELDS.items():
            setattr(self, k, kw.get(k, json.loads(json.dumps(v))))

    @property
    def folder(self):
        return DOTS_DIR / self.id

    @property
    def log_path(self):
        return self.folder / "log.txt"

    def save(self):
        self.updated = _now()
        self.folder.mkdir(parents=True, exist_ok=True)
        with _dot_lock(self.id):
            _write_json(self.folder / "dot.json", {k: getattr(self, k) for k in self.FIELDS})

    def log(self, text):
        self.folder.mkdir(parents=True, exist_ok=True)
        with open(self.log_path, "a", encoding="utf-8") as f:
            f.write(text)

    # The chat and messages waiting to be read live in their own append-only
    # files, so a text that arrives while a run is saving dot.json is never lost.
    def add_message(self, who, text, **extra):
        self.folder.mkdir(parents=True, exist_ok=True)
        with _store_lock, open(self.folder / "chat.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(dict({"from": who, "text": redact(text), "t": _now()}, **extra)) + "\n")

    def chat(self):
        try:
            rows = (self.folder / "chat.jsonl").read_text(encoding="utf-8").splitlines()
        except FileNotFoundError:
            return list(self.messages)
        return list(self.messages) + [json.loads(r) for r in rows if r.strip()]

    def push_followup(self, text):
        self.folder.mkdir(parents=True, exist_ok=True)
        with _store_lock:
            if not self.has_followups():
                (self.folder / "inbox.since").write_text(str(_now()), encoding="utf-8")
            with open(self.folder / "inbox.txt", "a", encoding="utf-8") as f:
                f.write(json.dumps(text) + "\n")
            if not str(text or "").lstrip().startswith(("[", "(")):  # "[They said to keep going ...]" and
                # "(the exact details ...)" are the daemon; only their own words start the reply window
                # 2026-11-04: their message forwarded here; kept after the inbox is read so replies to it reach them
                (self.folder / "heard.at").write_text(str(_now()), encoding="utf-8")

    def has_followups(self):
        p = self.folder / "inbox.txt"
        return p.exists() and p.stat().st_size > 0

    def unread(self):
        """(how many messages it hasn't read yet, when the oldest arrived)"""
        try:
            rows = [r for r in (self.folder / "inbox.txt").read_text(encoding="utf-8").splitlines() if r.strip()]
        except FileNotFoundError:
            return 0, 0.0
        try:
            since = float((self.folder / "inbox.since").read_text(encoding="utf-8"))
        except (FileNotFoundError, ValueError):
            since = (self.folder / "inbox.txt").stat().st_mtime if rows else 0.0
        return len(rows), since

    def take_followups(self):
        p = self.folder / "inbox.txt"
        with _store_lock:
            try:
                rows = p.read_text(encoding="utf-8").splitlines()
            except FileNotFoundError:
                return ""
            p.unlink(missing_ok=True)
            (self.folder / "inbox.since").unlink(missing_ok=True)
        return "\n".join(json.loads(r) for r in rows if r.strip())

    def log_tail(self, chars=20000):
        try:
            data = self.log_path.read_text(encoding="utf-8", errors="replace")
        except FileNotFoundError:
            return ""
        return data[-chars:]

    def public(self):
        d = {k: getattr(self, k) for k in self.FIELDS if k not in ("conv_id", "parent_id")}
        d["messages"] = self.chat()[-200:]
        d["when"] = _stamp(self.updated)
        d["next"] = _stamp(self.next_run) if self.next_run and self.status == "sleeping" else ""
        return d


def _read_dot_data(dot_id):
    """dot.json as a dict. FileNotFoundError means it's gone; anything else (a
    half-written file, Windows holding it during a replace) is tried again."""
    path = DOTS_DIR / dot_id / "dot.json"
    for attempt in range(20):
        try:
            with _dot_lock(dot_id):
                return json.loads(path.read_text(encoding="utf-8"))
        except FileNotFoundError:
            raise
        except Exception:
            if attempt == 19:
                raise
            time.sleep(0.05)


def load_dot(dot_id):
    try:
        data = _read_dot_data(dot_id)
    except FileNotFoundError:
        return None
    except Exception as e:
        print(f"[load] {dot_id}: {e}", file=sys.stderr)
        return None
    data.setdefault("kind", "legacy")  # saved before tasks existed: an old merged chat, never resumed
    return Dot(**data)


def _update(dot, force=False, **fields):
    """Change only these fields, on top of what's on disk now (another thread or
    a job's own process may have saved since `dot` was loaded). A "stopped" Dot
    stays stopped unless a person restarts it (force=True). Also updates `dot`
    in memory."""
    with _dot_lock(dot.id):
        disk = load_dot(dot.id)
        if disk is None:  # deleted
            for k, v in fields.items():
                setattr(dot, k, v)
            return dot
        if disk.status == "stopped" and not force and fields.get("status", "stopped") != "stopped":
            fields = {k: v for k, v in fields.items() if k != "status"}
        for k, v in fields.items():
            setattr(disk, k, v)
        disk.save()
    for k in Dot.FIELDS:
        setattr(dot, k, getattr(disk, k))
    return dot


_dots_cache = {}  # dot id -> ((mtime, size) of dot.json, its data), so an unchanged file isn't re-read


def all_dots():
    out, seen = [], set()
    if DOTS_DIR.exists():
        for f in DOTS_DIR.glob("*/dot.json"):
            dot_id = f.parent.name
            seen.add(dot_id)
            try:
                st = f.stat()
                key = (st.st_mtime_ns, st.st_size)
            except OSError:
                continue
            hit = _dots_cache.get(dot_id)
            if hit and hit[0] == key:
                data = hit[1]
            else:
                try:
                    data = _read_dot_data(dot_id)
                except Exception:
                    continue
                data.setdefault("kind", "legacy")
                _dots_cache[dot_id] = (key, data)
            out.append(Dot(**copy.deepcopy(data)))  # a fresh copy: callers change their Dots
    for gone in set(_dots_cache) - seen:
        _dots_cache.pop(gone, None)
    return sorted(out, key=lambda d: d.created, reverse=True)


def _short_name(goal):
    words = re.sub(r"[^\w\s'-]", " ", goal).split()
    return " ".join(words[:5])[:40] or "Dot"


def new_dot(goal, computer="auto", schedule="", model="", source="page", reply_to="", kind=None,
            status="queued"):
    raw = goal.strip()
    goal = redact(raw)  # codes and passwords stay off disk...
    kind = kind or ("job" if schedule.strip() else "task")
    dot = Dot(id=datetime.datetime.now().strftime("%m%d-") + uuid.uuid4().hex[:5], name=_short_name(goal),
              goal=goal, computer=computer if computer in ("auto", "vm", "pc") else "auto",
              schedule=schedule.strip(), model=model, created=_now(), next_run=_now(),
              source=source, reply_to=reply_to, kind=kind, status=status)
    dot.save()
    if goal != raw:  # ...but the job still gets them once, through its inbox
        dot.push_followup(f"(the exact details for this, not saved anywhere: {raw})")
    dot.log(f"=== {_stamp()} · new Dot: {goal}\n")
    _wake.set()
    return dot


# --- schedules -----------------------------------------------------------------
# "every 30 minutes", "every 2 hours", "hourly", "daily 8:00", "every day at 7am",
# "weekdays 9:30". Anything else means "run once".

def next_run_after(schedule, after=None):
    s = (schedule or "").strip().lower()
    after = after or _now()
    if not s:
        return None
    m = re.match(r"every\s+(\d+)\s*(m|min|mins|minutes?|h|hr|hrs|hours?)\b", s)
    if m:
        n = int(m.group(1)) * (60 if m.group(2).startswith("m") else 3600)
        return after + max(n, 300)
    if s in ("hourly", "every hour"):
        return after + 3600
    m = re.search(r"(daily|every day|weekdays|every weekday)\D*(\d{1,2})(?::(\d{2}))?\s*(am|pm)?", s)
    if m:
        hour, minute = int(m.group(2)), int(m.group(3) or 0)
        if m.group(4) == "pm" and hour < 12:
            hour += 12
        if m.group(4) == "am" and hour == 12:
            hour = 0
        base = datetime.datetime.fromtimestamp(after)
        cand = base.replace(hour=hour % 24, minute=minute, second=0, microsecond=0)
        while cand.timestamp() <= after or ("weekday" in m.group(1) and cand.weekday() >= 5):
            cand += datetime.timedelta(days=1)
        return cand.timestamp()
    return None


# --- memory --------------------------------------------------------------------

def memory_text():
    try:
        return MEMORY_PATH.read_text(encoding="utf-8")
    except FileNotFoundError:
        return ""


# Lines that are rules for how to work always go in, whatever the job.
_PINNED_RE = re.compile(r"\b(never|don'?t|do not|always|rule|rules|must|only ever)\b", re.I)
# Personal facts for forms (demographics, GPA, phone...) only go to jobs that fill forms.
_PERSONAL_RE = re.compile(r"\b(race|ethnicity|hispanic|latino|gender|pronouns|veteran|disabilit\w*|disabled|"
                          r"gpa|citizen\w*|visa|sponsorship|phone( number)?|date of birth|birthday|sexual orientation)\b",
                          re.I)
_FORM_GOAL_RE = re.compile(r"\b(appl(y|ying|ied|ication|ications)|forms?|internships?|sign ?up|register|"
                           r"greenhouse|lever|workday|ashby|job posting)\b", re.I)
PINNED_BUDGET = 6000  # rule lines for a job that isn't an application or form (those still get every rule)
_ALWAYS_PINNED_RE = re.compile(r"\b(message ?archive|imessage|whatsapp|(chat|message|text) history|private|"
                               r"remote[- ]connected|passwords?|card|money|pay|payment|purchas\w*|buy\w*|"
                               r"spend\w*|bank)\b", re.I)


def memory_for(goal, budget=2500):
    """What a job should know about them: the rules always, personal form facts
    only for applications and forms, then the facts most about this job (like
    the lessons). Replaces taking the file's last N characters, which cut off
    "don't send history to the server"."""
    lines = [re.sub(r"^\s*[-*]\s*", "", l).strip() for l in memory_text().splitlines()]
    lines = [l for l in lines if l and not l.startswith("#")]
    if not lines:
        return ""
    forms = bool(_FORM_GOAL_RE.search(goal or ""))
    pinned = [l for l in lines if _PINNED_RE.search(l)]
    rest = [l for l in lines if l not in pinned and (forms or not _PERSONAL_RE.search(l))]
    if not _FORM_GOAL_RE.search((goal or "")[:300]) and sum(len(l) + 3 for l in pinned) > PINNED_BUDGET:
        # 2026-11-10 audit: 140 "never/don't/always" lines (48k characters, nearly all application-lane
        # minutiae) went into every job, a Math 21 Drive folder included, and buried its ask. Privacy and
        # money rules always go in; the other rules go in by how much they're about this job.
        safety = [l for l in pinned if _ALWAYS_PINNED_RE.search(l)]
        others = [l for l in pinned if l not in safety]
        try:
            picked_rules = _sc_speed().pick_lessons(goal, budget=PINNED_BUDGET,
                                                    text="\n".join(f"- {l}" for l in others))
            chosen = {re.sub(r"^\s*-\s*", "", p).strip() for p in picked_rules.splitlines() if p.strip()}
        except Exception:
            chosen = set(others[-20:])
        pinned = safety + [l for l in others if l in chosen]
    if forms:  # every form fact, then the rest by relevance
        personal = [l for l in rest if _PERSONAL_RE.search(l)]
        rest = [l for l in rest if l not in personal]
        pinned += personal
    used = sum(len(l) + 3 for l in pinned)
    picked = ""
    if rest and budget - used > 100:
        try:
            picked = _sc_speed().pick_lessons(goal, budget=budget - used, text="\n".join(f"- {l}" for l in rest))
        except Exception:
            picked = "\n".join(f"- {l}" for l in rest[-12:])
    keep = set(pinned) | {re.sub(r"^\s*-\s*", "", p).strip() for p in picked.splitlines() if p.strip()}
    return "\n".join(f"- {l}" for l in lines if l in keep)  # in their original order


def remember(line):
    line = line.strip()
    if not line:
        return
    MEMORY_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(MEMORY_PATH, "a", encoding="utf-8") as f:
        f.write(f"- {line}\n")


# --- standing instructions: on/off states that apply to every job, newest wins ------
# "pause the applications", "only one job at a time". Kept here, not written into a
# job's goal, where they outlived newer instructions and jobs paused each other.

STANDING_PATH = DOTS_DIR / "standing.json"
# A job's last reply saying it has no tools ("this session has no tool access", "No computer, VM, mail, or calendar
# tools are connected here"): period's detector misses these, and the claim repeats every run once it's in
# the history.
_NO_TOOLS_RE = re.compile(
    r"\b(no|without|don't have|do not have|can't|cannot|unable to)\b[^.\n]{0,80}?"
    r"\b(tool access|tools? (are |is )?(connected|available)|run (commands|anything)|reach the (vm|dot pc)|"
    r"access to the (vm|dot pc)|(live )?connection to the (vm|dot pc)|vm[^.\n]{0,40}tools)", re.I)


def standing():
    """{topic: {"text": ..., "at": time}}"""
    try:
        data = json.loads(STANDING_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def set_standing(topic, text):
    """Set what's true now for a topic; empty text clears it."""
    topic = re.sub(r"\s+", " ", str(topic or "")).strip().lower()[:40]
    if not topic:
        return
    data = standing()
    text = redact(re.sub(r"\s+", " ", str(text or "")).strip())
    if text and text.lower() not in ("null", "none", "clear"):
        data[topic] = {"text": text[:300], "at": _now()}
    else:
        data.pop(topic, None)
    _write_json(STANDING_PATH, data)


def standing_text():
    rows = sorted(standing().items(), key=lambda kv: kv[1].get("at", 0) if isinstance(kv[1], dict) else 0)
    return "\n".join(f"- {topic}: {v.get('text', '')} (set {_stamp(v.get('at'))})"
                     for topic, v in rows if isinstance(v, dict) and v.get("text"))


# --- getting smarter: lessons from its own jobs, and knowing what it has ----------

LESSONS_PATH = DOTS_DIR / "lessons.md"
INVENTORY_PATH = DOTS_DIR / "inventory.json"
# What Dot checks for on its own computer (name: why it helps).
VM_KIT = {
    "codex": "OpenAI coding agent: codex exec for coding tasks; ~/tools/ai_run.py --order codex for prompt responses",
    "tesseract": "read text off screenshots (OCR) instead of guessing where to click",
    "ffmpeg": "convert/cut audio and video", "yt-dlp": "download videos and audio from most sites",
    "convert": "ImageMagick: resize/convert images", "pdftotext": "read PDFs as text",
    "pandoc": "convert documents (md/docx/html/pdf)", "soffice": "LibreOffice: open/convert Word, Excel, PowerPoint",
    "jq": "work with JSON", "rclone": "their Google Drive as a folder", "gh": "GitHub from the command line",
    "npm": "Node packages and more MCP servers", "uv": "fast Python installs and Python MCP servers",
    "playwright": "browser control by page element, not screen position",
    "xdotool": "mouse/keyboard", "wmctrl": "switch and arrange windows", "google-chrome": "the browser",
}
VM_PY_KIT = ("playwright", "bs4", "pypdf", "docx", "openpyxl", "cv2", "pytesseract", "PIL", "requests")


def _sc_speed():
    import pd_speed
    return pd_speed


def _sc_fast():
    import pd_fast
    return pd_fast


def lessons_text():
    try:
        return LESSONS_PATH.read_text(encoding="utf-8")
    except FileNotFoundError:
        return ""


def learn(line):
    """A lesson from a job ("Wikimedia downloads need a User-Agent"). Future jobs see it."""
    line = re.sub(r"\s+", " ", line or "").strip()
    if len(line) < 8:
        return
    have = lessons_text()
    key = re.sub(r"\W+", " ", line.lower()).strip()
    if key and key in re.sub(r"\W+", " ", have.lower()):
        return
    LESSONS_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(LESSONS_PATH, "a", encoding="utf-8") as f:
        f.write(f"- {line}\n")


def refresh_inventory():
    """Check what's installed on Dot's computer; saved for every job's [ABOUT YOU]."""
    import subprocess
    names = " ".join(VM_KIT)
    py = ",".join(repr(m) for m in VM_PY_KIT)
    script = (f"for c in {names}; do command -v $c >/dev/null 2>&1 && echo have:$c || echo miss:$c; done; "
              f"python3 -c \"import importlib.util as u; [print(('pyhave:' if u.find_spec(m) else 'pymiss:')+m) "
              f"for m in [{py}]]\"; nproc; free -g | awk '/Mem:/{{print \"ram:\"$2}}'; "
              f"df -BG / | awk 'NR==2{{print \"disk:\"$4}}'")
    try:
        if sys.platform != "win32":  # a Mac's Dot PC is a Lima VM: the VM bridge knows how to reach it
            import pd_vm
            if not pd_vm.DotPC.available():
                return None
            _code, raw, _err = pd_vm.DotPC.sh(script, timeout=60)
            out = raw.decode("utf-8", errors="replace").replace("\r", "").splitlines()
        else:
            # On stdin: wsl re-parses a -c command line through a shell and eats the $vars.
            r = subprocess.run(["wsl", "-d", "Ubuntu-24.04", "--", "bash", "-l", "-s"], input=script,
                               capture_output=True, text=True, timeout=60, creationflags=_NO_WINDOW)
            out = r.stdout.replace("\r", "").splitlines()
    except Exception as e:
        print(f"[inventory] {e}", file=sys.stderr)
        return None
    inv = {"t": _now(), "have": [], "missing": [], "py_have": [], "py_missing": [], "ram": "", "disk": ""}
    for row in out:
        for prefix, key in (("have:", "have"), ("miss:", "missing"), ("pyhave:", "py_have"),
                            ("pymiss:", "py_missing"), ("ram:", "ram"), ("disk:", "disk")):
            if row.startswith(prefix):
                val = row[len(prefix):]
                if isinstance(inv[key], list):
                    inv[key].append(val)
                else:
                    inv[key] = val
    _write_json(INVENTORY_PATH, inv)
    return inv


def _inventory_loop():
    """Re-check its own computer at start and every few hours (jobs install things)."""
    while True:
        refresh_inventory()
        time.sleep(3 * 3600)


def inventory():
    try:
        return json.loads(INVENTORY_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


_VM_SEEN = {"t": 0.0, "ok": False}


def _vm_set_up():
    """Mac/Linux: whether a Dot PC VM exists (checked at most every 10 minutes)."""
    if _now() - _VM_SEEN["t"] > 600:
        try:
            import pd_vm
            _VM_SEEN["ok"] = bool(pd_vm.DotPC.available())
        except Exception:
            _VM_SEEN["ok"] = False
        _VM_SEEN["t"] = _now()
    return _VM_SEEN["ok"]


def self_text(short=False):
    """What Dot knows about itself: its computers, what's installed, what's missing, MCPs."""
    if sys.platform != "win32" and not _vm_set_up():
        return ("You have no computer of your own on this install (no Dot PC VM): do everything on their "
                f"{HOST_PC} with run_command and the screen tools, and never use vm_* tools. Ask before installing "
                "anything or doing anything risky on it.")
    inv = inventory()
    have = ", ".join(inv.get("have", [])) or "unknown (not checked yet)"
    missing = "; ".join(f"{m} ({VM_KIT.get(m, '')})" for m in inv.get("missing", []))
    py_missing = ", ".join(inv.get("py_missing", []))
    try:
        mcps = sorted(sc().load_mcp_server_configs())
    except Exception:
        mcps = []
    if short:
        return (f"Your own computer (Dot PC: {VM_KIND.replace(' 24.04', '')}, {inv.get('ram', '?')} GB RAM, "
                f"{inv.get('disk', '?')} free) has: {have}. Missing: {', '.join(inv.get('missing', [])) or 'nothing'}. "
                f"MCP servers: {', '.join(mcps) or 'none'}. You can install anything on your own computer (vm_run with \"as_root\": true).")
    return (
        f"You can make yourself better. Your own computer (the Dot PC: {VM_KIND}, "
        f"{inv.get('ram', '?')} GB RAM, {inv.get('disk', '?')} disk free) is yours: when a tool would make "
        "a job faster or more reliable, install it with vm_run {\"command\": \"apt-get install -y ...\", \"as_root\": true} "
        "(no sudo: as_root runs it as root; pip install --user / npm in your home need no root) without asking, then use it. On THEIR PC, ask before "
        "installing anything.\n"
        f"Installed on your computer: {have}.\n"
        + (f"Not installed yet: {missing}.\n" if missing else "")
        + (f"Python modules not installed yet: {py_missing}.\n" if py_missing else "")
        + (f"MCP servers you have (mcp_<server>_<tool> tools): {', '.join(mcps)}.\n" if mcps else "")
        + ("On their PC, mcp_windows_Snapshot lists the apps and clickable elements on screen; clicking and "
           "typing by what it lists is more reliable than guessing screen positions.\n" if "windows" in mcps else "")
        + ("On your own computer, use tesseract on a screenshot to read text you can't get any other way, and "
           "Playwright (python3) to drive pages by element.\n" if "tesseract" in inv.get("have", []) else "")
        + "When you hit a snag worth avoiding next time (a site that needs a header, a faster way, a tool "
        "that didn't work), write one line starting LEARNED: so future jobs know it."
    )


# --- Dot's own iMessage line ---------------------------------------------------
# A second BlueBubbles server on the Mac, signed into an Apple ID made just for
# Dot (docs/DOTS.md). Reading it is fine: everything on it was sent to Dot.

SELF_TAG = "🤖 Dot: "


def _split_text(text, limit):
    """Break a long message into pieces under `limit`, between paragraphs, then
    lines, then sentences, then words; only cut mid-word as a last resort."""
    text = text or ""
    out = []
    while len(text) > limit:
        cut = -1
        for sep in ("\n\n", "\n", ". ", "! ", "? ", " "):
            cut = text.rfind(sep, 0, limit)
            if cut > limit // 3:
                cut += len(sep)
                break
            cut = -1
        if cut <= 0:
            cut = limit
        out.append(text[:cut].rstrip())
        text = text[cut:].lstrip()
    if text or not out:
        out.append(text)
    return out


# --- iMessage: texting like a person --------------------------------------------
# Dot's replies were written for Discord (markdown, buttons, long messages). On
# iMessage it texts like a sharp friend: plain text, a few short bubbles with small
# pauses, buttons turned into "text 1, 2 or 3", files as real attachments, never
# the same text twice, and nothing unprompted overnight. Tapbacks and "typing…"
# need BlueBubbles' Private API (docs/IMESSAGE.md); without it Dot just texts.

IMSG_POLL_SEC = 2.0           # Dot's line is checked this often (Discord pushes, BlueBubbles is polled)
IMSG_BURST_SEC = 3.5          # texts this close together are one message (polling adds up to 2 s)
IMSG_UPDATE_GAP_SEC = 120     # progress texts while a job works: at most one every 2 minutes
IMSG_MAX_BUBBLES = 4
IMSG_QUIET_HOURS = (23, 8)    # local time: nothing unprompted (settings "line_quiet_hours" overrides)
IMSG_AWAKE_SEC = 90 * 60      # ...unless they texted in the last 90 minutes
IMSG_DUP_SEC = 10 * 60        # the same text again within 10 min, with nothing from them since, is dropped
IMSG_MENU_SEC = 30 * 60       # "text 2 to ..." options stay answerable this long
IMSG_OVERLAP_MS = 60_000      # each check looks a minute back (late deliveries); message guids stop repeats
IMSG_MAX_FILE = 100_000_000   # iMessage's own limit is about this
_imsg_sleep = time.sleep      # tests make the pauses instant
_line_state_tlock = threading.RLock()


def is_imessage_chat(chat):
    """Dot's iMessage line (a BlueBubbles chat guid, an address, or the note-to-self chat)."""
    chat = chat or ""
    return bool(chat) and not chat.startswith(("discord", "local:"))


def _addr_key(address):
    a = (address or "").strip().lower()
    digits = re.sub(r"\D", "", a)
    return digits[-10:] if "@" not in a and len(digits) >= 10 else a


def _line_state_path():
    return DOTS_DIR / "line_state.json"


def _line_state_read():
    try:
        return json.loads(_line_state_path().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


@contextlib.contextmanager
def _line_state():
    """line_state.json for a read-change-write, locked across processes (jobs text too)."""
    path = _line_state_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    with _line_state_tlock:
        fh = open(DOTS_DIR / "line_state.lock", "a+b")
        locked = False
        try:
            deadline = time.time() + 5
            while not locked:
                try:
                    if sys.platform == "win32":
                        import msvcrt
                        fh.seek(0)
                        msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
                    else:
                        import fcntl
                        fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    locked = True
                except OSError:
                    if time.time() > deadline:
                        break  # go on without it rather than hang a send
                    time.sleep(0.02)
            readable = True
            try:
                st = json.loads(path.read_text(encoding="utf-8"))
            except FileNotFoundError:
                st = {}
            except (OSError, ValueError):
                st, readable = {}, False  # never overwrite a file we couldn't read
            before = json.dumps(st, sort_keys=True)
            yield st
            if readable and json.dumps(st, sort_keys=True) != before:
                _write_json(path, st)
        finally:
            if locked:
                try:
                    if sys.platform == "win32":
                        import msvcrt
                        fh.seek(0)
                        msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
                    else:
                        import fcntl
                        fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
            fh.close()


_URL_RE = re.compile(r"https?://[^\s<>()\"']+(?:\([^\s<>()]*\)[^\s<>()\"']*)*")


def imessage_text(text):
    """Dot's Discord-style text -> clean iMessage text: no markdown (bold, headers,
    code fences, quotes, tables), "[words](url)" as words plus the link, Discord
    emoji/mentions dropped. Links, emoji, file paths and snake_case come through as is."""
    t = (text or "").replace("\r\n", "\n")
    urls = []  # pieces kept exactly as they are (links, drafts), put back at the end

    def keep(s):
        urls.append(s)
        return f"\x00{len(urls) - 1}\x00"
    # A fenced block (an email draft) becomes its own bubble, word for word: fences go, what's inside stays.
    t = re.sub(r"(?ms)^[ \t]*```[^\n]*\n(.*?)^[ \t]*```[ \t]*\n?",
               lambda m: "\n\n" + keep(re.sub(r"\n[ \t]*\n+", "\n", m.group(1).strip("\n"))) + "\n\n", t)
    t = re.sub(r"(?m)^[ \t]*```[^\n]*\n?", "", t)  # one left open
    t = re.sub(r"(?m)^\.[ \t]+(?=\S)", "", t)       # ". ok to go ahead?" after a block
    def md_link(m):
        label, url = m.group(1).strip(), m.group(2)
        bare = re.sub(r"^https?://(www\.)?", "", url).rstrip("/").lower()
        if label.rstrip("/").lower() in (url.rstrip("/").lower(), bare):
            return url
        whole = (m.start() == 0 or t[m.start() - 1] == "\n") and (m.end() == len(t) or t[m.end()] == "\n")
        return f"{label}: {url}" if whole else f"{label} ({url})"
    t = re.sub(r"\[([^\]\n]{1,200})\]\((https?://[^\s)]+)\)", md_link, t)
    t = re.sub(r"<(https?://[^>\s]+)>", r"\1", t)  # Discord's no-preview links
    t = re.sub(r"<a?:\w+:\d+>", "", t)               # custom emoji
    t = re.sub(r"<[@#][!&]?\d+>", "", t)            # mentions
    t = re.sub(r"<t:(\d+)(:\w)?>", lambda m: _clock(int(m.group(1))), t)  # timestamps
    t = _URL_RE.sub(lambda m: keep(m.group(0)), t)  # links are never touched by what follows
    t = re.sub(r"\\([*_~`|>#])", lambda m: keep(m.group(1)), t)  # Discord's \* is a real *
    t = re.sub(r"`([^`\n]+)`", r"\1", t)
    t = re.sub(r"(?m)^[ \t]{0,3}#{1,6}[ \t]+(.+?)[ \t#]*$", r"\1", t)
    t = re.sub(r"(?m)^[ \t]*>[ \t]?", "", t)
    t = re.sub(r"(?m)^[ \t]*([-*_])([ \t]*\1){2,}[ \t]*$\n?", "", t)  # --- rules
    t = re.sub(r"(?m)^([ \t]*)[-*+][ \t]+(?=\S)", lambda m: ("  " if len(m.group(1)) >= 2 else "") + "• ", t)
    def table_row(m):
        row = m.group(0).strip()
        if re.fullmatch(r"\|?[\s:|-]+\|?", row):
            return "\x01"
        return " · ".join(c.strip() for c in row.strip("|").split("|") if c.strip())
    t = re.sub(r"(?m)^[ \t]*\|.*\|[ \t]*$", table_row, t)
    t = re.sub(r"\x01\n?", "", t)
    t = re.sub(r"\*\*(?=\S)(.+?)(?<=\S)\*\*", r"\1", t)
    t = re.sub(r"(?<!\w)__(?=\S)(.+?)(?<=\S)__(?!\w)", r"\1", t)
    t = re.sub(r"(?<![\w*])\*(?=[^\s*])([^*\n]+?)(?<=[^\s*])\*(?![\w*])", r"\1", t)
    t = re.sub(r"(?<![\w\\])_(?=[^\s_])([^_\n]+?)(?<=[^\s_])_(?!\w)", r"\1", t)
    t = re.sub(r"~~(?=\S)(.+?)(?<=\S)~~", r"\1", t)
    t = re.sub(r"\|\|(.+?)\|\|", r"\1", t)
    t = re.sub(r"\x00(\d+)\x00", lambda m: urls[int(m.group(1))], t)
    t = re.sub(r"[ \t]+\n", "\n", t)
    t = re.sub(r"\n{3,}", "\n\n", t)
    return t.strip()


_YES_LABELS = {"yes", "go ahead", "send it", "do it", "ok", "okay", "approve", "yep", "sure"}
_NO_LABELS = {"no", "don't", "dont", "skip", "skip it", "cancel", "nope", "not now"}


def _plain_label(label):
    return re.sub(r"\s+", " ", re.sub(r"[^\w\s'’]", "", str(label or "").lower())).replace("’", "'").strip()


def imessage_menu(components, body=""):
    """Discord buttons and pick lists, for a text: (the line to add, [[label, custom_id]]
    that "1", "2", ... picks, True if it's a plain yes/no). Yes/no needs no menu: a
    texted "yes"/"no" already answers it."""
    picks, links = [], []
    for row in components or []:
        for c in (row or {}).get("components") or []:
            label = re.sub(r"\s+", " ", str(c.get("label") or "")).strip()
            if c.get("type") == 2 and c.get("url"):
                links.append((label or "link", c["url"]))
            elif c.get("type") == 2 and c.get("custom_id") and label:
                picks.append([label, c["custom_id"]])
            elif c.get("type") == 3:
                for o in c.get("options") or []:
                    picks.append([str(o.get("label") or o.get("value")), f"{c.get('custom_id')}={o.get('value')}"])
    lines = [f"{label}: {url}" for label, url in links]
    yesno = (len(picks) == 2 and _plain_label(picks[0][0]) in _YES_LABELS
             and _plain_label(picks[1][0]) in _NO_LABELS)
    if yesno:
        picks = []
        if not (body or "").rstrip().endswith("?"):
            lines.append("(yes or no?)")
    elif len(picks) == 1:
        lines.append(f"(text 1 to {_plain_label(picks[0][0])})")
    elif picks:
        words = [f"{i} to {_plain_label(label)}" for i, (label, _cid) in enumerate(picks[:9], 1)]
        picks = picks[:9]
        lines.append("text " + ", ".join(words[:-1]) + ("," if len(words) > 2 else "") + " or " + words[-1])
    return "\n".join(lines), picks, yesno


def imessage_bubbles(text, limit=IMSG_MAX_BUBBLES):
    """A reply as a few texts, the way a person sends them: short ones stay whole;
    longer ones break between paragraphs (a lead-in ending in ":" stays with what
    follows, lists stay together), long paragraphs between sentences; never more
    than `limit` bubbles (neighbours merge). Nothing is cut or dropped."""
    text = (text or "").strip()
    if not text:
        return []
    if len(text) <= 320 and "\n\n" not in text:
        return [text]
    pieces = []
    for p in re.split(r"\n[ \t]*\n", text):
        p = p.strip()
        if p:
            pieces += _split_text(p, 700) if len(p) > 900 else [p]
    out = []
    for p in pieces:
        if out and (out[-1].endswith(":") or len(out[-1]) < 40):
            out[-1] += ("\n" if out[-1].endswith(":") else "\n\n") + p
        else:
            out.append(p)
    while len(out) > limit:
        i = min(range(len(out) - 1), key=lambda k: len(out[k]) + len(out[k + 1]))
        out[i:i + 2] = [out[i] + "\n\n" + out[i + 1]]
    return out


def _update_gap(dot):
    """Time between progress texts while a job works: Discord likes lots; a phone
    buzzing every few seconds doesn't, so iMessage gets one every 2 minutes at most."""
    return IMSG_UPDATE_GAP_SEC if is_imessage_chat(getattr(dot, "reply_to", "")) else UPDATE_GAP_SEC


def _last_text_to(dot):
    """When anything (the quick reply, another job) last texted this job's iMessage chat; 0 on Discord."""
    chat = getattr(dot, "reply_to", "")
    if not is_imessage_chat(chat):
        return 0
    chat = line.chat_guid(chat)
    return max([s.get("t", 0) for s in _line_state_read().get("sent") or [] if s.get("chat") == chat] or [0])


def _progress_kept(dot, held):
    """Progress lines held back by that gap, still worth sending: only ones with a link, a question or an FYI
    (the rest is stale "ok doing X", and on Discord it turned the answer into a wall, 2026-11-09)."""
    return [h for h in held if _URL_RE.search(h) or "?" in h or "you're away" in h]


_YESNO_Q_RE = re.compile(r"\b(ok|okay|should i|want me|go ahead|keep going|send it|sounds? good|that work|"
                         r"yes or no)\b[^\n]*\?\s*$", re.I)


def _imsg_quiet(now=None):
    hours = settings().get("line_quiet_hours") or IMSG_QUIET_HOURS
    start, end = int(hours[0]), int(hours[1])
    h = datetime.datetime.fromtimestamp(now or _now()).hour
    return (h >= start or h < end) if start > end else (start <= h < end)


def _norm_key(text):
    t = re.sub(r"\W+", " ", (text or "").lower()).strip()
    return hashlib.sha1((t or (text or "")).encode("utf-8")).hexdigest()[:16]


class _LineSlow(RuntimeError):
    """The Mac got the request but answered late: a send probably went, so it's never retried."""


class DotLine:
    def __init__(self):
        self.seen_after = int(_now() * 1000)
        self._started = self.seen_after
        self._floor = self.seen_after  # nothing from before this start (unless resuming saved state)
        self._resumed = False
        self._seen_guids = set()
        self._recent_texts = []
        self._papi = (0.0, False)

    @staticmethod
    def creds():
        s = sc()
        return s._secret_get(_LINE_URL), s._secret_get(_LINE_PW)

    def connected(self):
        if self.self_mode():
            return bool(self.self_chat()) and sc().imessage_connected()
        url, pw = self.creds()
        return bool(url and pw)

    def _call(self, method, path, timeout=20, raw=False, **kw):
        import requests
        if self.self_mode() and not raw:  # the user's own BlueBubbles
            try:
                return sc()._bluebubbles(method, path, timeout=timeout, **kw)
            except Exception as e:
                if type(e).__name__ == "_IMsgSlow":
                    raise _LineSlow(str(e)) from None
                raise
        url, pw = self.creds()
        if not url or not pw:
            raise RuntimeError("Dot's iMessage line isn't connected")
        try:
            r = requests.request(method, url.rstrip("/") + "/api/v1" + path, params={"password": pw},
                                 timeout=timeout, **kw)
        except requests.exceptions.ReadTimeout:
            raise _LineSlow("Dot's Mac took too long to answer") from None
        except requests.exceptions.RequestException:
            raise RuntimeError("Can't reach Dot's BlueBubbles server on the Mac") from None  # URL holds the password
        if r.status_code == 401:
            raise RuntimeError("Dot's BlueBubbles server turned down the password")
        if raw:
            if not r.ok:
                raise RuntimeError(f"Dot's line: {r.status_code}")
            return r
        body = r.json() if r.content else {}
        if not r.ok:
            raise RuntimeError(f"Dot's line: {body.get('message') or r.status_code}")
        return body.get("data")

    @staticmethod
    def _allowed(address):
        allowed = {a.strip().lower() for a in settings().get("line_allowed", []) if a.strip()}
        a = (address or "").strip().lower()
        digits = re.sub(r"\D", "", a)
        return a in allowed or (len(digits) >= 10 and any(re.sub(r"\D", "", x).endswith(digits[-10:])
                                                         for x in allowed if re.sub(r"\D", "", x)))

    def chat_guid(self, to, st=None):
        """Where a text to `to` goes: a chat guid as is; an address -> the chat its texts
        came from (macOS 26 names them "any;-;<address>", which is also the fallback)."""
        to = (to or "").strip()
        if self.self_mode():
            return self.self_chat()
        if ";" in to:
            return to
        chats = (st if st is not None else _line_state_read()).get("chats") or {}
        return chats.get(_addr_key(to)) or f"any;-;{to}"

    # -- reading ---------------------------------------------------------------
    def _resume(self):
        """After a restart, carry on from the last check (up to 30 minutes back), so a
        text sent while Dot restarted still gets answered, and none twice."""
        if self._resumed:
            return
        self._resumed = True
        saved = int(_line_state_read().get("seen_after") or 0)
        if saved:
            self.seen_after = max(saved, int((_now() - PENDING_REPLAY_SEC) * 1000))
            self._floor = self.seen_after - IMSG_OVERLAP_MS

    def poll(self):
        """New texts to Dot from allowed people: [(address, chat_guid, text, files, guid)].
        BlueBubbles' "after" includes the newest message again, so each message guid is
        handed over once, across restarts too. Tapbacks only count as a yes/no on the
        question Dot just asked."""
        if self.self_mode():
            return self._poll_self()
        self._resume()
        msgs = self._call("POST", "/message/query", json={
            "after": max(0, self.seen_after - IMSG_OVERLAP_MS), "limit": 100, "sort": "ASC",
            "with": ["chat", "handle", "attachment"]}) or []
        out, now = [], _now()
        with _line_state() as st:
            seen = list(st.get("guids") or [])
            known = set(seen)
            for m in msgs:
                created = int(m.get("dateCreated") or 0)
                self.seen_after = max(self.seen_after, created)
                guid = m.get("guid") or ""
                if m.get("isFromMe") or not guid or guid in known:
                    continue
                address = (m.get("handle") or {}).get("address", "")
                if not self._allowed(address):  # people other than them aren't Dot's
                    continue
                known.add(guid)
                seen.append(guid)
                chats = m.get("chats") or []
                chat = (chats[0].get("guid") if chats else "") or self.chat_guid(address, st)
                st.setdefault("chats", {})[_addr_key(address)] = chat
                if created and created < self._floor:
                    continue  # from before this start: the last run already had it
                if m.get("associatedMessageType"):
                    answer = self._tapback_answer(m, chat, st)
                    if answer:
                        out.append((address, chat, answer, [], guid))
                    continue
                st.setdefault("last_in", {})[chat] = now
                text = (m.get("text") or "").replace("\ufffc", "").strip()  # an attachment's placeholder
                if text or m.get("attachments"):
                    out.append((address, chat, text, m.get("attachments") or [], guid))
            st["guids"] = seen[-500:]
            st["seen_after"] = self.seen_after
        got = []
        for address, chat, text, atts, guid in out:  # downloads happen outside the lock
            files = self._download(atts) if atts else []
            if text or files:
                got.append((address, chat, text, files, guid))
        return got

    @staticmethod
    def _tapback_answer(m, chat, st):
        kind = m.get("associatedMessageType")
        kind = {2000: "love", 2001: "like", 2002: "dislike"}.get(kind, kind) if isinstance(kind, int) else str(kind)
        emoji = m.get("associatedMessageEmoji") or ""
        target = re.sub(r"^(p:\d+/|bp:)", "", m.get("associatedMessageGuid") or "")
        ask = (st.get("asks") or {}).get(chat) or {}
        if not target or target not in (ask.get("guids") or []) or _now() - ask.get("t", 0) > QUESTION_TIMEOUT_SEC:
            return None
        if kind in ("like", "love") or emoji in ("👍", "❤️", "✅", "👌"):
            answer = "yes"
        elif kind == "dislike" or emoji in ("👎", "❌"):
            answer = "no"
        else:
            return None
        if not any(t.status == "waiting" and t.reply_to == chat for t in all_dots()):
            return None
        ask["guids"] = []  # one answer per question
        return answer

    def _download(self, attachments):
        """Photos, voice memos and files they texted Dot, saved so it can look at them.
        BlueBubbles hands HEIC photos over as JPEG."""
        out = []
        folder = DOTS_DIR / "received"
        types = {"image/jpeg": ".jpg", "image/png": ".png", "image/gif": ".gif", "image/heic": ".heic",
                 "audio/mpeg": ".mp3", "audio/mp3": ".mp3", "audio/x-caf": ".caf", "audio/mp4": ".m4a",
                 "video/mp4": ".mp4", "video/quicktime": ".mov", "application/pdf": ".pdf"}
        for a in attachments[:10]:
            try:
                if not a.get("guid") or int(a.get("totalBytes") or 0) > 50_000_000:
                    continue
                r = self._call("GET", f"/attachment/{a['guid']}/download", timeout=90, raw=True)
                name = re.sub(r"[^\w.\-]", "_", a.get("transferName") or "file")
                ext = types.get((r.headers.get("content-type") or "").split(";")[0].strip().lower())
                if ext and not name.lower().endswith(ext):
                    name = os.path.splitext(name)[0] + ext
                folder.mkdir(parents=True, exist_ok=True)
                path = folder / f"{time.strftime('%m%d-%H%M%S')}-{name}"
                path.write_bytes(r.content)
                out.append(str(path))
            except Exception as e:
                print(f"[line attachment] {e}", file=sys.stderr)
        return out

    # -- what it can do beyond texting (Private API only) --------------------------
    def private_api(self):
        """True when BlueBubbles' Private API is on and its helper connected (tapbacks,
        typing). Asked at most every 10 minutes; off when the Mac can't be reached."""
        if self.self_mode():
            return False
        at, on = self._papi
        if _now() - at < 600:
            return on
        try:
            info = self._call("GET", "/server/info", timeout=8) or {}
            on = bool(info.get("private_api") and info.get("helper_connected"))
        except Exception:
            on = False
        self._papi = (_now(), on)
        return on

    def react(self, chat, msg_guid, reaction):
        """Tapback on one of their texts: like / love / emphasize / question / laugh / dislike."""
        if not msg_guid or not is_imessage_chat(chat) or not self.private_api():
            return False
        try:
            self._call("POST", "/message/react", timeout=20, json={
                "chatGuid": self.chat_guid(chat), "selectedMessageGuid": str(msg_guid),
                "reaction": reaction, "partIndex": 0})
            return True
        except Exception as e:
            print(f"[line react] {e}", file=sys.stderr)
            return False

    def typing(self, chat, on=True):
        if not is_imessage_chat(chat) or not self.private_api():
            return False
        import urllib.parse
        try:
            self._call("POST" if on else "DELETE",
                       f"/chat/{urllib.parse.quote(self.chat_guid(chat), safe='')}/typing", timeout=10)
            return True
        except Exception:
            return False

    # -- texting ---------------------------------------------------------------
    def send(self, to, text, files=(), components=None, _held=False):
        """Text them like a person: plain text, a few bubbles with small pauses, buttons
        as options they text back, files as attachments. Never the same text twice
        with nothing from them in between, and nothing unprompted in quiet hours
        (held for the morning, or until they text)."""
        chat = self.chat_guid(to)
        body = imessage_text(text)
        menu, picks, yesno = imessage_menu(components, body)
        files = list(dict.fromkeys(str(f) for f in files or () if f))
        if not body and not menu and not files:
            return
        with _line_state() as st:
            if not _held and self._hold(st, chat, body, files):
                return
            if body and not files and self._repeat(st, chat, body):
                print(f"[line] not sending the same text twice: {body[:60]}", file=sys.stderr)
                return
        full = (body + "\n" + menu).strip() if menu else body
        bubbles = imessage_bubbles(full)
        guids, notes = [], []
        try:
            for i, piece in enumerate(bubbles):
                if i:
                    self._pause(chat, piece)
                guids.append(self._send_bubble(chat, piece))
            for f in files:
                note = self._send_file(chat, f)
                if note:
                    notes.append(note)
            if notes:
                guids.append(self._send_bubble(chat, "\n".join(notes)))
        finally:
            if guids:
                with _line_state() as st:
                    st["sent"] = ([s for s in st.get("sent") or [] if _now() - s.get("t", 0) < IMSG_DUP_SEC]
                                  + [{"chat": chat, "k": _norm_key(body), "t": _now()}])[-50:]
                    if picks:
                        st.setdefault("menus", {})[chat] = {"t": _now(), "options": picks}
                    if yesno or (bubbles and _YESNO_Q_RE.search(bubbles[-1])):
                        st.setdefault("asks", {})[chat] = {"guids": [g for g in guids if g], "t": _now()}

    def _hold(self, st, chat, body, files):
        if self.self_mode() or not _imsg_quiet() or _now() - (st.get("last_in") or {}).get(chat, 0) < IMSG_AWAKE_SEC:
            return False
        held = st.get("held") or []
        if not any(h["chat"] == chat and h["text"] == body for h in held) or files:
            held.append({"chat": chat, "text": body, "files": files, "t": _now()})
        st["held"] = held[-15:]
        return True

    @staticmethod
    def _repeat(st, chat, body):
        key, since = _norm_key(body), (st.get("last_in") or {}).get(chat, 0)
        return any(s.get("chat") == chat and s.get("k") == key and _now() - s.get("t", 0) < IMSG_DUP_SEC
                   and s.get("t", 0) > since for s in st.get("sent") or [])

    def flush_held(self):
        """Texts held overnight go out once it's morning (or once they text): one message
        per chat, oldest first, repeats left out."""
        with _line_state() as st:
            held = st.get("held") or []
            if not held:
                return 0
            quiet = _imsg_quiet()
            awake = lambda c: _now() - (st.get("last_in") or {}).get(c, 0) < IMSG_AWAKE_SEC
            ready = [h for h in held if not quiet or awake(h["chat"])]
            if not ready:
                return 0
            st["held"] = [h for h in held if h not in ready]
        for chat in dict.fromkeys(h["chat"] for h in ready):
            mine = [h for h in ready if h["chat"] == chat]
            texts = list(dict.fromkeys(h["text"] for h in mine if h["text"]))
            files = [f for h in mine for f in h.get("files") or []]
            lead = "" if quiet else "while you were asleep:\n"
            try:
                self.send(chat, lead + "\n\n".join(texts), files, _held=True)
            except Exception as e:  # the Mac is away: they wait for the next try
                print(f"[line held] {e}", file=sys.stderr)
                with _line_state() as st:
                    st["held"] = (mine + (st.get("held") or []))[-15:]
                return 0
        return len(ready)

    def _pause(self, chat, next_piece):
        """A beat between bubbles, longer for a longer one (with "typing…" when it can)."""
        self.typing(chat)
        _imsg_sleep(min(2.5, 0.7 + len(next_piece) / 160))

    def _send_bubble(self, chat, piece):
        """One text. Returns its guid ("" if unknown). A late answer is taken as sent."""
        if self.self_mode():
            piece = SELF_TAG + piece  # tells Dot's replies apart from the user's own notes
        try:
            data = self._call("POST", "/message/text", timeout=45, json={
                "chatGuid": chat, "tempGuid": f"temp-{uuid.uuid4()}", "message": piece, "method": "apple-script"})
        except _LineSlow:
            return ""
        return (data or {}).get("guid", "") if isinstance(data, dict) else ""

    def _send_file(self, chat, path):
        """One attachment (AppleScript, no Private API needed). Returns a note to text
        instead when it can't go."""
        p = Path(path)
        try:
            size = p.stat().st_size
        except OSError:
            return ""
        if not size:
            return ""
        if size > IMSG_MAX_FILE:
            return f"({p.name} is too big to text, it's on the PC at {p})"
        try:
            with open(p, "rb") as h:
                self._call("POST", "/message/attachment", timeout=180, data={
                    "chatGuid": chat, "tempGuid": f"temp-{uuid.uuid4()}", "name": p.name,
                    "method": "apple-script"}, files={"attachment": (p.name, h)})
            return ""
        except _LineSlow:
            return ""
        except Exception as e:
            print(f"[line file] {e}", file=sys.stderr)
            return f"(couldn't attach {p.name}, it's on the PC at {p})"

    # -- note-to-self mode: the user's own iCloud, one chat only -------------
    # The user texts their own number/Apple ID. Only that chat is fetched from
    # the Mac (GET /chat/<guid>/message), so no other text ever leaves it.
    @staticmethod
    def self_mode():
        return settings().get("line_mode") == "self"

    @staticmethod
    def self_chat():
        return settings().get("self_chat", "")

    def _poll_self(self):
        import urllib.parse
        chat = self.self_chat()
        msgs = sc()._bluebubbles("GET", f"/chat/{urllib.parse.quote(chat, safe='')}/message", params={
            "after": self.seen_after, "limit": 50, "sort": "ASC"}) or []
        out = []
        for m in msgs:
            self.seen_after = max(self.seen_after, m.get("dateCreated") or 0)
            text = (m.get("text") or "").strip()
            if (not text or m.get("associatedMessageType") or text.startswith(SELF_TAG.strip())
                    or (m.get("dateCreated") or 0) <= self._started):
                continue
            # A note to self arrives twice (sent + received); take each text once.
            key = m.get("guid") or text
            if key in self._seen_guids:
                continue
            self._seen_guids.add(key)
            when = (m.get("dateCreated") or 0) / 1000
            if any(t == text and abs(when - w) < 15 for t, w in self._recent_texts):
                continue  # the second copy of the same note
            self._recent_texts = (self._recent_texts + [(text, when)])[-20:]
            out.append(("me", chat, text, [], None))
        return out


line = DotLine()


def imessage_tick():
    """One check of Dot's line (the daemon's iMessage loop): new texts join the same
    queue as Discord's, so bursts merge and texts are handled in order; texts held
    overnight go out when it's time. A restart mid-reply replays them (pending.json)."""
    for address, chat, text, files, guid in line.poll():
        if guid:
            if not _first_time(guid):
                continue
            pending_add(guid, chat, text, address)
        gateway.incoming.put((address, chat, text, list(files or ()), guid))
    line.flush_held()


_imsg_loop_on = [False]


def imessage_loop():
    """Dot's iMessage line, every 2 s (the Discord loop used to poll it every 30 s)."""
    _imsg_loop_on[0] = True
    failing, wait = False, IMSG_POLL_SEC
    while True:
        try:
            if line.connected():
                imessage_tick()
            failing, wait = False, IMSG_POLL_SEC
        except Exception as e:
            if not failing:
                print(f"[DotLine] {e}", file=sys.stderr)
            failing, wait = True, min(30, wait * 2)  # the Mac is asleep or away: back off
        time.sleep(wait)


def _save_outgoing(name, data):
    """A picture or file made for a text (screenshot, replay), saved so it can be attached."""
    folder = DOTS_DIR / "sent" / f"{time.strftime('%m%d-%H%M%S')}-{uuid.uuid4().hex[:4]}"  # the name is what they see
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / re.sub(r"[^\w.-]", "_", name)
    path.write_bytes(data)
    return str(path)


def _imsg_pick(chat, text):
    """"2" (or an option's words) after a "text 1, 2 or 3" menu. Returns True when it
    was handled here, the option's words to handle as their text, or None."""
    low = _plain_label(text)
    if not low:
        return None
    with _line_state() as st:
        menu = (st.get("menus") or {}).get(chat)
        if not menu or _now() - menu.get("t", 0) > IMSG_MENU_SEC:
            return None
        opts = menu.get("options") or []
        m = re.fullmatch(r"(?:no |number |option )?(\d{1,2})", low)
        if m:
            n = int(m.group(1))
            pick = opts[n - 1] if 1 <= n <= len(opts) else None
        else:  # their words for an option; a plain "stop" still stops everything
            pick = None if re.match(STOP_RE, low) else next((o for o in opts if _plain_label(o[0]) == low), None)
        if pick is None:
            return None
        st["menus"].pop(chat, None)
    return _imsg_choose(chat, *pick)


def _imsg_choose(chat, label, cid):
    """What a Discord button does, for its texted number. Buttons that need Discord
    (mail cards, reminders...) come back as their words, as if typed."""
    kind, _, rest = (cid or "").partition(":")
    if kind == "ok":
        dot_id, ans, qid = (rest.split(":") + ["", ""])[:3]
        dot = load_dot(dot_id)
        if not dot or dot.asking != "ok" or (qid and dot.qid and qid != dot.qid):
            say_to(chat, "that one's old, it isn't waiting on that anymore")
            return True
        dot.add_message("you", "yes" if ans == "y" else "no")
        _update(dot, answer="yes" if ans == "y" else "no")
        return True
    if kind == "ans":
        dot_id, qid, text = (rest.split(":", 2) + ["", ""])[:3]
        dot = load_dot(dot_id)
        if not dot or dot.status != "waiting" or dot.asking != "question" or qid != dot.qid:
            say_to(chat, "that one's old, it isn't waiting on that anymore")
            return True
        dot.add_message("you", text)
        dot.push_followup(text)
        _update(dot, status="queued", question=None, asking="", answer=None, next_run=_now(),
                runs_this_goal=0, wait_wakes=0)
        _wake.set()
        return True
    if kind == "more":
        dot_id, _, how = rest.partition(":")
        dot = load_dot(dot_id)
        if not dot or dot.status == "working":
            return True
        if dot.status == "stopped":
            say_to(chat, "that one's stopped. tell me if you want it started again")
            return True
        dot.push_followup("That approach wasn't working. Try a different way." if how == "other"
                          else "Keep going and finish it.")
        _update(dot, force=True, status="queued", next_run=_now(), question=None, asking="",
                answer=None, runs_this_goal=0)
        _wake.set()
        say_to(chat, "on it 👍")
        return True
    if kind == "stop":
        dot = load_dot(rest)
        if dot and dot.status in ACTIVE:
            kill_task(dot.id)
        say_to(chat, f"ok, stopped {dot.label or dot.name}" if dot else "ok, stopped")
        return True
    if kind == "say":
        return rest.partition(":")[2] or label
    return label


# --- Dot in Discord DMs --------------------------------------------------------
# The same bot Period already uses ("connect discord"). Dot reads only its
# DM channel with the user (found once by `connect-discord`), so nobody else
# can give it jobs, and it never reads server channels after setup.

def _snowflake_age(snowflake):
    """Seconds since a Discord id was made (ids carry their creation time)."""
    try:
        return _now() - ((int(snowflake) >> 22) + 1420070400000) / 1000
    except (TypeError, ValueError):
        return float("inf")


class DotDiscord:
    def __init__(self):
        self.last_id = None

    @staticmethod
    def dm():
        return settings().get("discord_dm", "")

    def connected(self):
        try:
            return bool(self.dm()) and sc().discord_connected()
        except Exception:
            return False

    def poll(self):
        dm = self.dm()
        if self.last_id is None:
            # Pick up what was sent while Dot was off (up to an hour back), but
            # don't redo older history the first time.
            saved = settings().get("discord_last_id")
            if saved and _snowflake_age(saved) < 3600:
                self.last_id = saved
            else:
                latest = sc()._discord("GET", f"/channels/{dm}/messages", params={"limit": 1}) or []
                self.last_id = latest[0]["id"] if latest else "0"
                self._save_last()
                return []
        msgs = sc()._discord("GET", f"/channels/{dm}/messages", params={"after": self.last_id, "limit": 50}) or []
        if msgs:
            self.last_id = max((m["id"] for m in msgs), key=int)
            self._save_last()
        out = []
        for m in sorted(msgs, key=lambda m: int(m["id"])):
            author = m.get("author") or {}
            text = (m.get("content") or "").strip()
            if (text or m.get("attachments")) and not author.get("bot") \
                    and author.get("id") == settings().get("discord_user") and _first_time(m["id"]):
                pending_add(m["id"], "discord:" + dm, text)
                out.append(("discord", "discord:" + dm, text, _download_attachments(m), m["id"]))
        return out

    def _save_last(self):
        st = settings()
        st["discord_last_id"] = self.last_id
        save_settings(st)

    def send(self, dm, text, files=(), components=None, reply_to=None, _gated=False):
        dm = dm.split(":", 1)[-1] if dm.startswith("discord:") else (dm if dm not in ("", "discord") else self.dm())
        if reply_to and not str(reply_to).isdigit():
            reply_to = None  # a replayed or local text has no Discord message to reply to
        if not _gated and dm and dm == self.dm():
            text = _gate_discord(text, files, components, asked=True if reply_to else None)
            if text is None:
                return
        chunks = _split_text(text, 1900)
        for n, chunk in enumerate(chunks):
            last = n == len(chunks) - 1
            if n == 0 and reply_to and not files and not components:
                # Shown in Discord as a reply to their message (no ping, and still sent
                # if that message was deleted).
                sc()._discord("POST", f"/channels/{dm}/messages", json={
                    "content": chunk, "allowed_mentions": {"replied_user": False},
                    "message_reference": {"message_id": str(reply_to), "fail_if_not_exists": False}})
                if last:
                    return
                continue
            if last and components:
                _live().post(dm, chunk, files=files, components=components, gated=True)
            elif last and files:
                # Pictures and files ride on the last message (up to 10, Discord's limit).
                handles = []
                try:
                    up = {}
                    for i, f in enumerate(list(files)[:10]):
                        h = open(f, "rb")
                        handles.append(h)
                        up[f"files[{i}]"] = (Path(f).name, h)
                    sc()._discord("POST", f"/channels/{dm}/messages",
                                  data={"payload_json": json.dumps({"content": chunk})}, files=up)
                finally:
                    for h in handles:
                        h.close()
            elif chunk:
                sc()._discord("POST", f"/channels/{dm}/messages", json={"content": chunk})


discord = DotDiscord()
CHANNELS = (line, discord)
_seen_msg_ids = set()  # Discord message ids already handled (gateway and polling both see them)
_seen_lock = threading.Lock()


def _download_attachments(m):
    """Save what they sent (photos, files) so Dot can look at it. Returns paths."""
    import requests
    out = []
    folder = DOTS_DIR / "received"
    for a in (m.get("attachments") or [])[:10]:
        try:
            if int(a.get("size") or 0) > 50_000_000:
                continue
            folder.mkdir(parents=True, exist_ok=True)
            name = re.sub(r"[^\w.\-]", "_", a.get("filename") or "file")
            path = folder / f"{time.strftime('%m%d-%H%M%S')}-{name}"
            r = requests.get(a["url"], timeout=60)
            r.raise_for_status()
            path.write_bytes(r.content)
            out.append(str(path))
        except Exception as e:
            print(f"[attachment] {e}", file=sys.stderr)
    return out


# Texts that arrived but aren't fully handled yet. Discord's "last seen" moves on as soon as a text
# arrives, so without this a restart mid-reply lost it for good (Oct 21: an email request and a
# Google Sheets request). Startup replays what's left.
PENDING_REPLAY_SEC = 30 * 60
_pending_lock = threading.Lock()


def _pending_path():
    return DOTS_DIR / "pending.json"


def _pending_read():
    try:
        return json.loads(_pending_path().read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return {}


def pending_add(msg_id, chat, text, address="discord"):
    if not msg_id:
        return
    with _pending_lock:
        p = _pending_read()
        p[str(msg_id)] = {"chat": chat, "text": text, "address": address, "t": _now()}
        _write_json(_pending_path(), p)


def pending_merge(old_id, new_id, text):
    """A burst became one text: it's now pending under the newest id only."""
    with _pending_lock:
        p = _pending_read()
        if str(new_id) in p:
            p.pop(str(old_id), None)
            p[str(new_id)]["text"] = text
            _write_json(_pending_path(), p)


def pending_done(msg_id):
    if not msg_id:
        return
    with _pending_lock:
        p = _pending_read()
        if p.pop(str(msg_id), None) is not None:
            _write_json(_pending_path(), p)


def replay_pending():
    """At startup: texts a restart cut off get handled now; ones over 30 minutes old are dropped."""
    with _pending_lock:
        p = _pending_read()
        _write_json(_pending_path(), {})
    redo = sorted(((k, v) for k, v in p.items() if _now() - v.get("t", 0) < PENDING_REPLAY_SEC),
                  key=lambda kv: kv[1]["t"])
    for msg_id, v in redo:
        _first_time(msg_id)  # polling won't hand it over a second time
        pending_add(msg_id, v["chat"], v["text"], v.get("address", "discord"))
        enqueue(v.get("address", "discord"), v["chat"], v["text"], (), msg_id)
    return len(redo)


def _first_time(msg_id):
    with _seen_lock:
        if msg_id in _seen_msg_ids:
            return False
        _seen_msg_ids.add(msg_id)
        return True


class DotGateway:
    """A live connection to Discord, so the bot shows online (green dot) with
    a status saying what it's working on, and DMs arrive the moment they're sent.
    Polling (DotDiscord.poll) stays on as a fallback if this drops."""
    URL = "wss://gateway.discord.gg/?v=10&encoding=json"
    INTENTS = (1 << 12) | (1 << 15)  # direct messages + their text

    def __init__(self):
        import queue
        self.incoming = queue.Queue()
        self.connected = False
        self._ws = None
        self._send_lock = threading.Lock()
        self._seq = None
        self._activity = None

    def start(self):
        threading.Thread(target=self._run, daemon=True, name="discord-gateway").start()

    def working_on(self, name):
        self._activity = name
        self._presence()

    def _send(self, payload):
        with self._send_lock:
            if self._ws is not None:
                self._ws.send(json.dumps(payload))

    def _presence(self):
        state = f"working on: {self._activity}"[:120] if self._activity else "here if you need me"
        try:
            self._send({"op": 3, "d": {"since": None, "afk": False, "status": "online",
                                       "activities": [{"type": 4, "name": "Custom Status", "state": state}]}})
        except Exception:
            pass

    def _run(self):
        from websockets.sync.client import connect
        backoff = 2
        while True:
            token = None
            try:
                token = sc()._secret_get(sc()._DISCORD_SECRET)
            except Exception:
                pass
            if not token or not discord.dm():
                time.sleep(15)
                continue
            try:
                with connect(self.URL, max_size=None, open_timeout=20) as ws:
                    hello = json.loads(ws.recv(timeout=30))
                    interval = hello["d"]["heartbeat_interval"] / 1000
                    with self._send_lock:
                        self._ws = ws
                    self._send({"op": 2, "d": {"token": token, "intents": self.INTENTS,
                                               "properties": {"os": "windows", "browser": "dots", "device": "dots"}}})
                    alive = threading.Event()
                    threading.Thread(target=self._heartbeat, args=(interval, alive), daemon=True).start()
                    try:
                        while True:
                            msg = json.loads(ws.recv())
                            if msg.get("s") is not None:
                                self._seq = msg["s"]
                            op, t, d = msg.get("op"), msg.get("t"), msg.get("d")
                            if op == 0 and t == "READY":
                                self.connected, backoff = True, 2
                                self._presence()
                                threading.Thread(target=brand_bot, daemon=True).start()
                                threading.Thread(target=_live().register_commands, daemon=True).start()
                            elif op == 0 and t == "MESSAGE_CREATE":
                                self._on_message(d)
                            elif op == 0 and t == "INTERACTION_CREATE":
                                threading.Thread(target=_live().on_interaction, args=(d,), daemon=True).start()
                            elif op in (7, 9):  # Discord asks us to reconnect
                                break
                    finally:
                        alive.set()
            except Exception as e:
                print(f"[discord gateway] {str(e)[:120]}", file=sys.stderr)
            finally:
                self.connected = False
                with self._send_lock:
                    self._ws = None
            time.sleep(backoff)
            backoff = min(backoff * 2, 60)

    def _heartbeat(self, interval, stop):
        while not stop.wait(interval):
            try:
                self._send({"op": 1, "d": self._seq})
            except Exception:
                return

    def _on_message(self, m):
        author = m.get("author") or {}
        if m.get("channel_id") != discord.dm() or author.get("bot"):
            return
        if author.get("id") != settings().get("discord_user"):
            return
        text = (m.get("content") or "").strip()
        if (text or m.get("attachments")) and _first_time(m.get("id")):
            chat = "discord:" + discord.dm()
            pending_add(m["id"], chat, text)
            discord.last_id = max(discord.last_id or "0", m["id"], key=int)
            discord._save_last()
            if m.get("attachments"):
                # Downloads happen off this thread, so the connection never stalls on a big file.
                threading.Thread(target=lambda: self.incoming.put(
                    ("discord", chat, text, _download_attachments(m), m["id"])), daemon=True,
                    name="dot-download").start()
            elif _is_quick(text):
                # "stop" / "yes" / "no" are handled right away, not behind a slow quick-brain call.
                threading.Thread(target=_safe_handle, args=("discord", chat, text, [], m["id"]), daemon=True,
                                 name="dot-fast").start()
            else:
                self.incoming.put(("discord", chat, text, [], m["id"]))


gateway = DotGateway()

BRAND_VERSION = 1  # bump to re-apply the name and picture


def _avatar_png():
    """Dot's picture: a soft white dot on the server red, with a small glow."""
    from PIL import Image, ImageDraw, ImageFilter
    size = 512
    img = Image.new("RGB", (size, size), (140, 21, 21))
    glow = Image.new("L", (size, size), 0)
    ImageDraw.Draw(glow).ellipse((136, 136, 376, 376), fill=200)
    glow = glow.filter(ImageFilter.GaussianBlur(40))
    img.paste((255, 214, 170), (0, 0), glow)
    ImageDraw.Draw(img).ellipse((176, 176, 336, 336), fill=(255, 255, 255))
    buf = io.BytesIO()
    img.save(buf, "PNG")
    return buf.getvalue()


def brand_bot():
    """Give the bot its name and picture once (Discord limits name changes)."""
    st = settings()
    if st.get("brand_version") == BRAND_VERSION:
        return
    import base64
    try:
        body = {"avatar": "data:image/png;base64," + base64.b64encode(_avatar_png()).decode()}
        try:
            sc()._discord("PATCH", "/users/@me", json=dict(body, username="Dot"))
        except Exception:
            sc()._discord("PATCH", "/users/@me", json=body)  # name taken or changed too often
        st = settings()
        st["brand_version"] = BRAND_VERSION
        save_settings(st)
    except Exception as e:
        print(f"[brand] {e}", file=sys.stderr)


def say_to(chat, text, fallback=True):
    """Send a quick reply and keep it in the chat history, so later replies
    (and the quick brain) know it was said."""
    try:
        _conversation_for(chat).add_message("dot", text)
    except Exception:
        pass
    send_to(chat, text, fallback=fallback)


def send_to(chat, text, files=(), components=None, fallback=True):
    """Reply where the message came from: Discord DM or iMessage. "local:" chats
    (the test endpoint) are only recorded in the Dot's chat. fallback=False: when
    the Mac can't be reached, raise instead of repeating it on Discord."""
    if chat.startswith("local:"):
        return
    if chat.startswith("discord:") or chat == "discord":
        discord.send(chat, text, files, components)
    else:  # iMessage: plain text in a few bubbles, buttons as texted options, real attachments
        try:
            line.send(chat, text, files, components)
        except RuntimeError as e:
            # The Mac is asleep or off Wi-Fi: say it on Discord rather than not at all (2026-10-26, 2:22 PM:
            # "yo why didn't u respond", the reply was lost).
            dm = discord.dm() if fallback and "Can't reach" in str(e) else ""
            if not dm:
                raise
            discord.send("discord:" + dm, text, files, components)


# --- what reaches his phone: one gate for every Discord DM -------------------------------------------------------
# Owner 2026-11-09: "dot spams me". Nov 6-8 had 813 Dot DMs against 75 of his (about 270 a day, 260 of them between
# 11 PM and 8 AM): 216 "can't reach the Mac" / "the Mac is back" flaps, 103 live-screen cards from the
# background lane, and ~300 lane "still waiting on you" fragments asking the same five questions all night.
# Every DM to him goes through _gate_discord. A reply (he texted or tapped in the last REPLY_WINDOW_SEC, or it's a
# job he started) only loses repeats and "I can't reach my tools" claims. Anything unprompted also waits for the
# morning between 11 PM and 8 AM, skips repeats of the last 12 hours, has a daily and hourly budget, and is cut to
# a short text with the rest on "more". Urgent texts (due today or tomorrow, a security alert, a sign-in or captcha
# link) skip the night hold and the budget.
OUTBOX_PATH = DOTS_DIR / "outbox.jsonl"       # every DM decision: sent, held or dropped, and why
NIGHT_HELD_PATH = DOTS_DIR / "night_held.json"
MORE_PATH = DOTS_DIR / "more.json"
OWNER_TAP_PATH = DOTS_DIR / "owner_tap.at"     # he pressed a button: no text, but he's there
REPLY_WINDOW_SEC = 20 * 60
AWAKE_SEC = 60 * 60            # he texted in the last hour: he's up, so the night hold doesn't apply
DM_QUIET_HOURS = (23, 8)       # settings "dm_quiet_hours" overrides
PROACTIVE_PER_DAY = 12
PROACTIVE_PER_HOUR = 4
REPEAT_SEC = 12 * 3600
PROACTIVE_MAX_CHARS = 600
MORE_KEEP_SEC = 12 * 3600
SYSTEM_ALERT_PREFIXES = ("📚", "📬", "⏳", "🎓", "📋")  # texts Dot's own features send, not a job's answer
SYSTEM_REPLY_SEC = 120
MORE_RE = r"^(more|tell me more|the rest|rest of it|full (version|thing)|whole thing|show (me )?(more|the rest))[.?! ]*$"
_dm_ctx = threading.local()

_URGENT_RE = re.compile(
    r"\b(due|expires?|expiring|deadline|closes?|closing|ends?)\b[^.\n]{0,60}\b(today|tonight|tomorrow|"
    r"in \d+ ?(h|hours?|hrs?|min(ute)?s?))\b|"
    r"\b(today|tonight|tomorrow)\b[^.\n]{0,40}\b(due|deadline|interview|expires?|closes?)\b|"
    r"\binterview\b[^.\n]{0,40}\b(today|tomorrow|in \d+ ?(min(ute)?s?|hours?))\b|\(\d{1,2}h left\)|"
    r"\b(security alert|new (sign-?in|login)|password (was )?changed|fraud|unusual activity|card (was )?declined|"
    r"verification code|security code|one-?time (pass)?code)\b|"
    r"\b(sign in|sign-in|log ?in|captcha)\b[^\n]{0,120}https?://|https?://\S+[^\n]{0,80}\b(sign in|log ?in|captcha)\b",
    re.I)
# "I can't run commands from this message", "reconnect me to the VM": never true of Dot, never worth his phone.
_FALSE_ALARM_RE = re.compile(
    _NO_TOOLS_RE.pattern + r"|"
    r"\b(can'?t|cannot|unable to)\b[^.\n]{0,40}\b(from|in) (this|a) (message|turn|chat|reply|session)\b|"
    r"\b(from|in) this (message|turn|session)\b[^.\n]{0,40}\b(can'?t|cannot|no)\b|"
    r"\breconnect (me|my)\b[^.\n]{0,30}\b(vm|tools?|terminal|computer|dot pc)\b|"
    r"\b(session|chat) (that has|with) (vm|tool|terminal) access\b|"
    r"\bdon'?t have access to (dot'?s computer|the vm|my computer|the dot pc)\b|"
    r"\b(vm|tool) (tool )?doesn'?t exist in this session\b", re.I)
# Unprompted texts that are never worth a buzz: a status with nothing for him in it.
_DM_NOISE_RE = re.compile(r"(?!)")  # status lines that never need a buzz (none yet)
# A lead-in with nothing after it ("**Needs your eye**", "Waiting on you, as noted:") or an ask with no subject.
_DM_FRAGMENT_RE = re.compile(
    r"^(\W*\*\*[^*\n]{1,80}\*\*\W*|[^\n]{0,70}:\s*|"
    r"(want me to|should i|did you|can you|do you want me to|what did you want me to)\b[^?\n]{0,30}"
    r"\b(that|it|those|them|these|this|do)\b[^?\n]{0,15}\?)$", re.I)
_JARGON_SUBS = (
    (re.compile(r"^\s*re dot lane: [^:\n]+:\s*", re.I), ""),
    (re.compile(r"(?m)^\s*(transcripts|log|file|saved at|path)\s*:\s*\S*[\\/]\S*\s*$\n?", re.I), ""),
    (re.compile(r"`([^`\n]{1,80})`"), r"\1"),
    (re.compile(r"(?:[A-Za-z]:\\[^\s'\"<>()]+|\\\\wsl\$\\[^\s'\"<>()]+|(?<![\w/:])(?:~|/home/dot|/mnt/c|/tmp)/[^\s'\"<>()]*)"),
     "a file on my computer"),
    (re.compile(r"\s*\((?:job|run|dot) \d{4}-[0-9a-f]{5}\)", re.I), ""),
    (re.compile(r"\bmorning notes\b", re.I), "your to-do list"),
    (re.compile(r"\bquarantin(?:ed|e)\b", re.I), "set aside"),
    (re.compile(r"\bneeds_input\b", re.I), "needs your answer"),
    (re.compile(r"\bAUDIT_PASS\b"), "my checks"),
)


@contextlib.contextmanager
def _dm_context(**kw):
    """For the sends inside: asked=True (it answers him), urgent=True, cap=False (no "more" cut)."""
    old = dict(getattr(_dm_ctx, "kw", None) or {})
    _dm_ctx.kw = dict(old, **kw)
    try:
        yield
    finally:
        _dm_ctx.kw = old


def owner_tapped():
    """He pressed a button or sent a slash command: the replies to it are answers, not unprompted texts."""
    try:
        OWNER_TAP_PATH.write_text(str(_now()), encoding="utf-8")
    except OSError:
        pass


def _owner_seen_at():
    """When he last texted Dot's DM or pressed one of its buttons (0 if never)."""
    t = 0.0
    lid = settings().get("discord_last_id") or discord.last_id
    if lid and str(lid) != "0":
        age = _snowflake_age(lid)
        if age != float("inf"):
            t = _now() - age
    try:
        t = max(t, float(OWNER_TAP_PATH.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    return t


def _dm_quiet(now=None):
    start, end = (int(x) for x in (settings().get("dm_quiet_hours") or DM_QUIET_HOURS))
    h = datetime.datetime.fromtimestamp(now or _now()).hour
    return (h >= start or h < end) if start > end else (start <= h < end)


def _dm_norm(text):
    t = _plain(text or "").lower()
    t = re.sub(r"(?m)^\s*\(.*\)\s*$", " ", t)  # "(your mac's asleep, so this came here instead)"
    t = re.sub(r"^\s*re [^:\n]{1,80}:\s*", "", t)
    t = re.sub(r"<[^>\s]+>", " ", t)
    t = re.sub(r"https?://\S+", " link ", t)
    t = re.sub(r"[^\w\s]", " ", t)
    return re.sub(r"\s+", " ", t).strip()[:400]


def _dm_similar(a, b):
    import difflib
    if not a or not b:
        return False
    if a == b:
        return True
    if min(len(a), len(b)) < 12:
        return False
    m = difflib.SequenceMatcher(None, a, b)
    return m.real_quick_ratio() >= 0.85 and m.quick_ratio() >= 0.85 and m.ratio() >= 0.85


def _outbox(since):
    """DMs actually sent since then: [{"t", "key", "proactive", ...}]."""
    try:
        rows = OUTBOX_PATH.read_text(encoding="utf-8").splitlines()[-1500:]
    except OSError:
        return []
    out = []
    for r in rows:
        try:
            x = json.loads(r)
        except ValueError:
            continue
        if x.get("status") == "sent" and x.get("t", 0) >= since:
            out.append(x)
    return out


def _outbox_log(status, why, text, **extra):
    try:
        _rotate(OUTBOX_PATH)
        with open(OUTBOX_PATH, "a", encoding="utf-8") as f:
            f.write(json.dumps(dict({"t": _now(), "at": _stamp(), "status": status, "why": why,
                                     "key": _dm_norm(text), "text": redact(text or "")[:500]}, **extra)) + "\n")
    except Exception:
        pass


def _dejargon(text):
    for rx, sub in _JARGON_SUBS:
        text = rx.sub(sub, text)
    text = re.sub(r"[ \t]{2,}", " ", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def _more_push(rest):
    try:
        st = json.loads(MORE_PATH.read_text(encoding="utf-8"))
        stack = st if isinstance(st, list) else []
    except (OSError, ValueError):
        stack = []
    stack = [s for s in stack if _now() - s.get("t", 0) < MORE_KEEP_SEC][-4:] + [{"t": _now(), "text": rest}]
    try:
        _write_json(MORE_PATH, stack)
    except Exception:
        pass


def _more_pop():
    """The rest of the last text cut short ("" if none in the last 12 hours)."""
    try:
        stack = json.loads(MORE_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return ""
    stack = [s for s in stack if isinstance(s, dict) and _now() - s.get("t", 0) < MORE_KEEP_SEC]
    if not stack:
        return ""
    rest = stack.pop()["text"]
    try:
        _write_json(MORE_PATH, stack)
    except Exception:
        pass
    return rest


def _shorten(text, limit=PROACTIVE_MAX_CHARS):
    """(the short text, the rest): whole lines or sentences up to about `limit`, never cutting a link."""
    if len(text) <= limit:
        return text, ""
    keep, size = [], 0
    for ln in text.split("\n"):
        if keep and size + len(ln) > limit - 80:
            break
        keep.append(ln)
        size += len(ln) + 1
    short = "\n".join(keep).rstrip()
    if len(short) > limit:  # one long paragraph: cut between sentences
        parts, short = re.split(r"(?<=[.!?])\s+", short), ""
        for p in parts:
            if short and len(short) + len(p) > limit - 80:
                break
            short = (short + " " + p).strip()
        if len(short) > limit:
            cut = short.rfind(" ", 0, limit - 80)
            short = short[:cut if cut > 0 else limit - 80].rstrip(" ,;:") + "…"
    rest = text[len(short.rstrip("…")):].strip()
    return short, rest


def _gate_discord(text, files=(), components=None, asked=None, urgent=None, cap=None):
    """What may go to his DM: the text to send (maybe shortened), or None. Logs every decision in outbox.jsonl."""
    ctx = getattr(_dm_ctx, "kw", None) or {}
    asked = ctx.get("asked") if asked is None else asked
    urgent = ctx.get("urgent") if urgent is None else urgent
    cap = ctx.get("cap", True) if cap is None else cap
    text = (text or "").strip()
    if not text:
        return text if (files or components) else None
    now, seen = _now(), _owner_seen_at()
    if asked is not None:
        reply = bool(asked)
    elif text.startswith(SYSTEM_ALERT_PREFIXES):  # mail cards, deadlines, the to-do: his own
        reply = bool(seen) and now - seen < SYSTEM_REPLY_SEC  # command's answer comes back within seconds
    else:
        reply = bool(seen) and now - seen < REPLY_WINDOW_SEC
    urgent = bool(urgent) or bool(_URGENT_RE.search(text)) or text.startswith(("⏰", "⏳"))
    if _FALSE_ALARM_RE.search(_plain(text)[:800]):
        _outbox_log("dropped", "claims it can't reach its tools", text)
        return None
    if not reply:
        if _DM_NOISE_RE.search(text):
            _outbox_log("dropped", "status with nothing for him", text)
            return None
        text = _dejargon(text)
        if not components and not files and _DM_FRAGMENT_RE.match(text):
            _outbox_log("dropped", "fragment", text)
            return None
    key = _dm_norm(text)
    since = max(now - REPEAT_SEC, 0) if not reply else max(seen + 0.001, now - 30 * 60)  # replies: since his text
    if any(_dm_similar(key, x.get("key", "")) for x in _outbox(since)):
        _outbox_log("dropped", "repeat", text, proactive=not reply)
        return None
    if not reply and not urgent:
        if _dm_quiet(now) and not (seen and now - seen < AWAKE_SEC):
            _night_hold(text)
            _outbox_log("held", "overnight: goes in the morning", text, proactive=True)
            return None
        day = datetime.datetime.fromtimestamp(now).strftime("%Y-%m-%d")
        mine = [x for x in _outbox(now - 86400) if x.get("proactive")
                and datetime.datetime.fromtimestamp(x["t"]).strftime("%Y-%m-%d") == day]
        if len(mine) >= PROACTIVE_PER_DAY or sum(1 for x in mine if now - x["t"] < 3600) >= PROACTIVE_PER_HOUR:
            _outbox_log("dropped", "over today's budget of unprompted texts", text, proactive=True)
            return None
    if not reply and cap:
        short, rest = _shorten(text)
        if rest:
            _more_push(rest)
            text = short + "\n(there's more, text \"more\")"
    _outbox_log("sent", "reply" if reply else ("urgent" if urgent else "unprompted"), text, proactive=not reply)
    return text


def _night_hold(text):
    try:
        held = json.loads(NIGHT_HELD_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        held = []
    held = (held if isinstance(held, list) else [])[-40:] + [{"t": _now(), "text": text}]
    try:
        _write_json(NIGHT_HELD_PATH, held)
    except Exception:
        pass


def flush_night_held():
    """After 8 AM: what came in overnight goes out as one short text (the full texts on "more")."""
    if _dm_quiet() or not discord.connected():
        return False
    try:
        held = json.loads(NIGHT_HELD_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    NIGHT_HELD_PATH.unlink(missing_ok=True)
    held = [h for h in held if isinstance(h, dict) and _now() - h.get("t", 0) < 14 * 3600 and h.get("text")]
    if not held:
        return False
    def first_line(t):
        ln = re.sub(r"\*\*|__|^[#>\-•*\s]+", "", t.strip().split("\n", 1)[0]).strip()
        return ln if len(ln) <= 140 else ln[:137].rstrip() + "…"
    lines = [f"• {first_line(h['text'])}" for h in held[:6]]
    text = "overnight, while you were asleep:\n" + "\n".join(lines)
    _more_push("\n\n".join(h["text"] for h in held))
    text += f"\n(+{len(held) - 6} more. text \"more\" for all of it)" if len(held) > 6 else "\n(text \"more\" for the details)"
    _outbox_log("sent", "morning batch of overnight texts", text, proactive=True)
    discord.send(discord.dm(), text, _gated=True)
    return True


# A between-steps text worth their phone: it asks them something or needs them to do something.
_NEEDS_THEM_RE = re.compile(r"\?\s*$|\bhttps?://|\b(you need to|can you|could you|please|sign in|log ?in|captcha|"
                            r"your (ok|okay|answer|call|approval)|need(s)? you\b|waiting (on|for) you|tell me|"
                            r"submitted|went (out|through)|(was|were|got|been) sent|nothing (was|went|got) (sent|out))\b", re.I | re.M)
QUIET_SUMMARY_GAP_SEC = 3 * 3600   # a background job's "what went through" summary, at most this often
QUIET_REPLY_WINDOW_SEC = 20 * 60   # they texted this job recently: its replies go out normally
QUIET_STATE_PATH = DOTS_DIR / "quiet_summaries.json"
_NOTHING_WENT_RE = re.compile(r"\b(nothing|no (new )?(applications?|submits?|submissions?)|zero|0 (new )?submi\w*|none)\b"
                              r".{0,40}\b(went|gone|submitted|gone out|went out|gone through)|"
                              r"\b(never|not|hasn'?t|didn'?t|wasn'?t|haven'?t)\b.{0,25}\b(went|gone|submitted|sent)\b", re.I)


def _quiet_background(dot):
    """A job that runs in the background until told to stop (the application lanes): it works, it doesn't narrate."""
    if getattr(dot, "kind", "") not in ("task", "job"):
        return False
    return str(getattr(dot, "label", "") or "").startswith("Dot lane") or _autonomous(dot)


def _owner_asked_at(dot):
    """When they last asked this job something (texted it, or a message of theirs forwarded to it); 0 if never."""
    try:
        start = float(getattr(dot, "created", 0) or 0) + 10  # the text that started the job isn't a new question
        heard = [m.get("t", 0) for m in dot.chat() if m.get("from") == "you" and m.get("t", 0) > start]
    except Exception:
        heard = []
    try:
        inbox = (dot.folder / "inbox.txt").read_text(encoding="utf-8")
        if inbox.strip() and not re.search(r"^\W*\[", inbox.strip()):  # "[They said to keep going ...]" is the daemon
            heard.append(float((dot.folder / "inbox.since").read_text(encoding="utf-8")))
    except Exception:
        pass
    try:
        heard.append(float((dot.folder / "heard.at").read_text(encoding="utf-8")))
    except Exception:
        pass
    return max(heard) if heard else 0.0


def _owner_waiting(dot):
    """They asked this job something in the last QUIET_REPLY_WINDOW_SEC (texted it, or a message forwarded to it)."""
    at = _owner_asked_at(dot)
    return bool(at) and _now() - at < QUIET_REPLY_WINDOW_SEC


# --- what a quiet background job (the Dot lane, any "until I say stop" job) may text ---------------------------
# Owner 2026-11-06: 166 Discord texts in 25 hours, 83 of them the portal lane narrating its own monitoring ("Running
# the next check now. It waits 4 minutes...", "Correcting my KION call...", "Nothing new went in since 22:02...").
# Only three kinds go out: (a) an answer to something they asked this job in the last 20 min, (b) one "what went
# through" summary every 3 hours, (c) a real ask (QUESTION, an OK prompt, or a text that needs them to act).
QUIET_ANSWERS_PER_ASK = 2   # texts per ask of theirs: the answer (and one follow-up), not every step after it
# The first sentence says what it's doing next, or corrects itself: work narration, never an answer.
_NARRATION_RE = re.compile(
    r"^\W*(?:(?:ok(?:ay)?|alright|so|now|also|still|one (?:more )?(?:thing|correction|catch))\W+)?(?:"
    r"next\b|running|re-?running|checking|re-?checking|retrying|trying|monitoring|picking\b|correct(?:ing|ion)|"
    r"scratch that|my (?:earlier|last|bad|mistake)|i was wrong|i (?:shouldn'?t|should not) have|i made the same|"
    r"(?:the |my |a )?(?:next|20-min(?:ute)?|first|last|latest|new) (?:check|sweep|step|row|pass|run|portal row)\b|"
    r"sweep|patch test|starting|waiting|looking|reading|auditing|verifying|confirming|testing|fixing|patching|"
    r"pulling|claiming|closing|caught|"
    r"(?:that|this|the|my) (?:check|click|lookup|look-?up|tool|script|command|page-check|retry|run|fetch|test|"
    r"patch|guard|hold gap|sign-?in page|screenshot)\b|"
    r"nothing (?:new|to fix|changed|has changed)|"
    r"i'?m (?:now |still |also |just )?\w+ing\b|i'?ll (?:now |next )?(?:check|look|run|retry|try|read|verify|confirm)\b|"
    r"let me\b|going to (?:check|look|run)|on the portals now|"
    r"(?!(?:no|some|every|any)thing\b|morning\b|evening\b|during\b)[a-z]+ing\b)", re.I)  # "Clicking ...", "Opening ..."
_ASKS_THEM_RE = re.compile(
    r"\b(?:you(?:'ll)? need to|can you|could you|would you|will you|do you want|"
    r"please (?:sign|log|send|reply|answer|confirm|approve|pick|choose|solve|enter|tell|text|decide|let me know)|"
    r"needs? (?:you|your)\b|wait(?:s|ing)? (?:on|for) (?:you|your)\b|"
    r"(?:only )?you can (?:do|answer|decide|sign|log|approve|pick)\b|"
    r"your (?:ok|okay|go-ahead|answer|call|approval|pick|choice) (?:is )?(?:needed|first|before)|"
    r"(?:sign|log) in (?:yourself|once|by hand)|solve (?:the|a|this|that) captcha|"
    r"(?:want|should) (?:me|i)\b[^.!?\n]*\?|let me know|tell me (?:if|whether|which|what|how))", re.I)
_NO_NEED_RE = re.compile(r"\b(?:nothing|no one|nobody|doesn'?t|don'?t|does not|do not|won'?t|isn'?t|never|no longer)\b"
                         r"[^.!?\n]{0,20}\b(?:needs?|waits?|waiting|need to)\b", re.I)
# Something really went in: the sentence says so with no "whether", "haven't verified", "nothing new ...".
_WENT_IN_RE = re.compile(r"\b(?:went (?:in|through)(?!\s+(?:the|a|an|my|its|your|their|this|that|every|each|all)\b)|"
                         r"(?:was|were|got|been|is|are) (?:logged as |marked |recorded as )?submitted|"
                         r"submitted (?:at|on|to|today|clean(?:ly)?)|applied to|applications? (?:is |are )?(?:in|sent)|"
                         r"success page|new submits?)\b", re.I)
_HEDGE_RE = re.compile(r"\b(?:haven'?t|hasn'?t|have not|has not|not|never|didn'?t|did not|won'?t|can'?t|couldn'?t|"
                       r"wouldn'?t|no new|nothing|none|whether|if|how|unconfirmed|unverified|would|could|might|until|"
                       r"check(?:ing)?|verif(?:y|ying)|zero)\b|\b0 (?:new )?(?:submits?|applications?)", re.I)


def _plain(text):
    return (text or "").replace("’", "'").replace("‘", "'")


def _sentences(text):
    return [s.strip() for s in re.split(r"(?<=[.!?])\s+|\n+", _plain(text)) if s.strip()]


def _narration(text):
    """It's describing its own work ("Running the next check now", "Correcting my KION call"), not answering."""
    first = re.split(r"(?<=[.!?:;])\s|\n", _plain(text).strip(), maxsplit=1)[0][:200]
    return bool(_NARRATION_RE.match(first))


def _asking_sentence(s):
    s = re.sub(r"\"[^\"\n]*\"|“[^”\n]*”|`[^`\n]*`", "", _plain(s)).strip()  # a quoted form question isn't for them
    if not s or _NO_NEED_RE.search(s):
        return False
    return bool(_ASKS_THEM_RE.search(s) or (s.endswith("?") and re.search(r"\byou(r)?\b", s, re.I)))


def _asks_them(text):
    """The part of a text that needs them to do or decide something ("" if none): the bullet lines that ask, or the
    asking sentences of a paragraph. "Can you perform the essential duties?" in quotes and "nothing needs you" don't."""
    keep = []
    for ln in _plain(text).splitlines():
        hits = [s for s in _sentences(ln) if _asking_sentence(s)]
        if hits:
            keep.append(ln.strip() if re.match(r"\s*[-•*]|\s*\d+[.)]\s", ln) else " ".join(hits))
    return "\n".join(keep)


def _went_through(text):
    """Only the sentences that say something really went through, or "" if none do."""
    hits = [s for s in _sentences(text) if _WENT_IN_RE.search(s) and not _HEDGE_RE.search(s) and not _narration(s)]
    return ("\n" if any(h[:1] in "-•*" for h in hits) else " ").join(hits)


def _quiet_state():
    try:
        return json.loads(QUIET_STATE_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _save_quiet_state(st):
    try:
        _write_json(QUIET_STATE_PATH, st)
    except Exception:
        pass


LANE_ASK_GAP_SEC = 6 * 3600   # a background job's own QUESTION to him, at most this often (across those jobs)
LANE_ASK_SAME_SEC = 24 * 3600  # ...and never the same question again within a day


def _background_question_ok(dot, text):
    """A background job's QUESTION may go out: he's talking to it, or it's urgent, or it's the first ask in
    LANE_ASK_GAP_SEC and not one he was already asked today. 2026-11-08/09: the lane asked "is the VM free?" 15
    times overnight and "Hispanic or Latino?" 10 times; application questions belong in his one-at-a-time buttons."""
    if _owner_waiting(dot):
        return True
    st = _quiet_state()
    asks = [a for a in st.get("lane#asks") or [] if isinstance(a, dict) and _now() - a.get("t", 0) < LANE_ASK_SAME_SEC]
    q = text.split("\n(", 1)[0]
    if any(_same_question(q, a.get("q", "")) for a in asks):
        return False
    if not _URGENT_RE.search(text) and any(_now() - a.get("t", 0) < LANE_ASK_GAP_SEC for a in asks):
        return False
    st["lane#asks"] = asks + [{"t": _now(), "q": q[:300]}]
    _save_quiet_state(st)
    return True


def _background_text(dot, text, ask=False, buttons=False):
    """What a quiet background job may text them ("" = it stays on the job's page as a quiet row):
    (a) an answer to something they asked this job in the last QUIET_REPLY_WINDOW_SEC, not narration, at most
        QUIET_ANSWERS_PER_ASK texts per ask;
    (b) at most one "what went through" summary every QUIET_SUMMARY_GAP_SEC, cut to the sentences that say so;
    (c) an OK prompt with buttons, a QUESTION (see _background_question_ok), or an urgent line that needs him
        (a deadline today or tomorrow, a sign-in link). "Still waiting on your answer" reminders never go: his
        application questions reach him one at a time through the daily to-do's buttons ."""
    text = (text or "").strip()
    if not text:
        return ""
    if buttons:
        return text
    if ask:
        return text if _background_question_ok(dot, text) else ""
    at = _owner_asked_at(dot)
    if at and _now() - at < QUIET_REPLY_WINDOW_SEC and not _narration(text):  # (a) their answer, whole
        st, key = _quiet_state(), f"{dot.id}#answers"
        rec = st.get(key) if isinstance(st.get(key), dict) else {}
        n = int(rec.get("n", 0)) if rec.get("at") == at else 0
        if n < QUIET_ANSWERS_PER_ASK:
            st[key] = {"at": at, "n": n + 1}
            _save_quiet_state(st)
            return text
    asking = _asks_them(text)
    if asking and _URGENT_RE.search(asking):  # (c) only the lines that need them, not the report around them
        return asking
    went = _went_through(text)  # (b)
    if went:
        st = _quiet_state()
        try:
            last = float(st.get(dot.id, 0) or 0)
        except (TypeError, ValueError):
            last = 0.0
        if _now() - last >= QUIET_SUMMARY_GAP_SEC:
            st[dot.id] = _now()
            _save_quiet_state(st)
            return went
    return ""


def _worth_interrupting(dot, text):
    """For a quiet background job: True if this text may go out (see _background_text)."""
    return bool(_background_text(dot, text))


def tell_user(dot, text, files=(), components=None, ask=False, gated=False):
    """Say something to the user: in the Dot's chat on the page, and by Discord
    DM or text when one is connected. A Dot made on the page or the command line
    gets the default channel as its home, so replies to it come back to it.
    ask: it's a question or OK prompt for them (a quiet background job still sends it).
    gated: the caller already ran _background_text on it."""
    text = (text or "").strip()
    if not text and not files:
        return
    if not gated and _quiet_background(dot):
        # Owner 2026-11-04: "the chats that dot are tellign me are kind of really irrelevant like idk what to do with
        # what its tellign me" (45 self-debugging texts in 20 min from the Dot lane); 11-06: 83 more in a day.
        # Everything else is kept on the job's page only.
        out = _background_text(dot, text, ask=ask, buttons=bool(components)) if text else ""
        keep_files = bool(files) and (bool(out) or _owner_waiting(dot))  # a screenshot they asked for still goes
        if out != text or (files and not keep_files):
            dot.add_message("dot", text + "".join(f"\n📎 {Path(f).name}" for f in files), quiet=True)
        if not out and not keep_files:
            return
        text, files = out, (files if keep_files else ())
    ref = None
    background = _quiet_background(dot)
    if text and not background and dot.kind not in ("chat", "reminder") and dot.reply_to \
            and len(active_tasks(dot.reply_to)) > 1:
        # Several jobs at once: like a person would, reply to the text that started
        # this one, so it's clear which job a message is about.
        if dot.trigger and dot.reply_to.startswith("discord"):
            ref = dot.trigger
        else:
            text = f"re {dot.label or dot.name}: {text}"
    dot.add_message("dot", text + "".join(f"\n📎 {Path(f).name}" for f in files))
    _last_told[dot.id] = _now()
    try:  # on disk too, so the job's own process (and the daemon) both know it just spoke
        if dot.kind != "chat" and load_dot(dot.id) is not None:
            _update(dot, told_at=_now())
    except Exception:
        pass
    to = dot.reply_to
    if not to:
        if discord.connected():
            to = "discord:" + discord.dm()
        elif line.connected():
            to = settings().get("line_notify", "")
        if to:
            _update(dot, reply_to=to)
    if not to or to.startswith("local:") or \
            not (discord.connected() if to.startswith("discord") else line.connected()):
        return
    # A job he started (or a reminder he set) answers him whenever it finishes; the lane, watches and briefs
    # are unprompted, and go through the night hold, the budget and the short-text cut.
    asked = dot.kind in ("chat", "reminder") or (dot.kind in ("task", "job") and not background)
    if background:  # the lane answers him only when he's talking to it, not whenever he texts about anything
        asked = _owner_waiting(dot)
    try:
        with _dm_context(asked=asked if (asked or background) else None, urgent=(dot.kind == "reminder") or None):
            if components and to.startswith("discord"):
                send_to(to, text, files, components)
            elif ref:
                discord.send(to, text, files, reply_to=ref)
            else:
                send_to(to, text, files, None if to.startswith("discord") else components)
        if is_imessage_chat(to) and dot.trigger and dot.asking and dot.kind != "chat":
            line.react(to, dot.trigger, "emphasize")  # ‼️ on their text: this one needs you (Private API only)
    except Exception as e:
        dot.log(f"\n[couldn't message you: {e}]\n")
        # Marked in the chat, so the quick brain and the page know it never arrived.
        dot.add_message("dot", f"[that last text didn't reach them: {str(e)[:120]}]", failed=True)


# --- running a Dot ---------------------------------------------------------------

_wake = threading.Event()


class _Tee(io.TextIOBase):
    def __init__(self, dot):
        self.dot = dot

    def write(self, s):
        if s:
            self.dot.log(re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", s))
        return len(s)

    def flush(self):
        pass


# What their computer and Dot's own computer are, in the words the prompts use (a friend's Mac runs the Dot PC in Lima).
HOST_PC = "Mac" if sys.platform == "darwin" else "Windows PC"
VM_KIND = "Ubuntu 24.04 in a Lima VM on their Mac" if sys.platform == "darwin" else "Ubuntu 24.04 in WSL"
PERSONA = (
    "You are Dot, the user's personal assistant. They text you from their phone (Discord DMs), "
    "like texting a friend who happens to be great with computers. You can control their " + HOST_PC + " "
    "(apps, files, their logged-in Chrome, mail, calendar, Canvas, the screen) and your own "
    "Linux computer (the Dot PC, vm_* tools: web, downloads, installs). Use whichever is easier: "
    "the Dot PC for general web work, their PC when it needs their accounts, apps or files."
)
DOT_STYLE = (
    "How you write: like a real person texting. Casual, warm, short, lowercase is fine, match "
    "their vibe. No headings, no tables, no \"Summary:\", no tool names, no \"Done.\" or \"On it.\" "
    "on their own. Be straight with them: no lectures, disclaimers or hedging; if something really "
    "can't be done, say so in a few words and offer what you can do. When a job needs work, do it fully with your tools (run independent look-ups "
    "together in one reply) and push through problems yourself; don't ask what to do next or offer "
    "a menu. Don't narrate your steps (owner 2026-11-04/05: step-by-step texts are useless to them and "
    "aren't sent); just do the work, then reply with what you found or did, like you'd text it: the "
    "answer first, short. "
    "Every text buzzes their phone (owner 2026-11-09: \"dot spams me\"), so text like the best assistant they "
    "know: one message, 1-3 short lines, unless they asked for a list, a draft or the details. Only text when "
    "they have to do or decide something, or when something real happened (it went through, it's sent, it's "
    "booked, a deadline is close). Never a status with nothing in it for them, never what you're about to do, "
    "never something you already told them, never a question they already answered. Plain words only: no lane "
    "or script names, file paths, job ids, \"quarantined\", \"morning notes\", \"retry guard\", \"audit\", "
    "tracker rows. Never tell them you can't reach your computer, the VM or your tools: use them, and if one "
    "really fails, say in plain words what you couldn't get. "
    "If the answer is somewhere you can reach (their mail, calendar, Canvas, a site you can sign in to "
    "on your computer, the job data on your computer), look it up and give them the answer. Never tell "
    "them to go check it (not \"check the letter for the pay\", not \"look in your email\"). Only ask for "
    "what really needs them: a login code, a choice, a fact you can't reach. Save facts that last "
    "(offers, pay, locations, booked calls, interview stages) on REMEMBER: lines. "
    "Every reply you write is a slow, rate-limited send, so make each one count: put every action "
    "you can already predict in the same reply (open + wait + read together; several look-ups at once), "
    "do multi-step file or web work as ONE run_command script (e.g. download, check the size, convert), "
    "prefer web_search / web_fetch / reading a page over clicking through it, and never spend a reply "
    "only to talk. "
    "Know when to stop: the moment you have what they asked for, answer and end (no extra "
    "double-checking, polishing or bonus steps they didn't ask for). If the same approach fails "
    "twice, switch to a different one; if nothing works, say so and stop. "
    "If you catch yourself doing the same manual look-ups you've done before for a kind of ask that keeps "
    "coming back, or a simple ask is taking minutes, finish the answer first, then add one line "
    "AUTOTOOL: <what to script and why> so Dot builds a script for it. "
    "To send a picture or file, put a line SEND: <full path> (save_screenshot makes screen "
    "pictures; send one whenever seeing it beats describing it). Files they send you are saved on "
    "their PC; if they want one somewhere (\"put this on my desktop\"), copy it there. If they ask you "
    "to email or text someone without giving the exact words, write it, show them the draft, and ask "
    "\"QUESTION: send it?\" before sending. If you are truly blocked (a choice only they can make, a login, a code), ask "
    "one short question on a line starting QUESTION:. If you must wait (a reply, a time), end "
    "with WAIT: <how long>. Facts worth remembering about them go on lines starting REMEMBER:."
)


FINDINGS_HOURS = 24
FINDINGS_PER_JOB = 1500
FINDINGS_TOTAL = 4000


def _recent_findings(dot, now=None):
    """What this chat's other jobs texted them in the last day, newest first.
    2026-11-05: "when are my interviews due?" took 25 steps over every inbox; an hour later "what do
    I have to do before I sleep" would have started that search from zero, since a job only saw
    the last few chat lines, not what earlier jobs found."""
    if not dot.reply_to:
        return ""
    now = now or _now()
    rows = []
    for o in all_dots():
        if o.id == dot.id or o.reply_to != dot.reply_to or o.kind not in ("task", "job") or _is_lane(o):
            continue
        try:
            said = [m for m in o.chat() if m.get("from") == "dot" and not m.get("quiet")
                    and len(str(m.get("text") or "")) >= 80 and now - m.get("t", 0) < FINDINGS_HOURS * 3600]
        except Exception:
            continue
        if said:
            text = "\n".join(str(m["text"]) for m in said[-2:])
            rows.append((said[-1].get("t", o.updated), o, text[-FINDINGS_PER_JOB:]))
    out, used = [], 0
    for t, o, text in sorted(rows, key=lambda r: -r[0]):
        block = f"- {o.label or o.name} ({_ago(t)}):\n{text}"
        if used + len(block) > FINDINGS_TOTAL:
            break
        out.append(block)
        used += len(block)
    return "\n".join(out)


def _prompt_for(dot, goal=None):
    """The first message of a job's conversation. `goal` is the unredacted goal
    when it differs from the saved one (a code they just texted)."""
    goal = goal or dot.goal
    computer = COMPUTER_MODES[computer_mode()]
    if computer_mode() == "auto" and dot.computer == "vm":
        computer = "For this job use your own computer (vm_* tools)."
    elif computer_mode() == "auto" and dot.computer == "pc":
        computer = "This job needs their own PC (their apps, files and logged-in accounts)."
    mem = memory_for(goal)  # the rules, plus what's about this job (not the file's tail)
    rules = standing_text()
    recent = _clean_context(dot.context) or "\n".join(
        f"{'them' if m['from'] == 'you' else 'you'}: {m['text']}" for m in dot.chat()[-10:]
        if m["from"] == "you" or not _says_no_tools(m["text"]))
    now = datetime.datetime.now().strftime("%A %b %d, %I:%M %p")
    others = [f"- {o.label or o.name}" for o in active_tasks(dot.reply_to) if o.id != dot.id] if dot.reply_to else []
    lessons = lessons_text()
    return (
        f"[{PERSONA}]\n[{DOT_STYLE}]\n[NOW] {now}\n"
        + (f"[COMPUTER] {computer}\n" if computer else "")
        + ("[LIVE] They're watching your screen live right now: do the work visibly on it (open pages "
           "in the browser and show results on screen, not only background downloads).\n" if dot.live else "")
        + ("[OTHER JOBS YOU'RE DOING AT THE SAME TIME (not yours to do here)]\n" + "\n".join(others) + "\n"
           if others else "")
        + (f"[STANDING INSTRUCTIONS FROM THEM, newest wins over anything older, including in this task]\n"
           f"{rules}\n" if rules else "")
        + (f"[WHAT YOU KNOW ABOUT THEM]\n{mem}\n" if mem else "")
        + f"[ABOUT YOU]\n{self_text(short=True)} When you hit a snag worth avoiding next time, write one "
          "line starting LEARNED: so future jobs know it.\n"
        + (f"[WHAT YOU'VE LEARNED FROM PAST JOBS]\n{_sc_speed().pick_lessons(goal, budget=1500, text=lessons)}\n"
           if lessons.strip() else "")
        + (f"[EARLIER PROGRESS]\n{dot.summary[-2500:]}\n" if dot.summary else "")
        + (f"[WHAT YOUR OTHER JOBS FOUND FOR THEM LATELY (what you texted, as of then). Reuse it instead of "
           f"searching again when it covers this; check again only what could have changed since]\n{found}\n"
           if (found := _recent_findings(dot)) else "")
        + (f"[RECENT CHAT, background only: earlier requests in it are already handled or belong to "
           f"other jobs. Don't redo or re-report them]\n{recent}\n" if recent else "")
        + f"[WHAT THEY WANT]\n{goal}\n"
        + JOB_FOCUS_NOTE
    )


# 2026-11-10 audit: every job that night answered with the same stale to-do list (recruiter HireVue, Capital One,
# Constellation) and "I don't have tools in this session" instead of doing its own ask. The ask now closes the
# prompt with what to do with it; the sections above it are background.
JOB_FOCUS_NOTE = ("[THIS JOB] Do exactly WHAT THEY WANT above. Everything before it is background: don't list or "
                  "re-report other jobs' to-dos, deadlines or application status unless this request asks for them. "
                  "Your tools are live: start with the first tool call this request needs. Never say the work is "
                  "done unless a tool result in this conversation shows it.")

# Lines in a job's chat context that only say "I can't do anything from here" (Dot's own old replies, or the
# separate Claude chat's "I can't change anything from here"). Copied in as "you:", the model believed them.
_CONTEXT_NO_TOOLS_RE = re.compile(r"\b(can'?t|cannot|unable to) (change|edit|run|do|touch) (anything|files)\b|"
                                  r"\bonly (lets me )?read files\b|\b(edit\w*|run\w*|commands?)\b[^.\n]{0,50}\b(are|were|is)"
                                  r" (turned off|disabled|off|unavailable|not allowed)\b|"
                                  r"\bdon'?t have (any )?(tools|tool access)\b", re.I)


def _says_no_tools(text):
    t = str(text or "")[:600].replace("’", "'")
    try:
        if sc()._claims_no_tool_access(t):
            return True
    except Exception:
        pass
    return bool(_NO_TOOLS_RE.search(t) or _CONTEXT_NO_TOOLS_RE.search(t))


def _clean_context(context):
    """A job's saved chat context minus the lines where an assistant said it couldn't act."""
    if not context:
        return context
    note = LANE_SIDE_NOTE if context.rstrip().endswith(LANE_SIDE_NOTE) else ""
    body = context.rstrip()[:-len(note)] if note else context
    chunks = re.split(r"(?m)^(?=(?:them|you): )", body)
    kept = [c for c in chunks if c.strip() and not (c.startswith("you: ") and _says_no_tools(c[5:]))]
    # The Claude chat (autotools/claude_chat.py) answers in the same DM, but it is a different assistant:
    # what it can or can't do is not what this job can do.
    kept = [re.sub(r"^you: Claude chat:", "claude chat (a separate assistant, not you):", c) for c in kept]
    return ("".join(kept).strip() + ("\n" + note if note else "")).strip()


_SEND_RE = re.compile(r"^\s*SEND:\s*\"?(.+?)\"?\s*$", re.I | re.M)
_TAG_RE = re.compile(r"^\s*(REMEMBER|LEARNED|AUTOTOOL|WAIT|QUESTION):\s*(.*)$", re.I | re.M)


def split_turn(prose):
    """A model turn -> (text to send, files to send, tags). Tags: REMEMBER/LEARNED/AUTOTOOL/WAIT/QUESTION."""
    files = [m.group(1).strip() for m in _SEND_RE.finditer(prose or "")]
    text = _SEND_RE.sub("", prose or "")
    tags = {"remember": [], "learned": [], "autotool": [], "wait": "", "question": ""}
    for m in _TAG_RE.finditer(text):
        kind, val = m.group(1).lower(), m.group(2).strip()
        if kind in ("remember", "learned", "autotool"):
            tags[kind].append(val)
        else:
            tags[kind] = val
    # a question stays in the text (minus its label); the other tags are for Dot only
    text = re.sub(r"(?im)^\s*QUESTION:\s*", "", text)
    text = re.sub(r"(?im)^\s*(REMEMBER|LEARNED|AUTOTOOL|WAIT):.*$", "", text)
    text = re.sub(r"(?im)^\s*(summary:.*|done[.!]?|on it[.!]?)\s*$", "", text)
    # internal labels never reach a text: tool names on their own, "Step 2/5:" prefixes
    text = re.sub(r"(?im)^[ \t]*[`*]*(update_plan|noop|no-op)[`*]*[.!]?[ \t]*(\n|$)", "", text)
    text = re.sub(r"(?im)^\s*[*\[]*(plan\s+)?step\s*\d+(\s*(/|of)\s*\d+)?[\]*]*\s*[:.)-]\s*", "", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip(), files, tags


UPDATE_GAP_SEC = 60  # between-step texts at most this often (2026-11-09 "dot spams me": it was 3 s)
PROGRESS_SAVE_SEC = 15  # the step and trail go to dot.json at most this often


def _just_acked(dot, within=45):
    """True if Dot gave this chat a heads-up moments ago. A job's first progress
    line ("ok grabbing the #1 post") right after the quick reply ("i'll check
    what's at #1") says the same thing twice, so it's skipped. Later updates
    still go out often, the way they like it."""
    if not dot.reply_to:
        return False
    try:
        last = [m for m in chat_history(dot.reply_to, 3) if m["from"] == "dot"]
    except Exception:
        return False
    return bool(last) and _now() - last[-1].get("t", 0) < within
QUIET_STEP_SEC = 20  # no text for this long mid-job: say what step it's on
NOTHING_NEW = "NOTHING_NEW"
STOP_WATCHING = "STOP_WATCHING"


_STEP_OPENERS = ("ok ", "now ", "", "", "alright, ")


def _step_line(desc):
    """'Reading the page on my computer' -> 'now reading the page on my computer'.
    Plain words like a person texting what they're up to; no "still on it ·" tags."""
    desc = (desc or "").strip().rstrip(".")
    if not desc:
        return ""
    opener = _STEP_OPENERS[len(desc) % len(_STEP_OPENERS)]  # varied, but the same step reads the same
    return opener + desc[0].lower() + desc[1:]


class DotStop(KeyboardInterrupt):
    """Dot ending a run on purpose (time limit, repeating, stopped, a question).
    The agent loop treats it like Ctrl+C but logs the reason and keeps the
    conversation it got to."""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


QUESTION_REPEAT_SEC = 10 * 60  # the same question isn't texted again within this


def _norm_question(q):
    return re.sub(r"\s+", " ", re.sub(r"[^\w\s]", " ", (q or "").lower())).strip()


def _same_question(a, b):
    import difflib
    a, b = _norm_question(a), _norm_question(b)
    return bool(a and b) and (a == b or difflib.SequenceMatcher(None, a, b).ratio() >= 0.85)


LONG_JOB_RE = re.compile(r"\b(until i (say|tell you)( to)? stop|keep going|don'?t stop|until i('m| am) back|"
                         r"all night|until (it'?s|they'?re|everything'?s) (all )?done)\b", re.I)
LONG_TASK_TIME_LIMIT_SEC = 45 * 60
# It says something actually went through (an application, a send): the 20-minute clock restarts.
WIN_RE = re.compile(r"\b(submitted|went (in|through)|confirmed|applied to|application (is )?(in|sent)|"
                    r"success page)\b", re.I)
LONG_MAX_RUNS = 20


def _long_job(dot):
    """They said to keep at it ("until I say stop"): longer runs, no check-ins.
    Only the original ask counts, not a "keep going" button pressed later."""
    first = (dot.goal or "").split("\n(then they said")[0]
    return dot.kind in ("task", "job") and bool(LONG_JOB_RE.search(first))


# "keep applying until I tell you to stop", "work thru the night", "no check-ins": the
# job never parks on "want me to keep going?" or a question; it decides, skips, carries on.
# (2026-10-20: the application run parked at 6:55am on "keep going?" while they slept,
# and nothing was sent until they woke at 10.)
AUTONOMY_RE = re.compile(r"\b(until (i|you'?re|you are) (say|tell you|explicitly told|told)( to)? stop|"
                         r"until (explicitly )?told to stop|infinitely|forever|all night|(thru|through) the night|"
                         r"(without|no) (any )?(continuation )?check-?ins?|work autonomously|"
                         r"i'?m (going to sleep|asleep|away|not here)|user is away)\b", re.I)
FOREVER_RE = re.compile(r"\b(until (i|you'?re|you are) (say|tell you|explicitly told|told)( to)? stop|"
                        r"until (explicitly )?told to stop|infinitely|forever)\b", re.I)
AUTONOMY_NAP_SEC = 20 * 60   # the "20 minutes with nothing sent = something's wrong" they asked for
MAX_NUDGES = 6               # un-stuck this many times in a row: rest 20 minutes, then try again


def _standing_for(dot):
    """Standing rules about this job (its topic is in the goal, or they share two longer words)."""
    goal = ((dot.goal or "") + " " + (dot.label or "")).lower()
    common = {"explicitly", "continue", "autonomously", "without", "instructions", "remains",
              "suitable", "consolidated", "unrelated", "including"}
    words = set(re.findall(r"[a-z]{7,}", goal)) - common
    out = []
    for topic, v in standing().items():
        text = (v.get("text") if isinstance(v, dict) else str(v or "")) or ""
        stem = topic.lower().rstrip("s")[:9]
        shared = words & set(re.findall(r"[a-z]{7,}", text.lower()))
        if (len(stem) >= 5 and stem in goal) or len(shared) >= 2:
            out.append(text)
    return out


def _own_standing(dot, rx):
    """Standing rules matching rx that are about this job's own topic. A standing "until I say stop"
    or "I'm away" about one topic (applications) only counts for jobs on that topic: a calendar or
    Akwaaba job that mentions the applications job must still finish and still check in."""
    mine = _topic_of(_lead(f"{dot.label or ''}. {dot.goal or ''}")) or _topic_of(_lead(dot.goal or ""))
    return [t for t in _standing_for(dot) if rx.search(t) and _topic_of(t) in (None, mine)]


def _autonomous(dot):
    """They're away and said to keep at it: no check-ins, no parking on questions."""
    if dot.kind not in ("task", "job"):
        return False
    return _long_job(dot) or bool(AUTONOMY_RE.search(dot.goal or "")) or bool(_own_standing(dot, AUTONOMY_RE))


def _forever(dot):
    """"until I tell you to stop": even a run that thinks it's finished picks up again."""
    if dot.kind not in ("task", "job"):
        return False
    if FOREVER_RE.search(dot.goal or ""):
        return True
    return bool(_own_standing(dot, FOREVER_RE))


# "If there's truly nothing left you can do, say what's blocking in one line" answered.
# (2026-10-22: "blocked: akwaaba's done, ..." and "everything for this job is finished" didn't count,
# so those jobs woke every minute and texted it again.)
NOTHING_LEFT_RE = re.compile(r"\bnothing(?:'s| is)? (?:left|blocking|to pick up|more to do)\b|"
                             r"\b(?:this job's|my) work (?:here )?is done\b|^\W*blocked\b|"
                             r"\b(?:this|the) (?:job|chat|task)(?:'s| is)? (?:all |already )?"
                             r"(?:finished|done|complete)\b", re.I)
FOREVER_IDLE_MAX_SEC = 2 * 3600  # an endless job with nothing to do looks again at 20, 40, 80, then every 120 min
FOREVER_IDLE_FINISH = 3          # endless only by a standing rule: this many idle stretches in a row and it's done


def _same_text(a, b):
    """Two texts saying the same thing (wording aside), like a repeated "nothing left here"."""
    return _same_question((a or "")[:800], (b or "")[:800])


def _last_said(dot):
    """The last text this job got through to them ("" if none)."""
    try:
        said = [m for m in dot.chat() if m.get("from") == "dot" and not m.get("failed")]
    except Exception:
        return ""
    return str(said[-1].get("text") or "") if said else ""


def _carry_on(dot, summary, note, wait=0):
    """Keep an autonomous job moving instead of asking them. After MAX_NUDGES in a row
    it rests AUTONOMY_NAP_SEC first (a real outage shouldn't burn the quota), never parks."""
    nudges = (dot.nudges or 0) + 1
    if nudges > MAX_NUDGES:
        wait, nudges = max(wait, AUTONOMY_NAP_SEC), 0
    dot.push_followup(note)
    _update(dot, summary=summary or dot.summary, status="sleeping" if wait else "queued",
            next_run=_now() + wait, nudges=nudges, runs_this_goal=0, question=None, asking="",
            answer=None, wait_wakes=0)
    dot.log(f"\n[autonomous] carrying on ({nudges}/{MAX_NUDGES}{f', resting {wait // 60} min' if wait else ''}): "
            f"{note[:200]}\n")


# What the send tools (email, Outlook, texts) return, so a text can't claim a send that didn't happen.
SEND_OK_RE = re.compile(r"^(Sent from |Sent to |Sent email|Sent\.)", re.I)
SEND_BLOCKED_RE = re.compile(r"Nothing was sent|^Not sent|waiting in Drafts|sending failed", re.I)
SENT_CLAIM_RE = re.compile(r"\b(sent|sending (it|them|both|now)|going out|went out|emailed|on (its|their) way)\b", re.I)
WEBMAIL_RE = re.compile(r"mail\.google\.com|outlook\.(live|office|office365)\.com|outlook\.com/mail", re.I)
NOT_SENT_RE = re.compile(r"\b(not|nothing|never|didn'?t|wasn'?t|weren'?t|isn'?t|no emails?|unsent|stopped|held|"
                         r"before sending|chose not)\b", re.I)

# Owner 2026-11-05, on "nov 18: capital one offer expires. check the letter for pay + location": "why does it
# tell me that. it can access it itself, it has a whole VM ... it should be telling me everything about
# everything." A final text that sends them off to look something up Dot can reach isn't sent; the job goes
# and looks it up (once a run, see Relay._look_it_up_yourself). Telling them to DO something only they can do
# (take a test, attend, sign) is fine.
_LOOK_PLACE = (r"e-?mails?|inbox|g?mail|outlook|(?:offer )?letter|calendar|canvas|gradescope|portal|attachment|"
               r"pdf|link|site|website|page|dashboard|account|workday|handshake|candidate home|thread|spam|junk")
_LOOK_YOURSELF_RE = re.compile(
    r"^(?:(?:you(?:'ll| will)? (?:can|could|should|need to|must|have to|gotta|might want to|may want to|"
    r"want to|'d want to|wanna)|you'?ll (?:want|need|have) to|you'?ll|make sure (?:to|you)|be sure to|go|try(?: to)?)\s+)?"
    r"(?:double[- ]?)?(?:(?:check|open|find|pull up|search|dig (?:up|through|into)|look (?:in|at|through|for|over|up|into))"
    rf"\b.{{0,80}}?\b(?:{_LOOK_PLACE})\b|(?:log ?in(?:to)?|sign in(?:to)?|go to|head (?:over )?to|visit)\b.{{0,60}}?"
    r"\bto (?:see|check|find|view|look|get|read)\b)", re.I)
_LOOK_THERE_RE = re.compile(  # "the link's in the X email, open it" / "the pay is in the letter"
    r"\b(?:link's|link is|links are|details (?:are|is)|info(?:rmation)?(?:'s| is)|everything(?:'s| is)|"
    r"the rest(?:'s| is)|(?:pay|salary|location|deadline|date|time)(?:'s| is| are))\s+(?:all\s+)?(?:in|on)\s+"
    rf"(?:the|your|their|that|this)\b.{{0,40}}?\b(?:{_LOOK_PLACE})\b|"
    rf"\b(?:{_LOOK_PLACE})\b[^.!?\n]{{0,60}}[,;]\s*(?:just\s+|so\s+)?(?:open|check)\s+(?:it|that|them)\b", re.I)
_LOOK_FILLER_RE = re.compile(r"^(?:(?:and|then|so|just|pls|please|ok|okay|also|but|maybe|now|first|tip|btw)\b[\s,]*)+", re.I)
_LOOK_NOT_RE = re.compile(r"\b(?:no need|don'?t (?:have|need) to|you don'?t need|without|not have to|won'?t (?:have|need) to|"
                          r"never)\b", re.I)
# Something only they can do in the same breath ("open the link and record the video") is a real ask.
_LOOK_THEIRS_RE = re.compile(r"\b(?:and|to|then)\s+(?:record|take|sign|accept|decline|attend|join|start|complete|finish|"
                             r"submit|interview|pay|upload|book|schedule|approve)\b|\b(?:phone|sms|authenticator|duo|"
                             r"password|passcode|2fa|two-factor)\b", re.I)
LOOKUP_NOTE = "[Your answer told them to go look something up themselves"


def _sends_them_to_look(text):
    """The part of a text that tells them to check / look up / open something Dot could reach itself ("" if none)."""
    # "if that wasn't you, check your account" (a security alert) is theirs to judge
    text = re.sub(r"[^.!?\n]*\bif (?:that|this|it) (?:wasn'?t|was not|wasn’t) you\b[^.!?\n]*", "", text or "", flags=re.I)
    for clause in re.split(r"[.!?;\n•]+|:[*_]*\s|,\s+|\s[-–—]\s|[()]", text):
        c = _LOOK_FILLER_RE.sub("", clause.strip(" \t*_>\"'`-–—")).strip()
        if not c or _LOOK_NOT_RE.search(c) or _LOOK_THEIRS_RE.search(c):
            continue
        if _LOOK_YOURSELF_RE.search(c):
            return c[:200]
    for line_ in text.splitlines():
        for s in re.split(r"(?<=[.!?])\s+", line_):
            m = _LOOK_THERE_RE.search(s)
            if m and not _LOOK_NOT_RE.search(s) and not _LOOK_THEIRS_RE.search(s):
                return s.strip()[:200]
    return ""


class Relay:
    """Turns the agent's turns into texts: quick updates while it works, then the
    answer. Fed by period's _reply_hook, so it sees exactly what the model
    said (no log scraping)."""

    def __init__(self, dot):
        self.dot = dot
        self.sent = []
        self.final = ""
        self.files = []
        self.tags = {"remember": [], "learned": [], "autotool": [], "wait": "", "question": ""}
        self.tool_counts = {}   # tool name -> calls this run, for the speed reflex (pd_autotool)
        self.repeat_calls = 0   # calls identical (name + args) to an earlier one this run
        self._call_seen = set()
        self.card = None
        self.stop_watching = False
        self._last_step = ""
        self._step_saved = 0.0
        self.cut_short = ""  # "time" or "stuck" when Dot pulled the plug on a run
        self._calls = {}
        self.began = _now()
        self.trail = []   # steps not saved to the Dot yet
        self.turns = 0    # model replies this run (each one is a rate-limited send)
        self.installed = False
        self.held = []         # updates that came too soon after the last text: sent with the next one
        self.q_told = False    # this run's question already reached them (or was a repeat)
        self.q_dup = False     # this run's question is one they were just asked
        self.asked_away = ""   # a question it had while they're away (it went on without an answer)
        self.won = False       # it said something went through this run
        # Woken by its own timer or "keep going" note, not by a text from them: an answer that only
        # repeats its last text isn't sent again (see _after_run).
        self.auto_wake = (dot.runs or 0) > 1 and (not dot.has_followups() or _only_own_notes(dot))
        self.sends_ok = 0      # email/text sends that really went out this run
        self.sends_blocked = 0  # ones the OK step or an error stopped
        self.evidence = []     # what each tool call this run actually returned, for the second-opinion check
        self.looked_up = False  # this run already sent it back to look something up itself (once a run)
        self.autonomous = _autonomous(dot)
        self.time_limit = LONG_TASK_TIME_LIMIT_SEC if (self.autonomous or _long_job(dot)) else TASK_TIME_LIMIT_SEC
        self.stuck_on = ""          # the action it kept repeating, for the nudge
        self._last_win = _now()     # last time it said something actually went through
        self._last_drift = _now()   # last "20 minutes and nothing went through" note
        self._standing_seen = self._standing_mtime()
        import pd_speed
        self.speed = pd_speed.Coach(dot.id)  # notices slow spots, hands back what it learned

    @staticmethod
    def _standing_mtime():
        try:
            return STANDING_PATH.stat().st_mtime_ns
        except OSError:
            return 0

    def _told_at(self, fresh=None):
        """When this job last texted them, from this process or any other."""
        return max(_last_told.get(self.dot.id, 0), getattr(fresh or self.dot, "told_at", 0) or 0)

    def after_tool(self, name, args, result, seconds):
        if name == "vm_claude":
            self.began += seconds  # Claude doing the work isn't this job's working time
        notes = []
        out = str(result or "").strip()
        try:
            shown = {k: v for k, v in (args or {}).items() if k != "desc"}
            self.evidence.append(redact(f"{name}({json.dumps(shown, default=str)[:300]}) -> {out[:500]}"))
            self.tool_counts[name] = self.tool_counts.get(name, 0) + 1
            key = f"{name}:{json.dumps(shown, sort_keys=True, default=str)[:400]}"
            if key in self._call_seen:
                self.repeat_calls += 1
            self._call_seen.add(key)
        except Exception:
            pass
        if SEND_OK_RE.match(out):
            self.sends_ok += 1
        elif SEND_BLOCKED_RE.search(out[:300]):
            self.sends_blocked += 1
            notes.append("[That was NOT sent. Nothing went out. Never tell them it was sent or is going out; "
                         "say it wasn't sent and why, then do what they ask next.]")
        try:
            note = self.speed.after(name, args, result, seconds)
            if note:
                notes.append(note)
        except Exception as e:
            print(f"[speed] {e}", file=sys.stderr)
        # A text they sent while this ran lands now, not on the job's next run.
        try:
            if self.dot.has_followups():
                said = self.dot.take_followups()
                if said and any(not r.lstrip().startswith("[") for r in said.splitlines() if r.strip()):
                    self.auto_wake = False  # they texted: whatever it says next is an answer to them
                if said:
                    notes.append(f"[They just texted]: {said}\n[Take this into account from now on; it "
                                 "can change or replace what you were doing.]")
                    _update(self.dot, current=redact(said), wait_wakes=0)
        except Exception as e:
            print(f"[inbox] {e}", file=sys.stderr)
        # They asked for it: 20 minutes with nothing going through means something's wrong.
        if self.autonomous and _now() - max(self._last_win, self._last_drift) > AUTONOMY_NAP_SEC:
            self._last_drift = _now()
            notes.append("[20-minute check: nothing has gone through in the last 20 minutes. Say in one line "
                         "what's blocking, then fix it or skip that item (log it) and move to the next one. "
                         "Don't ask them; they're away.]")
        # So does a standing instruction they changed ("pause the applications").
        seen = self._standing_mtime()
        if seen != self._standing_seen:
            self._standing_seen = seen
            rules = standing_text()
            if rules:
                notes.append(f"[Their standing instructions just changed, newest wins]:\n{rules}")
        return "\n\n".join(notes) or None

    def gate(self, name, args):
        """Refuse tools the current computer mode rules out (checked live, so
        "stay off my PC" applies mid-job), and screens another job is driving."""
        try:  # hard no's, refused outright (2026-11-06: Dot never writes ~/jobs/AUDIT_PASS, its own audit sign-off)
            import pd_policy
            hard = pd_policy.forbidden(name, args)
        except Exception as e:
            print(f"[policy] {e}", file=sys.stderr)
            hard = None
        if hard:
            self.dot.log(f"\n[refused {name}: {hard}]\n")
            return f"Refused: {hard}. Don't try another way."
        blocked = mode_blocks(name)
        if blocked:
            return blocked
        if re.search(r"navigate|open|goto", name) and WEBMAIL_RE.search(json.dumps(args or {}, default=str)):
            return ("Email only goes out through the email send tool, which shows them the email and waits for "
                    "their OK. Don't open Gmail or Outlook in a browser to write, schedule or send anything; "
                    "read mail with the email search/read tools.")
        which = "pc" if name in PC_INPUT_TOOLS else ("vm" if name in VM_INPUT_TOOLS else None)
        if which is None:
            return None
        waited = _now()
        ok = take_screen(which, self.dot, timeout=SCREEN_WAIT_SEC, tell=False)
        self.began += _now() - waited  # waiting for a screen isn't working time
        if ok:
            return None
        owner = next((t for t in active_tasks() if t.pid == _lock_owner(which)), None)
        where = "their screen" if which == "pc" else "your computer's screen"
        return (f"{where} is busy with another job ({owner.label or owner.name if owner else 'another job'}) "
                "right now. Do this part without the screen (web_search, web_fetch, run_command / vm_run "
                "scripts), or try the screen again in a minute.")

    def on_tool(self, name, args):
        """Before each tool: stop runaway runs, feed the live screen, and if it's
        been quiet a while, say what it's doing so it never looks stuck."""
        try:
            key = name + json.dumps(args, sort_keys=True, default=str)
        except Exception:
            key = name
        self._calls[key] = self._calls.get(key, 0) + 1
        if name in ("vm_run", "run_command") and re.search(r"\b(install|apt|pip|npm i)\b", key):
            self.installed = True
        fresh = load_dot(self.dot.id)
        if fresh is None or fresh.status == "stopped":
            raise DotStop("stopped")  # they said stop (or deleted it): nothing more runs
        if self._calls[key] >= SAME_CALL_LIMIT and name not in REPEATABLE_TOOLS:
            self.cut_short = "stuck"
            self.stuck_on = (str((args or {}).get("desc") or "") or name)[:150]
            raise DotStop("repeating")  # the agent loop ends the run cleanly on this
        if self.dot.kind not in ("watch", "brief") and _now() - self.began > self.time_limit:
            self.cut_short = "time"
            raise DotStop("time limit")
        self._flush_held(fresh)
        if self.card is not None:
            self.card.tool(name, args)
        try:
            desc = (args or {}).get("desc") or sc().infer_action_description(name, args or {})
        except Exception:
            desc = ""
        desc = str(desc or "")[:150]
        if desc and desc != (self.trail[-1] if self.trail else ""):
            self.trail.append(desc)  # what it actually did, for "how'd you do that?"
            if _now() - self._step_saved > PROGRESS_SAVE_SEC:  # the first step is saved at once
                self._step_saved = _now()
                try:
                    _update(self.dot, step=desc, trail=(self.dot.trail + self.trail)[-TRAIL_KEEP:])
                    self.trail = []
                except Exception:
                    pass
        if self.dot.kind in ("watch", "brief"):
            return
        line_ = _step_line(desc)
        if line_ and line_ != self._last_step and _now() - self._told_at(fresh) > QUIET_STEP_SEC:
            if not self._last_step and not self.sent and _just_acked(self.dot, within=30):
                self._last_step = line_  # the heads-up just said this; the next step may speak
                return
            self._last_step = line_
            # Owner 2026-11-05, on 11 "now finding X" / "alright, checking Y" texts for one "when are my interviews
            # due?": "am i trippin or is this overly long for this easy ass prompt". Step lines go on the job page
            # only (the typing indicator shows it's working); the answer and real asks are what get texted.
            self.dot.add_message("dot", line_, quiet=True)

    def _only_real_sends(self, text):
        """A text saying an email went out, when this run's sends were all stopped, is replaced by what happened."""
        if not text or self.sends_ok or not self.sends_blocked:
            return text
        claims = [s for s in re.split(r"(?<=[.!?\n])\s+", text) if SENT_CLAIM_RE.search(s) and not NOT_SENT_RE.search(s)]
        if not claims:
            return text
        self.dot.log(f"\n[blocked a text claiming a send that didn't happen: {text[:300]}]\n")
        return (f"nothing was sent: {'that email' if self.sends_blocked == 1 else f'all {self.sends_blocked} emails'} "
                "stopped at the OK step or failed, so nothing went out.")

    def _look_it_up_yourself(self, text):
        """A final text telling them to go check something Dot can reach ("check the letter for pay") isn't
        sent: the job is sent back to look it up and answer. Once a run, and never on the run that's doing
        that look-up, so it can't loop. Returns True when the text was held back."""
        if self.looked_up or self.dot.kind in ("watch", "brief") or not text:
            return False
        fresh = load_dot(self.dot.id) or self.dot
        if LOOKUP_NOTE in str(fresh.current or ""):
            return False  # this run is the look-up: whatever it says now goes out
        hit = _sends_them_to_look(text)
        if not hit:
            return False
        self.looked_up = True
        self.dot.log(f"\n[not sent, it told them to look it up themselves ({hit}): {text[:300]}]\n")
        self.dot.push_followup(
            f"{LOOKUP_NOTE} (\"{hit}\"), so it wasn't sent. Don't send them to look: you can reach it (their mail, "
            "calendar, Canvas, sites you can sign in to on your computer, the job data on your computer). Look it "
            "up now and put the actual answer in your reply (e.g. the pay and location from the letter), keeping "
            "the rest of what you had. Ask them only if it really needs them (a login code, a choice). Save lasting "
            "facts (offers, pay, locations, booked calls, interview stages) on REMEMBER: lines.]\n"
            f"(the reply that wasn't sent: {text[:1500]})")
        return True

    def _second_opinion(self, text):
        """A "done/sent/added" text is read by a model from another family next to the
        tool results; one it finds wrong is replaced by what really happened."""
        if not CHECKER_ON or not pd_checker.makes_claim(text):
            return text
        try:
            proof = pd_proof.facts_for(text)
        except Exception as e:
            print(f"[proof] {e}", file=sys.stderr)
            proof = pd_proof.Proof()
        if proof.lines:
            self.dot.log(f"\n[records for that claim: {'; '.join(proof.lines)[:600]}]\n")
        earlier = [f"earlier step: {t}" for t in (self.dot.trail or [])[-15:]]
        try:
            r = pd_checker.check_claim(text, earlier + self.evidence, self.dot.id, records=proof.lines)
        except Exception as e:
            print(f"[checker] {e}", file=sys.stderr)
            r = {"verdict": "unchecked", "why": "", "fixed": "", "model": ""}
        if r["verdict"] == "wrong":
            self.dot.log(f"\n[second opinion ({r['model']}) caught: {text[:300]} -- {r['why']}]\n")
            return r["fixed"] or f"{text}\n(not confirmed: {r['why']})"
        if proof.problems:  # the records contradict it, whatever the checker said (or if it couldn't be reached)
            self.dot.log(f"\n[records contradict: {text[:300]} -- {'; '.join(proof.problems)}]\n")
            return f"{text}\n(records say: {'; '.join(proof.problems)})"
        return text

    def _flush_held(self, fresh=None):
        """Updates held back by the 3-second gap go out (merged) once it has passed."""
        if self.held and _now() - self._told_at(fresh) > _update_gap(self.dot):
            text = "\n".join(self.held)
            self.held = []
            self.sent.append(text)
            _last_told[self.dot.id] = _now()
            tell_user(self.dot, text)

    def _asked(self, question, text, used_tools):
        """The model asked them something. The job is waiting on it from now on
        (not when the run ends), and the same question isn't texted twice in 10 minutes."""
        fresh = load_dot(self.dot.id) or self.dot
        self.q_dup = (_same_question(question, fresh.last_q) and _now() - (fresh.last_q_at or 0) < QUESTION_REPEAT_SEC)
        fields = dict(status="waiting", question=question, asking="question", answer=None,
                      qid=uuid.uuid4().hex[:6], asked_at=_now())
        if not self.q_dup:
            fields.update(last_q=question, last_q_at=_now())
        try:
            _update(self.dot, **fields)
        except Exception as e:
            print(f"[question] {e}", file=sys.stderr)
        if self.q_dup:
            self.q_told = True  # already asked: don't text it again
            return
        if used_tools:  # it asked mid-run: send it now, then the run ends here
            self.sent.append(text)
            self.q_told = True
            _last_told[self.dot.id] = _now()
            tell_user(self.dot, "\n".join(self.held + [text]), ask=True)
            self.held = []

    def __call__(self, prose, used_tools):
        self.turns += 1
        try:  # each reply is a send: counted as it happens, so "how many sends" is right mid-run
            _update(self.dot, sends=(self.dot.sends or 0) + 1)
        except Exception:
            pass
        if STOP_WATCHING in (prose or ""):
            self.stop_watching = True
            prose = prose.replace(STOP_WATCHING, "")
        if NOTHING_NEW in (prose or ""):
            return  # a watch found nothing worth a text
        text, files, tags = split_turn(prose)
        text = self._only_real_sends(text)
        text = self._second_opinion(text)
        self.tags["remember"] += tags["remember"]
        self.tags["learned"] += tags["learned"]
        self.tags["autotool"] += tags.get("autotool", [])
        self.tags["wait"] = tags["wait"] or self.tags["wait"]
        self.tags["question"] = tags["question"] or self.tags["question"]
        self.files += [f for f in files if f not in self.files]
        if WIN_RE.search(text or ""):
            self._last_win = _now()
            self.won = True
        if tags["question"] and self.dot.kind not in ("watch", "brief") and self.autonomous:
            # They're away: the question is an FYI, and the run decides or skips and goes on.
            if _quiet_background(self.dot):
                # Only the question goes out (the narration around it stays on the page), and not again if they
                # were just asked the same thing (2026-11-06).
                if text:
                    self.dot.add_message("dot", text, quiet=True)
                fresh = load_dot(self.dot.id) or self.dot
                if not (_same_question(tags["question"], fresh.last_q)
                        and _now() - (fresh.last_q_at or 0) < QUESTION_REPEAT_SEC):
                    try:
                        _update(self.dot, last_q=tags["question"], last_q_at=_now())
                    except Exception:
                        pass
                    _last_told[self.dot.id] = _now()
                    tell_user(self.dot, f"{tags['question']}\n(going ahead without it for now)", ask=True)
            else:
                note = (f"{text}\n" if text else "") + f"(you're away, so I'm not waiting on this: {tags['question']})"
                self.held.append(note)
                self._flush_held()
            self.tags["question"] = ""
            self.asked_away = tags["question"]
            if not used_tools:
                self.final = ""
            return
        if tags["question"] and self.dot.kind not in ("watch", "brief"):
            self._asked(tags["question"], text, used_tools)
            if not used_tools and not self.q_dup:
                self.final = text  # the question goes out when the run ends, with Yes/No buttons
            if used_tools:
                raise DotStop("asked a question")  # nothing more runs until they answer
            return
        if not text:
            return
        if used_tools:
            # A thought between steps: send it if it's been quiet for a bit, like
            # a person giving a heads-up. Too soon after another message, it's held
            # and goes out with the next one; the run's first "ok doing X" is
            # skipped if the quick reply already said that.
            if text in self.sent or text in self.held:
                return
            if _quiet_background(self.dot):
                # The lane and "until I say stop" jobs: an answer to their ask, one summary every 3 hours, or a real
                # ask; never "running the next check" (2026-11-06, 83 lane texts in a day). No held/merged texts.
                self.sent.append(text)
                out = _background_text(self.dot, text)
                if out != text:
                    self.dot.add_message("dot", text, quiet=True)
                if out:
                    _last_told[self.dot.id] = _now()
                    tell_user(self.dot, out, gated=True)
                return
            if not _NEEDS_THEM_RE.search(text) and not (len(text) >= 100 and _owner_waiting(self.dot)
                                                        and not _narration(text)):
                # (while they're waiting on an ask, a real finding goes out; "ok checking X" lines still don't)
                # Owner 2026-11-04: step-by-step texts are "really irrelevant like idk what to do with" them. The page
                # (and the typing indicator) still show the work; only the answer and things that need them get sent.
                self.sent.append(text)
                self.dot.add_message("dot", text, quiet=True)
                return
            if _now() - max(self._told_at(), _last_text_to(self.dot)) > _update_gap(self.dot):
                if self.turns == 1 and not self.sent and not self.held and _just_acked(self.dot):
                    self.sent.append(text)  # counts as said, so it isn't repeated at the end
                    return
                text = "\n".join(_progress_kept(self.dot, self.held) + [text])
                self.held = []
                self.sent.append(text)
                _last_told[self.dot.id] = _now()
                tell_user(self.dot, text)
            else:
                self.held.append(text)
        else:
            if self._look_it_up_yourself(text):
                self.final = ""  # it goes and looks it up next (the followup), then answers
                return
            self.final = text  # the answer; sent when the run ends

    def finish(self):
        for line_ in self.tags["remember"]:
            remember(line_)
        for line_ in self.tags["learned"]:
            learn(line_)
        self.speed.close(self.tags["learned"])
        try:  # the speed reflex: what this run cost, filed under its kind of ask (+ its own AUTOTOOL: notes)
            import pd_autotool
            pd_autotool.record(self.dot, self)
        except Exception as e:
            print(f"[autotool] {e}", file=sys.stderr)
        if self.trail:
            _update(self.dot, trail=(self.dot.trail + self.trail)[-TRAIL_KEEP:])
            self.trail = []
        def empty(f):
            try:
                return os.path.getsize(f) == 0
            except OSError:
                return False
        found = [f for f in self.files if os.path.isfile(f)]
        files = [f for f in found if not empty(f)]
        if len(files) < len(found) and self.final:
            self.final += "\n(one of the files came out empty, so I left it off)"
        if self.held:  # updates still held back by the gap: they go out with the answer, never dropped
            # (on iMessage, stale "ok doing X" lines are left off an answer; ones with a link stay)
            self.final = "\n".join((_progress_kept(self.dot, self.held) if self.final else self.held)
                                   + ([self.final] if self.final else []))
            self.held = []
        buttons = None
        if self.tags["question"] and re.search(r"\b(send|ok|okay|should I|want me|go ahead|good)\b.*\?",
                                               self.tags["question"], re.I):
            L = _live()
            qid = (load_dot(self.dot.id) or self.dot).qid
            # The buttons name the question, so pressing one after a newer question says "that one's old".
            buttons = L.buttons([("Yes", f"ans:{self.dot.id}:{qid}:yes", 3), ("No", f"ans:{self.dot.id}:{qid}:no", 4)])
        if self.final and self.final not in self.sent:
            if self.tags["question"]:
                self.q_told = True
            if buttons:
                tell_user(self.dot, self.final, files, components=buttons)
            else:
                tell_user(self.dot, self.final, files, **({"ask": True} if self.tags["question"] else {}))
        elif files:
            tell_user(self.dot, "", files)
        trigger = _triggers.pop(self.dot.id, None)
        if not trigger and self.dot.trigger and (self.dot.reply_to or "").startswith("discord"):
            trigger = (self.dot.reply_to, self.dot.trigger)  # set by the daemon; jobs run in their own process
        if trigger:
            L = _live()
            L.react(L.channel_of(trigger[0]), trigger[1], "👀", on=False)
            # No ✅ on his text when a job ends (owner 2026-11-11: "it keeps reacting check marks to my messages";
            # jobs that did nothing were marked ✅ too). The job's reply says how it went.


_triggers = {}  # dot id -> (chat, message id) of the text that started the current job


_last_told = {}  # dot id -> when Dot last messaged the user


def _draft_warning(dot, draft):
    """What a second model thinks is off about a draft, judged against their own words; "" if nothing."""
    if not CHECKER_ON:
        return ""
    fresh = load_dot(dot.id) or dot
    said = [m["text"] for m in fresh.chat() if m.get("from") == "you"][-8:]
    request = "\n".join([f"job: {fresh.goal}"] + said + ([f"latest: {fresh.current}"] if fresh.current else []))
    try:
        r = pd_checker.check_draft(draft, request, dot.id)
    except Exception as e:
        print(f"[checker] {e}", file=sys.stderr)
        return ""
    return r["why"] if r["verdict"] == "wrong" else ""


def _approver_for(dot):
    def ask(prompt):
        hold = sc()._pending_hold[0] or {}
        sc()._pending_hold[0] = None
        reason, what = hold.get("reason", ""), hold.get("what", "")
        question = (f"quick check before I do this: {what.rstrip('.')}" if what else "quick check before I go on")
        question += f" ({reason})" if reason else ""
        draft = hold.get("draft", "")
        if draft:
            question += f"\n```\n{draft[:1500]}\n```"
            warning = _draft_warning(dot, draft)
            if warning:
                question += f"\n⚠️ second check: {warning}"
        qid = uuid.uuid4().hex[:6]
        _update(dot, question=question, asking="ok", answer=None, status="waiting", qid=qid, asked_at=_now())
        L = _live()
        tell_user(dot, question + ". ok to go ahead?", components=L.buttons(
            [("Go ahead", f"ok:{dot.id}:y:{qid}", 3), ("Don't", f"ok:{dot.id}:n:{qid}", 4)]))
        deadline = _now() + QUESTION_TIMEOUT_SEC
        while _now() < deadline:
            fresh = load_dot(dot.id)
            if fresh is None or fresh.status == "stopped":
                return "n"
            if fresh.answer is not None:
                ans = fresh.answer
                _update(dot, answer=None, question=None, asking="", status="working")
                return "n" if re.match(NO_RE, ans.lower()) else "y"
            time.sleep(1)
        _update(dot, question=None, asking="", status="working")
        tell_user(dot, "didn't hear back so I skipped that part")
        return "n"
    return ask


_typing_sent = {}  # Discord channel -> when "typing…" was last shown


def _typing_ping(chat):
    """Show "Dot is typing…" in their Discord DM for the next ~10 s (Discord's
    own length), at most once every 8 s. Sent off-thread so it never slows a reply.
    On iMessage it needs BlueBubbles' Private API; without it nothing is shown."""
    if is_imessage_chat(chat):
        if _now() - _typing_sent.get(chat, 0) >= 8:
            _typing_sent[chat] = _now()
            threading.Thread(target=line.typing, args=(chat,), daemon=True, name="dot-typing").start()
        return
    if not (chat or "").startswith("discord:"):
        return
    dm = chat.split(":", 1)[1]
    if _now() - _typing_sent.get(dm, 0) < 8:
        return
    _typing_sent[dm] = _now()

    def post():
        try:
            sc()._discord("POST", f"/channels/{dm}/typing")
        except Exception:
            pass
    threading.Thread(target=post, daemon=True, name="dot-typing").start()


_TOOL_FENCE_RE = re.compile(r"^[ \t]*`{3,}[ \t]*tool:", re.M)


def will_text(so_far):
    """Is the reply being written going to reach them as a text? True once it has
    words outside tool blocks (tool-only turns and Dot's own tags don't count)."""
    prose = _TOOL_FENCE_RE.split(so_far, 1)[0]
    prose = re.sub(r"(?im)^\s*(REMEMBER|LEARNED|AUTOTOOL|WAIT|SEND|NOTHING_NEW|STOP_WATCHING)\b.*$", "", prose)
    return bool(re.search(r"\w{2,}", prose))


def _start_typing(dot):
    """"Dot is typing…" only while it's writing something they'll get, not the
    whole time a job works (that made it look like a text was always coming).
    Returns a stop function."""
    imsg = is_imessage_chat(dot.reply_to) and line.private_api()  # iMessage shows typing only with the Private API
    if not ((dot.reply_to or "").startswith("discord:") or imsg) or dot.kind in ("watch", "brief"):
        return lambda: None

    def watch(so_far):
        if dot.status != "waiting" and will_text(so_far):
            _typing_ping(dot.reply_to)
    sc()._text_watchers.append(watch)
    return lambda: watch in sc()._text_watchers and sc()._text_watchers.remove(watch)


# 2026-11-05 speed: a job that never touches the PC's screen or apps doesn't wait up to 30 s for the MCP servers.
_NEEDS_MCP_RE = re.compile(r"\b(windows?|screens?|click|desktop|apps?|open|blender|roblox|studio|notepad|chrome|browser|type"
                           r"|pc|computer|laptop|mouse|keyboard|minecraft|spotify|discord app|files?|folders?|downloads?"
                           r"|install\w*|settings)\b", re.I)


def run_dot(dot):
    _cc = None  # the Claude engine's handle (pd_claudecall), undone in the finally below
    os.environ["DOT_JOB_LABEL"] = dot.label or ""  # pd_policy: the "Dot lane:" application job may set up job-site 2FA (10/29)
    fresh = load_dot(dot.id)
    if fresh is None or fresh.status == "stopped":
        return  # stopped while it was waiting its turn: a stopped job stays stopped
    s = sc()
    _update(dot, status="working", runs=dot.runs + 1, runs_this_goal=dot.runs_this_goal + 1)
    dot.log(f"\n=== {_stamp()} · run {dot.runs}\n")
    real_console = s.console
    relay = Relay(dot)
    try:
        if dot.kind == "reminder":
            tell_user(dot, dot.goal)
            _update(dot, status="done")
            return
        from rich.console import Console
        s.console = s._ConsoleRouter(Console(file=_Tee(dot), width=110, color_system=None,
                                             force_terminal=False, soft_wrap=True))
        s._human_approver[0] = _approver_for(dot)
        s._reply_hook[0] = relay
        if dot.kind not in ("watch", "brief"):
            relay.card = _live().LiveCard(dot)
            _live()._cards[dot.id] = relay.card
        s._tool_hook[0] = relay.on_tool
        s._tool_gate[0] = relay.gate
        s._tool_after_hook[0] = relay.after_tool
        try:  # 2026-11-05: Claude Code (owner's plan) writes the replies; this loop still runs and gates every tool
            _cc = __import__("pd_claudecall").install(s, dot, is_lane=_is_lane, autonomous=_autonomous)
        except Exception as e:
            _cc = None
            print(f"[claude engine] {e}", file=sys.stderr)
        s._UNATTENDED[0] = False  # questions reach the user through the approver
        work = dot.folder / "work"
        work.mkdir(parents=True, exist_ok=True)
        os.chdir(work)
        config = s.load_config()
        s.renew_login_if_due(config, hours_before=1, quiet=True)
        if (s.login_hours_left(config) or 0) <= 0:
            _update(dot, status="failed", summary="the server login expired")
            tell_user(dot, "my the server login ran out, so I can't think right now 😅 open Period "
                           "on your PC once and sign in, then text me again")
            return
        model = (s.resolve_model_name(dot.model) if dot.model else None) or s.DEFAULT_MODEL
        try:  # page only (the job's log), never texted
            _ccm = __import__("pd_claudecall")
            only = bool(getattr(s, "claude_only", None) and s.claude_only())
            dot.log(("engine: remote (not a Claude model)" if model not in _ccm.MODELS and not only else
                     _ccm.describe(dot, s, _cc, is_lane=_is_lane, autonomous=_autonomous)) + "\n")
        except Exception:
            pass
        followup = dot.take_followups()
        _update(dot, current=redact(followup or (dot.current if dot.conv_id else dot.goal)))
        if followup:
            _update(dot, wait_wakes=0)  # they said something: waiting starts over
        rules = standing_text()
        claimed_no_tools = False
        if dot.conv_id and dot.parent_id and (s._claims_no_tool_access(dot.summary or "")
                                              or _NO_TOOLS_RE.search((dot.summary or "")[:600].replace("\u2019", "'"))):
            # 2026-11-08: once a reply says "I can't reach the VM / run commands", that claim sits in the
            # server-side history and every later turn repeats it (1108-eca6a looped on it for an hour).
            # A fresh conversation with the full setup breaks the loop; the trail and summary carry the state.
            dot.log("fresh conversation: the last reply claimed it had no tools\n")
            claimed_no_tools = True
            done = "\n".join(f"- {t}" for t in (dot.trail or [])[-12:])
            _update(dot, conv_id=None, parent_id=None,
                    summary="Your tools (vm_*, run_command, mail, browser) are connected and work; earlier replies "
                            "that said otherwise were wrong. Steps already done:\n" + (done or "- (none recorded)"))
        if dot.conv_id and dot.parent_id:
            # Same conversation: the model already has the setup and everything
            # said so far, so only what's new goes out.
            if followup:
                prompt = (f"[They texted]: {followup}\n[Do what this newest text asks. Everything they asked "
                          "before it is already handled: don't redo or revisit it unless this text says to.]\n")
            else:
                prompt = "[Keep going where you left off. Don't redo steps you already finished.]\n"
            if rules:
                prompt += f"[Their standing instructions, newest wins]\n{rules}\n"
            prompt += f"[{DOT_STYLE}]"
            conv_id, parent_id = dot.conv_id, dot.parent_id
        else:
            goal = dot.goal
            if followup:
                goal = dot.goal + f"\n(then they said: {followup})"
                _update(dot, goal=redact(goal))  # saved without codes; this run still sees them
            prompt, conv_id, parent_id = _prompt_for(dot, goal=goal), None, None
            # The first message runs past 100k characters (system setup + memory), and the tool syntax at its
            # very top got lost: fresh runs said "I have no tools". Repeat it at the end, where it survives.
            prompt += s.tool_syntax_reminder()
            if dot.computer == "vm" or computer_mode() == "vm":
                prompt += ("\n[Your own computer, the Dot PC, is ON: run commands there with ```tool:vm_run``` "
                           "(JSON args: command, desc, timeout).]")
            if claimed_no_tools:
                prompt += ("\n[FIRST STEP] Your tools are connected and live in this conversation. Your first reply "
                           "must be a tool block, not a status summary, exactly like:\n"
                           "```tool:vm_run\n{\"command\": \"uptime && ls ~/jobs | head -3\", \"desc\": \"Checking the "
                           "Dot PC\"}\n```\nthen continue the work. Never say you can't reach the VM or run commands "
                           "unless a tool call you just made returned an error.")
            elif dot.empty_runs:
                prompt += ("\n[FIRST STEP] Your last try at this request answered without running a single tool, so "
                           "none of it has been done. Your tools are live. Your first reply must be the tool block "
                           "for the first real step of WHAT THEY WANT (read_file, list_dir, run_command, search, "
                           "mail_*, drive_*, vm_run...). No status list, no plan, no other jobs' to-dos.")
        focus = dot.goal if not followup else (goal if not (dot.conv_id and dot.parent_id)
                                               else f"{dot.goal}\n(newest text from them: {followup})")
        # Pictures they sent, named in the chat lines of this prompt ([they sent a file, saved at "..."]).
        sent_pics = [p for p in re.findall(r'saved at "([^"]+)"', prompt)
                     if str(DOTS_DIR / "received").lower() in p.lower()]
        if getattr(s, "_task_focus", None) is not None:  # the prompt is whole; only this text's pictures go
            s._task_focus[0] = focus + "".join(f'\n[their file: "{p}"]' for p in dict.fromkeys(sent_pics))
        try:  # its first look-ups (the brief's, or the quick brain's "look"), done before its first send
            prompt += _sc_fast().prefetch_block(dot, relay, s, first=conv_id is None)
        except Exception as e:
            print(f"[prefetch] {e}", file=sys.stderr)
        relay.fresh = conv_id is None  # a new conversation: its first reply must start the work (_did_no_work)
        stop_typing = _start_typing(dot)
        if dot.computer != "vm":  # a job only on Dot's own computer doesn't need the MCP servers
            _mcp_ready.wait(30 if _NEEDS_MCP_RE.search(f"{dot.goal} {followup or ''}") else 2)
        try:
            conv, parent = s.run_agent_loop(
                prompt, model, s.MODEL_ENDPOINTS.get(model, s.DEFAULT_ENDPOINT), config,
                auto_approve=True, conv_id=conv_id, parent_id=parent_id, max_steps=STEPS_PER_RUN)
        finally:
            stop_typing()
            if relay.card is not None:
                relay.card.finish()
        # Only a conversation the server actually answered in is worth continuing. A first
        # request it refused leaves a made-up id with nothing in it: "keep going" there
        # reached a model that had never seen the task, and it did another job's work.
        # (Sends are counted per reply by the relay as they happen.) A run cut short
        # still hands back the conversation it got to, so nothing answered is asked again.
        if parent:
            _update(dot, conv_id=conv, parent_id=parent)
        _after_run(dot, s._last_stop.get("reason") or "", relay)
    except Exception as e:
        dot.log("\n" + traceback.format_exc())
        try:
            _update(dot, status="failed", summary=f"Crashed: {e}")
        except Exception:
            pass
        tell_user(dot, "ugh something broke on my end and I had to stop. try asking again?")
    finally:
        if _cc:
            try:
                __import__("pd_claudecall").uninstall(s, _cc)
            except Exception:
                pass
        s.console = real_console
        s._human_approver[0] = None
        if getattr(s, "_task_focus", None) is not None:
            s._task_focus[0] = None
        s._reply_hook[0] = None
        s._tool_hook[0] = None
        s._tool_gate[0] = None
        s._tool_after_hook[0] = None
        _live()._cards.pop(dot.id, None)
        try:
            if load_dot(dot.id) is not None:
                _update(dot, current="")  # still set after a restart = it was cut off mid-job
        except Exception:
            pass
        try:
            os.chdir(HERE)
        except Exception:
            pass


EMPTY_RUN_RETRIES = 1  # a run that did nothing on real work: tries again this many times, then says so
_CLAIMS_DONE_RE = re.compile(r"\b(is|are|it's|all|now) (done|finished|complete|set up|uploaded|created|fixed)\b|"
                             r"\bi(?:'ve| have)? (made|created|uploaded|finished|fixed|built|set up|moved|saved)\b",
                             re.I)


def _did_no_work(dot, stop, relay):
    """A fresh run of a job they asked for that ran no tool at all, asked nothing, and ended "finished" while
    saying it has no tools, claiming it's done, or with no look-up done for it beforehand. Nothing of the ask
    happened, so it isn't done (and its answer isn't one to text)."""
    if dot.kind != "task" or _is_lane(dot) or _autonomous(dot) or not getattr(relay, "fresh", False):
        return False
    if relay._calls or relay.cut_short or relay.asked_away or relay.tags["question"] or relay.tags["wait"]:
        return False
    if stop not in sc()._CLEAN_STOPS or not relay.turns:
        return False
    said = relay.final or ""
    last = [l for l in said.strip().splitlines() if l.strip() and not l.strip().startswith("[")]
    if last and last[-1].rstrip(" *_`").endswith("?"):
        return False  # it asked them something (their "ask me before you do something" rule): fair
    try:
        claims_none = bool(sc()._claims_no_tool_access(said))
    except Exception:
        claims_none = False
    return bool(claims_none or _says_no_tools(said) or _CLAIMS_DONE_RE.search(said) or relay.won or not dot.look)


SPIN_RUNS = 3  # runs in a row with no tool call before a job is restarted clean; twice that and it stops
SPIN_CONTEXT = ("[Earlier replies on this job repeated an old to-do list without doing any work; they were wrong and "
                "are left out. Start WHAT THEY WANT with a tool call.]")


def _spin_guard(dot, on_disk, relay, repeat=""):
    """True when this run was handled here (the caller stops). 2026-11-11: the Dot lane (963 runs) and a Tesla job
    answered every minute with the same stale "Math 21 is done... send the recruiter email?" list and never called a
    tool. _did_no_work skips lanes, endless jobs, later runs and replies ending in a question, so nothing caught it for
    12 hours. Any job whose runs call no tool SPIN_RUNS times in a row now restarts in a fresh conversation with its
    summary and chat context wiped (they carried the loop); a further SPIN_RUNS stops it: a lane is restarted clean
    by the lane tick, any other job tells them once that it got stuck."""
    if relay._calls or relay.cut_short or dot.kind != "task":
        if on_disk.spin_runs:
            _update(dot, spin_runs=0)
        return False
    if not getattr(relay, "auto_wake", False):
        return False  # an answer to a text from them (it may need no tool): not counted either way
    if NOTHING_LEFT_RE.search(relay.final or repeat or ""):
        return False  # "nothing left": the idle back-off below rests it and finishes it
    spins = (on_disk.spin_runs or 0) + 1
    if spins not in (SPIN_RUNS, 2 * SPIN_RUNS):
        _update(dot, spin_runs=spins)
        return False
    said, relay.final, relay.held = relay.final, "", []
    if said:
        dot.add_message("dot", said, quiet=True)
    relay.finish()
    if spins == SPIN_RUNS:
        dot.log(f"\n[spin guard] {spins} runs in a row called no tool: fresh conversation, old summary and chat "
                "context dropped\n")
        _update(dot, status="queued", next_run=_now() + 5, conv_id=None, parent_id=None, summary="",
                context=SPIN_CONTEXT, spin_runs=spins, nudges=0)
        return True
    dot.log(f"\n[spin guard] still no tool after a fresh start ({spins} runs): stopped\n")
    if _is_lane(dot):  # the lane tick starts a clean one; no text (the owner's no-chatter rule)
        _update(dot, status="stopped", spin_runs=0)
        return True
    _update(dot, status="stuck", spin_runs=0,
            summary="Stopped: its runs kept answering without doing any of the work.")
    tell_user(dot, f"heads up, {dot.label or 'that job'} got stuck repeating itself without doing anything, so I "
                   "stopped it. say \"keep going\" to try again")
    return True


def _after_run(dot, stop, relay):
    s = sc()
    on_disk = load_dot(dot.id)
    if on_disk is None or on_disk.status == "stopped":  # deleted, or they said stop while it worked
        return
    if relay.installed:
        threading.Thread(target=refresh_inventory, daemon=True).start()
    repeat = ""
    if relay.final and relay.auto_wake and not relay.tags["question"] and _same_text(relay.final, _last_said(dot)):
        # Nothing from them since, and it would only say its last text again (2026-10-21/22: jobs
        # re-texted "nothing left here" dozens of times on their own wake-ups).
        repeat, relay.final = relay.final, ""
        dot.log("\n[not texted again: the same as its last text, and nothing new from them]\n")
    if _did_no_work(dot, stop, relay):
        # 2026-11-10 audit: seven jobs in a row ran no tool, answered with an old to-do list or "I have no tools
        # in this session" (one said "Math 21 is done"), and were marked done. That answer isn't texted: the
        # job tries once more in a fresh conversation, then says plainly that nothing was done.
        said, relay.final, relay.held = relay.final, "", []
        if said:
            dot.add_message("dot", said, quiet=True)  # kept on the job's page, not texted
        relay.finish()
        tries = (on_disk.empty_runs or 0) + 1
        if tries <= EMPTY_RUN_RETRIES:
            dot.log(f"\n[no tool ran and nothing was done: not marking it done. trying again in a fresh "
                    f"conversation ({tries}/{EMPTY_RUN_RETRIES})]\n")
            _update(dot, status="queued", next_run=_now() + 5, conv_id=None, parent_id=None, empty_runs=tries,
                    runs_this_goal=max(0, dot.runs_this_goal - 1))
            return
        dot.log("\n[no tool ran again: stopped and told them nothing was done]\n")
        _update(dot, status="stuck", empty_runs=0,
                summary="Nothing has been done on this yet: the last tries answered without running any tool.")
        tell_user(dot, f"heads up, I didn't actually get anywhere on {dot.label or 'that'}: my tries answered "
                       "without doing any of the work, so nothing's been done yet. say \"keep going\" and I'll "
                       "try again")
        return
    if relay._calls and on_disk.empty_runs:
        _update(dot, empty_runs=0)
    if _spin_guard(dot, on_disk, relay, repeat):
        return
    relay.finish()
    tags = relay.tags
    summary = (relay.final or repeat or (relay.sent[-1] if relay.sent else ""))[-2500:]
    clean = stop in s._CLEAN_STOPS
    if relay.stop_watching:
        _update(dot, summary=summary or dot.summary, status="done")
        return
    if dot.kind == "watch":  # quiet checks: no "all set", no "didn't finish"
        _update(dot, summary=summary or dot.summary, status="sleeping", runs_this_goal=0,
                next_run=next_run_after(dot.schedule) or _now() + 1800)
        return
    if dot.has_followups():  # they texted more while it worked: answer that next, same chat
        _update(dot, summary=summary, status="queued", next_run=_now())
        return
    if stop in _API_HICCUPS and dot.api_errors < 4:
        # the server refused or dropped a call (busy, too
        # many at once): try again shortly without bothering them. It isn't a
        # real run, so it doesn't count towards checking in.
        _update(dot, status="queued", next_run=_now() + 15 * (dot.api_errors + 1),
                api_errors=dot.api_errors + 1, runs_this_goal=max(0, dot.runs_this_goal - 1))
        return
    if dot.api_errors:
        _update(dot, api_errors=0)
    if _autonomous(dot):
        if relay.won and dot.nudges:
            _update(dot, nudges=0)
        if relay.cut_short == "stuck":
            _carry_on(dot, summary, f"[You stopped because you repeated the same action 3 times ({relay.stuck_on}). "
                      "Don't repeat it. If you're waiting on something (an emailed code, a page), move on to the "
                      "next item and come back to it later. If it's broken, skip it, log why, and continue. "
                      "They're away: don't ask, keep going.]")
            return
        if relay.cut_short == "time" or (not clean and not tags["wait"] and dot.runs_this_goal >= LONG_MAX_RUNS):
            _carry_on(dot, summary, "[Picking up where you left off. They're away: don't check in, keep going.]")
            return
        if relay.asked_away:
            _carry_on(dot, summary, f"[You wanted to ask them: {relay.asked_away}. They're away. Make the safe, "
                      "honest call yourself, or skip that item and log it, then keep going.]")
            return
        if clean and _forever(dot) and not tags["question"]:
            # "until I tell you to stop": done with this stretch, carry on with the next.
            # It said there's nothing left (or the same thing as last time): look again in 20
            # minutes, then 40, 80, 120, not every minute (each wake texted them; the Akwaaba
            # job said "nothing left" 60+ times over 19 hours on 2026-10-21/22).
            idle = not relay.won and (bool(NOTHING_LEFT_RE.search(summary or ""))
                                      or _same_text(summary, on_disk.summary))
            idle_runs = (on_disk.idle_runs or 0) + 1 if idle else 0
            asked_for = FOREVER_RE.search(dot.goal or "") or any(
                _topic_of(t) for t in _own_standing(dot, FOREVER_RE))  # "until I say stop" about this very job
            if idle_runs >= FOREVER_IDLE_FINISH and not asked_for:
                # Endless only by a general standing rule, and nothing to do again and again: it's done.
                dot.log(f"\n[autonomous] nothing left {idle_runs} times in a row: finished\n")
                _update(dot, summary=summary or dot.summary, status="done", idle_runs=0, nudges=0)
                return
            _carry_on(dot, summary, "[They said to keep going until they say stop. Pick the next item and continue. "
                      "If there's truly nothing left you can do, say what's blocking in one line.]",
                      wait=min(AUTONOMY_NAP_SEC * 2 ** (idle_runs - 1), FOREVER_IDLE_MAX_SEC) if idle else 60)
            _update(dot, idle_runs=idle_runs)
            return
    long_job = _long_job(dot)
    max_runs = LONG_MAX_RUNS if long_job else MAX_RUNS_UNTIL_DONE
    if long_job and relay.cut_short == "time" and dot.runs_this_goal < max_runs:
        # They said to keep at it: a long run just carries on, no "want me to keep going?"
        _update(dot, summary=summary, status="queued", next_run=_now())
        return
    if relay.cut_short or (not clean and not tags["question"] and not tags["wait"]
                           and dot.runs_this_goal >= max_runs and not dot.schedule):
        check_in(dot, summary, relay.cut_short or "long")
        return
    if tags["wait"] and VM_DOWN_WAIT_RE.search(tags["wait"]):
        # 11-07: "QUESTION: ... WAIT: until my computer reconnects" parked the Amazon job on the
        # question for 80 min. The link coming back doesn't need them: wake and retry on a timer
        # (any question it asked was already texted, and their reply still reaches this job).
        wakes = (dot.wait_wakes or 0) + 1
        if wakes <= VM_DOWN_MAX_WAKES:
            _update(dot, summary=summary, status="sleeping", next_run=_now() + VM_DOWN_WAKE_SEC,
                    wait_wakes=wakes)
            return
    if tags["question"]:
        fields = dict(summary=summary, status="waiting", question=tags["question"], asking="question")
        if not on_disk.qid or on_disk.question != tags["question"]:
            fields.update(qid=uuid.uuid4().hex[:6], asked_at=_now())
        _update(dot, **fields)
        if not relay.final and not relay.q_told:
            tell_user(dot, tags["question"], ask=True)
        return
    if tags["wait"]:
        _after_wait(dot, tags["wait"], summary)
        return
    if clean or dot.runs_this_goal >= max_runs:
        nxt = next_run_after(dot.schedule)
        if nxt:
            _update(dot, summary=summary, status="sleeping", next_run=nxt, runs_this_goal=0)
        else:
            _update(dot, summary=summary, status="done" if clean else "stuck")
        if not clean:
            tell_user(dot, "I got pretty far but didn't finish. say \"keep going\" and I'll pick it back up")
        return
    _update(dot, summary=summary, status="queued", next_run=_now())  # out of steps: keep going


WAIT_FOR_THEM_RE = re.compile(r"\buntil (you|they|he|she)\b.*\b(say|tell|text|reply|answer|confirm|decide|"
                              r"give|send|get back|ok|approve)", re.I)
MAX_UNTIMED_WAKES = 3   # a WAIT with no time it can read: this many 30-minute checks, then it asks
MAX_TIMED_WAKES = 12    # a timed WAIT: this many checks before it stops polling and asks
VM_DOWN_WAIT_RE = re.compile(r"\b(dot pc|my computer|computer|vm|wsl|link|connection)\b.{0,40}"
                             r"\b(reconnect|back|down|respond|answer|up)", re.I)
VM_DOWN_WAKE_SEC = 300  # Dot PC link down: retry every 5 min ...
VM_DOWN_MAX_WAKES = 18  # ... for 90 min, then the usual WAIT handling


def _after_wait(dot, wait, summary):
    """WAIT: <how long>. "until you say go" is a question, not a timer. A timer
    keeps going only so many times (polling jobs need an end), then it asks once."""
    if WAIT_FOR_THEM_RE.search(wait) and _autonomous(dot):
        _carry_on(dot, summary, f"[You were going to wait for them ({wait}). They're away: make the safe call "
                  "yourself, or skip that item and log it, then keep going.]")
        return
    if WAIT_FOR_THEM_RE.search(wait):
        _update(dot, summary=summary, status="waiting", asking="question", question=wait,
                qid=uuid.uuid4().hex[:6], asked_at=_now(), wait_wakes=0)
        return
    nxt = next_run_after("every " + re.sub(r"(?i)^\s*(for|about|another)\s+", "", wait))
    wakes = (dot.wait_wakes or 0) + 1
    if wakes > (MAX_TIMED_WAKES if nxt else MAX_UNTIMED_WAKES) and _autonomous(dot):
        _carry_on(dot, summary, f"[You've checked {wakes - 1} times and it still isn't ready ({wait}). Stop "
                  "waiting on it: log it, move on to the next item, and look again later.]")
        return
    if wakes > (MAX_TIMED_WAKES if nxt else MAX_UNTIMED_WAKES):
        q = "I've checked a bunch of times and it's still not ready. want me to keep checking?"
        _update(dot, summary=summary, status="waiting", asking="question", question=q,
                qid=uuid.uuid4().hex[:6], asked_at=_now(), wait_wakes=0)
        tell_user(dot, q)
        return
    _update(dot, summary=summary, status="sleeping", next_run=nxt or _now() + 1800, wait_wakes=wakes)


_API_HICCUPS = ("the server returned an error", "the server returned an empty reply", "the server API call failed",
                "Rate limit (quota) blocked the send")  # out of sends for the minute: wait, it isn't a failure


def check_in(dot, summary, why):
    """Dot stopped itself (looping, too long, too many runs): say where it got
    and let them pick, instead of grinding on."""
    _update(dot, summary=summary, status="waiting", asking="question", runs_this_goal=0,
            question="want me to keep going?")
    opener = {
        "stuck": "I kept trying the same thing and it wasn't working, so I stopped instead of looping",
        "time": "this is taking a while, so I'm checking in before I keep going",
    }.get(why, "I've been at this a while and I'm not done, so checking in")
    got = summary.strip().splitlines()[-1][:300] if summary.strip() else ""
    text = opener + (f". last thing I had: {got}" if got else "") + "\nwant me to keep going?"
    tell_user(dot, text, components=_live().buttons(
        [("Keep going", f"more:{dot.id}", 1), ("Try another way", f"more:{dot.id}:other", 2),
         ("Stop", f"stop:{dot.id}", 4)]))


def _clock(t):
    return datetime.datetime.fromtimestamp(t).strftime("%I:%M %p").lstrip("0").lower()


# --- tasks: each job is its own process ---------------------------------------------
# A job runs in `pd_dots.py run <id>`, so several can go at once (period's
# globals stay per process, and its send quota is shared through a lock file),
# one can be stopped by killing it, and a daemon restart doesn't interrupt it.

MAX_PARALLEL = 3
ACTIVE = ("queued", "working", "waiting", "sleeping")
_procs = {}  # dot id -> subprocess.Popen, or a pid adopted after a restart
_NO_WINDOW = 0x08000000 if sys.platform == "win32" else 0


def active_tasks(chat=None, sleeping=False):
    """Jobs in flight (not the chat log, not reminders). Ones asleep (waiting on a
    timer or their schedule) only with sleeping=True."""
    states = ("queued", "working", "waiting") + (("sleeping",) if sleeping else ())
    return [d for d in all_dots() if d.kind not in ("chat", "reminder") and d.status in states
            and (chat is None or d.reply_to == chat)]


def stoppable_tasks():
    """What "stop everything" stops: every job in flight or asleep, from any chat,
    except the repeating watches and the brief (they keep their schedule)."""
    return [d for d in all_dots() if d.kind not in ("chat", "reminder", "watch", "brief") + NEVER_RUN
            and d.status in ACTIVE]


def _alive(entry, started=0.0):
    """Is this job process still running? With `started` (when Dot started it),
    a pid Windows has since given to another process doesn't count."""
    if entry is None:
        return False
    if isinstance(entry, int):
        try:
            import psutil
            p = psutil.Process(entry)
            ok = p.is_running() and p.status() != psutil.STATUS_ZOMBIE and "pd_dots" in " ".join(p.cmdline())
            if ok and started:
                ok = abs(p.create_time() - started) < 120
            return ok
        except Exception:
            return False
    return entry.poll() is None


LOG_ROTATE_BYTES = 5 * 1024 * 1024


def _rotate(path, limit=LOG_ROTATE_BYTES):
    """Keep a log under `limit`: past it, it becomes <name>.1 (replacing the old one)."""
    try:
        if path.stat().st_size > limit:
            os.replace(path, path.with_name(path.name + ".1"))
    except OSError:
        pass


def _spawn(dot):
    import subprocess
    _rotate(dot.folder / "process.txt")
    out = open(dot.folder / "process.txt", "a", encoding="utf-8")
    # Jobs stop at 5 of the 6 sends a minute, so a text from them always gets an instant reply.
    # A job can ask for fewer (the overnight optimizer uses 2, so it only spends quiet sends).
    # DOT_JOB tags what it starts on Dot's computer, so stopping the job stops those too.
    env = dict(os.environ, PYTHONIOENCODING="utf-8", HF_HUB_DISABLE_SYMLINKS_WARNING="1",
               SC_SOFT_PER_MINUTE=str(int(dot.sends_per_minute or 0) or JOB_SENDS_PER_MINUTE),
               DOT_JOB=dot.id)
    p = subprocess.Popen([sys.executable, "-u", str(HERE / "pd_dots.py"), "run", dot.id], cwd=str(HERE),
                         stdout=out, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         creationflags=_NO_WINDOW, env=env)
    out.close()
    _procs[dot.id] = p
    _update(dot, status="working", pid=p.pid, started=_now())


def kill_task(dot_id, status="stopped"):
    """Stop a job now: the process (and anything it started) is killed."""
    entry = _procs.pop(dot_id, None)
    d = load_dot(dot_id)
    pid = entry if isinstance(entry, int) else (entry.pid if entry is not None else (d.pid if d else 0))
    if pid:
        try:
            import psutil
            p = psutil.Process(pid)
            if "pd_dots" in " ".join(p.cmdline()):
                for child in p.children(recursive=True):
                    child.kill()
                p.kill()
        except Exception:
            pass
    threading.Thread(target=_kill_vm_side, args=(dot_id,), daemon=True, name="dot-kill-vm").start()
    if d:
        _update(d, status=status, pid=0, step="", asking="", question=None, answer=None, qid="")
    _release_screens(pid)


def _kill_vm_side(dot_id):
    """What the job started on Dot's computer (vm_run scripts, vm_claude runs) is
    tagged with its id (DOT_JOB); those processes are killed too."""
    try:
        import pd_vm
        kill = getattr(pd_vm.DotPC, "kill_job", None)
        if kill is not None:
            kill(dot_id)
    except Exception as e:
        print(f"[kill] VM side of {dot_id}: {e}", file=sys.stderr)


_mcp_ready = threading.Event()
_mcp_ready.set()


def start_mcp():
    """Connect every MCP server (~/.period/mcp.json etc.) in the background;
    run_dot waits for it just before the first model call."""
    _mcp_ready.clear()

    def go():
        try:
            sc().mcp_hub.start(quiet=True)
            errs = sc().mcp_hub.errors
            if errs:
                print(f"[mcp] failed: {errs}", file=sys.stderr)
        except Exception as e:
            print(f"[mcp] {e}", file=sys.stderr)
        finally:
            _mcp_ready.set()
    threading.Thread(target=go, daemon=True, name="dot-mcp").start()


def run_task_process(dot_id):
    """Inside the job's own process: run it until it's finished, waiting or asleep."""
    dot = load_dot(dot_id)
    if dot is None:
        return
    _update(dot, pid=os.getpid())
    if dot.kind not in ("reminder", "watch"):
        start_mcp()
    try:
        while True:
            run_dot(dot)
            dot = load_dot(dot_id)
            if dot is None or dot.status != "queued" or dot.next_run > _now() + 1:
                break
    finally:
        _release_screens(os.getpid())
        if dot is not None and load_dot(dot_id) is not None:
            _update(dot, pid=0, step="")


def _only_own_notes(dot):
    """True when the inbox holds only this program's own instructions, not a text from them."""
    try:
        rows = (dot.folder / "inbox.txt").read_text(encoding="utf-8").splitlines()
    except OSError:
        return False
    notes = []
    for row in rows:
        if not row.strip():
            continue
        try:
            notes.append(json.loads(row))
        except ValueError:
            return False
    return bool(notes) and all(str(n).lstrip().startswith("[") for n in notes)


def _reap():
    """Notice jobs whose process ended."""
    for dot_id, entry in list(_procs.items()):
        if _alive(entry):
            continue
        _procs.pop(dot_id, None)
        d = load_dot(dot_id)
        if d is None:
            continue
        if d.status == "working":  # the process died mid-job
            _update(d, status="failed", pid=0, step="")
            tell_user(d, "ugh, that one crashed on my end. want me to try it again?")
        elif d.status == "waiting" and d.asking == "ok":
            # It died holding an OK (nobody is left to act on the answer): ask again on a fresh run.
            if d.current and d.conv_id:
                d.push_followup(d.current)
            _update(d, status="queued", next_run=_now(), question=None, asking="", answer=None, qid="",
                    current="", pid=0)
        elif d.status == "queued":
            _update(d, pid=0, step="")  # _due starts it again when it's time
        elif d.status not in ("stopped",) and d.has_followups():
            # Its own "keep going" note is not a new text. Waking on it throws away the
            # 20-minute rest and makes it repeat "nothing left" a minute later.
            if not (d.status == "sleeping" and (d.next_run or 0) > _now() and _only_own_notes(d)):
                _update(d, status="queued", next_run=_now())


NEVER_RUN = ("chat", "legacy")  # chat logs and pre-task conversations are history, not work


def _due():
    now = _now()
    due = [d for d in all_dots() if d.id not in _procs and d.kind not in NEVER_RUN and
           (d.status == "queued" or (d.status == "sleeping" and d.next_run <= now))]
    return sorted(due, key=lambda d: d.next_run or d.created)


def recover_after_restart():
    """Jobs whose process still runs are adopted; jobs cut off mid-way start again."""
    for d in all_dots():
        if d.kind in NEVER_RUN:
            if d.status in ACTIVE:
                if d.pid and _alive(d.pid):
                    kill_task(d.id, status="done")
                _update(d, force=True, status="done", current="", pid=0, question=None, asking="")
            continue
        if d.pid and _alive(d.pid, d.started):
            if d.status == "stopped":
                kill_task(d.id)  # told to stop, but its process outlived the old daemon
            else:
                _procs[d.id] = d.pid  # its process is still going, whatever it says it's doing: keep it
        elif d.status == "working" or (d.status == "waiting" and d.asking == "ok"):
            if d.current and d.conv_id:
                d.push_followup(d.current)  # redo exactly the request it was on
            _update(d, status="queued", next_run=_now(), question=None, asking="", answer=None,
                    current="", pid=0)
            if d.kind not in ("reminder", "brief", "watch"):
                tell_user(d, "sorry, I got restarted. back on it")
        elif d.status == "waiting" and not d.question:
            _update(d, status="queued", next_run=_now())


def revive_parked():
    """Watchdog for "if 20 minutes go by with nothing sent, something's wrong": an
    autonomous job left waiting on a question, stuck or crashed for AUTONOMY_NAP_SEC
    is put back to work (newest one only, never next to a running one of its kind).
    Approvals (asking="ok") stay put: those are the money/safety checks."""
    now = _now()
    jobs = [d for d in all_dots() if d.kind in ("task", "job")]
    if any(d.status in ("queued", "working", "sleeping") and _autonomous(d) for d in jobs):
        return None
    parked = [d for d in jobs if d.id not in _procs and _autonomous(d) and now - (d.updated or 0) < 12 * 3600 and (
        (d.status == "waiting" and d.asking == "question" and now - (d.asked_at or d.updated) > AUTONOMY_NAP_SEC)
        or (d.status in ("stuck", "failed") and now - (d.updated or 0) > AUTONOMY_NAP_SEC))]
    if not parked:
        return None
    d = max(parked, key=lambda x: x.updated or 0)
    was = d.question or d.status
    _carry_on(d, d.summary, f"[Watchdog: this sat for {int((now - (d.updated or now)) // 60)} minutes "
              f"({was[:150]}) while they're away. Say in one line what went wrong, then fix it or skip that "
              "item and keep going. Don't ask them.]")
    return d


LOGIN_CHECK_SEC = 5 * 60
LOGIN_RETRY_SEC = 20 * 60
_login_renew = {"busy": False, "next": 0.0}


def keep_login_fresh():
    """The server session has a fixed end; refreshing past it gets "403 Invalid
    refresh token". Only a starting job renewed it, so when no job started in its
    last hour the quick brain and the watcher failed and every text became a job
    (2026-10-20 20:12). Renew it here, in the background with no window, once
    under an hour is left. Returns True when a renewal was started."""
    now = _now()
    if _login_renew["busy"] or now < _login_renew["next"]:
        return False
    s = sc()
    try:
        hours = s.login_hours_left(s.load_config())
    except Exception:
        hours = None
    if hours is None or hours > 1:
        _login_renew["next"] = now + LOGIN_CHECK_SEC
        return False
    _login_renew["busy"] = True

    def go():
        ok = False
        try:
            ok = bool(s.renew_login_if_due(s.load_config(), hours_before=1, quiet=True))
            if not ok and getattr(s, "_LOGIN_PROBLEM", [None])[0] == "remote":
                print(f"[login renew] {s.REMOTE_REFUSED_MSG}", file=sys.stderr)
            elif not ok and (s.login_hours_left(s.load_config()) or 0) <= 1:
                print("[login renew] background renewal didn't finish (the server may want a sign-in)",
                      file=sys.stderr)
        except Exception as e:
            print(f"[login renew] {str(e)[:150]}", file=sys.stderr)
        finally:
            _login_renew["next"] = _now() + (LOGIN_CHECK_SEC if ok else LOGIN_RETRY_SEC)
            _login_renew["busy"] = False

    threading.Thread(target=go, daemon=True, name="login-renew").start()
    return True


UNREAD_ALERT_SEC = 15 * 60
QUEUE_SYNC_EVERY_SEC = 10 * 60
LISTINGS_PULL_EVERY_SEC = 6 * 3600


def unread_alerts():
    """A busy job that's left their message unread for 15 minutes: tell them, once per message batch."""
    for d in active_tasks(sleeping=False):
        if d.kind not in ("task", "job") or d.status != "working":
            continue
        n, since = d.unread()
        if not n or _now() - since < UNREAD_ALERT_SEC or d.unread_alerted == since:
            continue
        first = ""
        try:
            first = json.loads((d.folder / "inbox.txt").read_text(encoding="utf-8").splitlines()[0])
        except Exception:
            pass
        busy = f" because it's tied up {d.step[0].lower() + d.step[1:]}" if d.step else " because it's mid-step"
        tell_user(d, f"heads up: {d.label or d.name} hasn't read what you sent {_ago(since)}"
                     f"{f' ({first[:90]}…)' if first else ''}{busy}. it gets to it when that step ends. "
                     f"if it shouldn't wait, tell me to make it its own job")
        _update(d, unread_alerted=since)


def queue_sync():
    try:  # the speed reflex (scripts the small asks that keep coming back slow)
        import importlib, pd_autotool
        importlib.reload(pd_autotool).tick()
    except Exception as e:
        print(f"[autotool] {e}", file=sys.stderr)


def _queue_sync_safe():
    try:
        queue_sync()
    except Exception as e:
        print(f"[queue sync] {e}", file=sys.stderr)


def worker():
    recover_after_restart()
    shown = None
    last_watch = 0.0
    last_sync = 0.0
    while True:
        try:
            _reap()
            if _now() - last_watch > 60:
                last_watch = _now()
                try:
                    revive_parked()
                except Exception:
                    traceback.print_exc()
                try:
                    keep_login_fresh()
                except Exception:
                    traceback.print_exc()
                try:
                    unread_alerts()
                except Exception:
                    traceback.print_exc()
            if _now() - last_sync > QUEUE_SYNC_EVERY_SEC:
                last_sync = _now()
                threading.Thread(target=_queue_sync_safe, daemon=True, name="dot-queue-sync").start()
            for d in _due():
                if d.kind == "reminder":
                    run_dot(d)  # just a text: no process needed
                    continue
                if len(_procs) >= MAX_PARALLEL:
                    break
                _spawn(d)
            names = sorted((load_dot(i).label or load_dot(i).name) for i in _procs if load_dot(i))
            if names != shown:
                shown = names
                gateway.working_on(", ".join(names)[:100] if names else None)
            _wake.wait(2)
            _wake.clear()
        except Exception:
            traceback.print_exc()
            time.sleep(5)  # never let one bad job take the daemon down


# Only one job at a time drives a screen's mouse and keyboard; others wait their turn.
PC_INPUT_TOOLS = ("computer_click", "computer_type", "computer_key", "computer_scroll", "computer_drag",
                  "computer_move", "app_do") + tuple(
    f"mcp_windows_{t}" for t in ("App", "Click", "Type", "Scroll", "Move", "Shortcut", "MultiSelect",
                                 "MultiEdit", "Clipboard"))
VM_INPUT_TOOLS = ("vm_click", "vm_type", "vm_key", "vm_scroll", "vm_open", "vm_fill")
# Anything that moves their mouse, types, or drives windows/tabs they can see.
ON_THEIR_SCREEN = PC_INPUT_TOOLS + (
    "browser_navigate", "browser_click", "browser_type", "browser_scroll", "browser_close",
    "tab_navigate", "tab_click", "tab_type", "tab_scroll", "tab_close", "tab_execute_js")
# Looking and waiting legitimately repeat with the same arguments.
REPEATABLE_TOOLS = ("computer_screenshot", "vm_screenshot", "tab_screenshot", "browser_screenshot",
                    "save_screenshot", "tab_list", "app_windows", "vm_read", "tasks", "update_plan",
                    "vm_claude")  # {"check": id} again = still waiting on Claude
COMPUTER_MODES = {
    "auto": "Use whichever computer fits: your own (vm_* tools) for browsing and anything visual, "
            "their PC when the job needs their apps, files or logged-in accounts.",
    "vm": "They're using their PC right now: do ALL screen work on your own computer (vm_* tools). "
          "Don't touch their mouse, keyboard, windows or Chrome tabs; those tools are switched off. "
          "Background things (mail, calendar, files, commands) are fine.",
    "pc": "They said you may work on their PC (computer_*, app_*, tab_* tools). Your own computer "
          "(vm_* tools) stays available too: use both, and keep each job on whichever computer its "
          "own instructions say (applications stay on yours).",
}
COMPUTER_MODE_HOURS = 3  # "use my pc" / "stay off my pc" is for now, not forever


def computer_mode():
    st = settings()
    m = str(st.get("computer_mode") or "auto").lower()
    if m != "auto" and _now() - float(st.get("computer_mode_at") or 0) > COMPUTER_MODE_HOURS * 3600:
        return "auto"  # a "for now" instruction from hours ago no longer applies
    return m if m in COMPUTER_MODES else "auto"


def mode_blocks(name):
    m = computer_mode()
    if m == "vm" and name in ON_THEIR_SCREEN:
        return ("they're using their PC right now, so its screen, mouse, keyboard and tabs are off "
                "limits. Do this on your own computer with the vm_* tools instead.")
    # "pc" only adds their PC; it never locks Dot out of its own computer (a PC errand on Oct 21
    # set it and froze the applications job, which must stay on Dot's computer). User: use both.
    return None


def set_computer_mode(m):
    m = {"mine": "vm", "dot": "vm", "yours": "vm", "my pc": "pc", "both": "auto"}.get(m, m)
    if m not in COMPUTER_MODES:
        return None
    st = settings()
    st["computer_mode"] = m
    st["computer_mode_at"] = _now()
    save_settings(st)
    return {"vm": "ok, I'll stay off your PC and only use my own computer for the next few hours. it's all yours 👍",
            "pc": "ok, I'll work right on your PC for now",
            "auto": "ok, I'll pick whichever computer makes sense"}[m]


def _lock_path(which):
    return DOTS_DIR / f"{which}-screen.lock"


def _lock_owner(which):
    try:
        return int(_lock_path(which).read_text())
    except Exception:
        return 0


def take_screen(which, dot, timeout=1800, tell=True):
    """Wait for the screen to be free, then hold it until this process ends."""
    me = os.getpid()
    told = not tell
    deadline = _now() + timeout
    while _now() < deadline:
        owner = _lock_owner(which)
        if owner == me:
            return True
        if not owner or not _alive(owner):
            try:
                _lock_path(which).unlink(missing_ok=True)
                fd = os.open(_lock_path(which), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(fd, str(me).encode())
                os.close(fd)
                return True
            except FileExistsError:
                continue
        if not told:
            told = True
            where = "your screen" if which == "pc" else "my computer"
            tell_user(dot, f"another job's using {where} right now, I'll jump on once it's free")
        time.sleep(2)
    return False


def _release_screens(pid):
    for which in ("pc", "vm"):
        if pid and _lock_owner(which) == pid:
            _lock_path(which).unlink(missing_ok=True)


# --- texts in: the quick brain -----------------------------------------------------
# Every DM first goes to a fast model with the recent chat, memory and what's
# running. It answers small talk and quick questions itself (a few seconds) and
# writes a natural heads-up for real jobs, which go to the full agent.

CONVERSATION_GAP_SEC = 6 * 3600  # a DM within 6 h of the last one continues that chat
FRONT_MODEL = os.environ.get("PERIOD_DOT_FRONT_MODEL", "")  # default: Period's fast model
STOP_RE = r"^(stop|cancel|nvm|never ?mind|stop it|stop that|cancel it|cancel that|stop everything|quit it)[.! ]*$"
STOP_AND_RE = (r"^\s*(stop|drop|forget|cancel|quit)( what (you'?re|youre|your|ur) doing| everything| all that| that| it)?"
               r"[\s,.!]*(and|then|&)\s+(instead\s+)?(?P<rest>.+)$")
YES_RE = r"^(y|ya|ye|yes|yeah|yea|yep|yup|ok|okay|k|kk|sure|go|go ahead|do it|approve|approved|bet|send it|yes please)[.! ]*$"
NO_RE = r"^(n|no|nope|nah|don'?t|do not|deny|skip|no thanks|cancel)\b"
NO_BARE_RE = r"^(n|no|nope|nah|don'?t|do not|deny|skip|no thanks)[.! ]*$"  # "no, use the other one" isn't bare


def _first_line(text):
    """Stop words are matched on the first line: an attached file adds lines after it."""
    lines = (text or "").strip().splitlines()
    return lines[0].strip() if lines else ""


def _is_quick(text):
    """A bare stop / yes / no: handled at once, never merged into a burst."""
    first = _first_line(text).lower()
    return bool(re.match(STOP_RE, first) or re.match(YES_RE, first) or re.match(NO_BARE_RE, first))

FRONT_PROMPT = """{persona}
You are the quick-reply side of Dot. Read their new text and decide what to do. Reply with ONLY a JSON object:
{{"say": "<what to text back right now, in Dot's voice>",
  "job": "<if it needs NEW real work on a computer, mail, files, the web or anything you can't answer from what's here: a clear, self-contained one-paragraph task for the full agent (it won't see this chat, so include every detail it needs from the chat); else null>",
  "label": "<if job: a 1-3 word name for it, like 'remote essay' or 'cs111 slides'; else null>",
  "add_to": "<if this text is about one of your jobs below (more details, a change, an answer to its question, 'also do X'): that job's id; else null>",
  "add_text": "<if add_to: what that job should now know or do, in a clear sentence; else null>",
  "cancel": "<if they want one or more of your jobs dropped: a list of their ids; else null>",
  "repeat": "<if they want something done on a schedule: like 'daily 8am', 'every 2 hours', 'weekdays 9:30'; else null>",
  "remind_at": "<if they want a reminder at a time: ISO 8601 local time; else null>",
  "remember": "<a lasting fact about them worth saving, else null>",
  "action": "<an instant action instead of a job, else null: 'screen_pc' (show their screen), 'screen_vm' (show your computer's screen), 'replay' (GIF of how your last job went), 'control_pc' / 'control_vm' (they want to drive a screen themselves), 'live' (they want to watch what you're doing right now, a live feed)>",
  "live": "<true if they want to watch the new job happen live (a live feed / screen share while it works); else null>",
  "watch": "<if they want you to keep an eye on something and tell them when it changes (a price, a grade, an email from someone, tickets): what to check and what counts as news, in one sentence; else null>",
  "watch_every": "<how often to check for that watch, like '30 minutes' or '2 hours'; else null>",
  "notify": "<if they turn your heads-ups on or off: an object like {{"inbox": false}} using keys inbox (important emails), texts (their iMessages), deadlines, brief (morning brief), live_screen; else null>",
  "computer": "<if they say which computer you may use from now on: 'vm' (only your own computer, stay off theirs, e.g. 'I'm using my pc', 'only work on the vm', 'don't touch my computer'), 'pc' (work on their PC), 'auto' (either is fine again); else null. Can come with a job in the same text.>",
  "approve": "<only if one of your jobs below is 'waiting for their OK': 'yes' if this text approves it (\"send it\", \"go\", \"do it\", even with other words around it), 'no' if it refuses it or changes what should happen (then put the change in add_to/add_text for that job); else null. A question about it (\"ok to what?\") is neither: explain it in say.>",
  "standing": "<if they set or change an on/off state or rule that should hold for every job until they change it again ('pause the applications', 'resume submissions', 'only run one job at a time', 'don't text me after midnight'): an object like {{"applications": "paused: don't submit anything until they say resume"}}, one key per topic, with the rule as it stands NOW; an empty string clears that topic; else null>",
  "fast": "<if the request is one of these everyday commands, it's done instantly in code instead of a job (then job is null and say is null): 'volume N', 'volume up', 'volume down', 'mute', 'unmute', 'unmute N', 'volume?' (their PC's sound); 'spotify volume N' / 'spotify volume up|down'; 'lights off', 'lights on', 'lights <red|orange|yellow|green|blue|purple|pink|white|warm|cyan>', 'lights <party|rainbow|flow|breathe|candle|ocean|sunset|aurora>', 'lights music' (sync to music), 'lights night' (dim warm), 'lights brightness N', 'lights?' (what they're doing now); 'weather <place>' (current weather; just 'weather' for here); 'price <bitcoin|eth|solana|doge>'; 'hn' (top Hacker News post). A list of strings for several. Else null>",
  "look": "<if job: up to 3 read-only look-ups it will surely need first, done before it starts so its first step already has them: 'mail: <gmail-style search>', 'calendar: <days ahead>', 'canvas', 'web: <search words>', 'page: <url>'; a list; else null>",
  "more": "<if the text asks for MORE THAN ONE separate thing (often several texts in a row): the first goes in the fields above and each other one is an object in this list, with the same keys (job/label/action/add_to/remind_at/...; its own say only if needed); else null>"}}
Rules:
- temporary states (paused, resume, on/off, "for now", "until I say") go in "standing", never into "add_text" or a job's task: a task keeps what to do, "standing" keeps what's true right now, and the newest standing text wins.
- never drop a request: "send me a screenshot" + "what are my lights doing" is an action AND a job (one in "more"). Your "say" can cover all of them.
- small talk, quick facts, math, advice, opinions: answer yourself in "say", job null.
- "update?", "so?", "status?", "you there?" and other questions about what you're doing: answer from "Your jobs" in "say" (what each is on right now; say plainly if nothing is running), job null. Never start work from these.
- anything that needs looking something up live, their PC, accounts, files, screen, web, sending things: put it in "job" and make "say" a short natural heads-up ("ok pulling it up", "on it, one sec" is too robotic; vary it, sound human).
- emailing or texting someone for them: the job writes it and shows them the draft before anything goes out, so "say" is like "i'll write it up so you can check it", never "sending it now". Never write "authorizes sending", "no approval needed" or "don't ask" into a job unless their own text says to send it as is ("send it", "send it now", "don't ask me").
- a vague follow-up ("do the same for X", "the other one", "that one") that fits two different things in the chat or your jobs: ask which in one short line naming both, job null. Never guess when the job would send something to someone.
- "standing" holds only what this text sets or changes, in their words. Don't restate, merge or add other rules (eligibility, scope, other topics) from memory. A one-time "cancel/stop X" is "cancel", not a standing rule (it must not block their next asks).
- a reply that doesn't answer a job's question ("lol ok", "the thing", "bro", "asdf") is not an answer: add_to null, reply in "say" (one short line asking what they mean, if needed). Never turn a vague reply into "proceed" or "send".
- a job "waiting for their OK" is paused until they answer. If they ask what it's waiting on, tell them exactly (who, what, from where) in "say". Never just repeat the question.
- several jobs can run at once. A new unrelated request is a new "job" even while others run; never fold it into a running one. Use "add_to" only when the text is clearly about that job. A job waiting on their answer gets it through "add_to".
- if they repeat a request that's already one of your jobs, don't start it again: say it's in progress (add_to if they added anything).
- "never mind the essay", "forget that", "cancel the flights": "cancel" with those ids.
- "stop what you're doing and X": cancel every job in "Your jobs" AND start X as a new job.
- "do it again" / "try again" about a finished job: a NEW job with that job's full task (from "Just finished"), plus whatever they changed. Never answer it with only "say".
- "how did you do that?": answer from that job's steps in "Just finished", plainly and confidently. Don't claim you can't know.
- "what can you do?", "what would make you better?", "what should I install?": answer from "About you" (what you have, what's missing and what each would unlock). If they say to go ahead and upgrade yourself, that's a job: install it on your own computer.
- {voice}
- their PC's volume, the lights (the LED strip) and current weather/prices/top HN post go in "fast", never a job, even with typos ("sync the lgiths to the music" = "lights music"). Something more (a schedule, other apps or devices, several steps, a forecast) is a job.
- never mention JSON, tools, agents, ids or models.

Now: {now}
About you: {self}
What you know about them:
{memory}
Standing instructions (newest wins):
{standing}
Your jobs:
{running}
Recent chat (oldest first):
{chat}
Their new text: {text}"""

FRONT_KEYS = ("say", "job", "label", "add_to", "add_text", "cancel", "repeat", "remind_at", "remember",
              "action", "watch", "watch_every", "notify", "computer", "live", "approve", "standing", "more",
              "fast", "look")


def chat_history(chat, n=14):
    """The conversation as they saw it: every Dot's messages to this chat, in order."""
    rows = []
    for d in all_dots():
        if d.reply_to == chat:
            # Step lines and background-lane notes kept only on the job's page (quiet) never reached them:
            # they aren't the conversation, and the lane writes hundreds a night.
            rows += [m for m in d.chat() if not m.get("quiet")]
    return sorted(rows, key=lambda m: m.get("t", 0))[-n:]


def jobs_text(chat):
    lines = []
    for d in active_tasks(chat, sleeping=True):
        what = d.label or d.name
        if d.status == "working":
            state = f"working, {d.step.lower()}" if d.step else "working"
            if d.started:
                state += f" (since {_clock(d.started)})"
        elif d.status == "waiting" and d.asking == "ok":
            state = f"waiting for their OK to: {d.question or 'go on'}"
        elif d.status == "waiting":
            state = f"waiting for their answer to: {d.question}" if d.question else "waiting on them"
        elif d.status == "sleeping":
            state = f"asleep, wakes at {_clock(d.next_run)}" if d.next_run else "asleep"
        else:
            state = "up next"
        n, since = d.unread()
        if n:
            state += f"; has NOT read {n} of their messages yet (oldest {_ago(since)}), so it isn't doing those yet"
        said = [m["text"].replace("\n", " ")[:160] for m in d.chat() if m.get("from") == "dot"][-2:]
        lines.append(f"- id {d.id} · {what}: {state} (runs {d.runs}, sends {d.sends})"
                     f"\n  task: {d.goal.splitlines()[0][:200]}"
                     + "".join(f"\n  it texted: {t}" for t in said))
    out = "\n".join(lines) or "(none, you're free)"
    recent = sorted((d for d in all_dots() if d.reply_to == chat and d.kind in ("task", "job")
                     and d.status in ("done", "stuck", "failed", "stopped") and _now() - d.updated < 3 * 3600),
                    key=lambda d: -d.updated)[:3]
    if recent:
        out += "\nJust finished (use this to answer \"how did you do that\" or \"do it again\"):"
        for d in recent:
            steps = "; ".join(d.trail[-10:]) or "no screen or tool steps recorded"
            out += (f"\n- id {d.id} · {d.label or d.name} ({d.status} at {_clock(d.updated)})"
                    f"\n  steps: {steps[:700]}\n  result: {(d.summary or '').strip()[:300]}")
    return out


def front_brain(text, chat):
    """One fast call -> dict of FRONT_KEYS, or None if it failed."""
    s = sc()
    from rich.console import Console
    s._console_override.console = Console(file=io.StringIO())  # keep its spinner out of logs
    try:
        config = s.load_config()
        token = s.refresh_token(config, allow_browser_sync=False)
        if not token:
            return None
        history = "\n".join(f"{'them' if m['from'] == 'you' else 'you'}: {m['text'][:400]}"
                            for m in chat_history(chat, 14))
        prompt = _front_template().format(
            persona=PERSONA, voice=DOT_STYLE.split(" When a job")[0], now=datetime.datetime.now().strftime("%A %b %d %Y, %I:%M %p"),
            memory=memory_for(text) or "(nothing yet)", standing=standing_text() or "(none)",
            running=jobs_text(chat), chat=history or "(new chat)", text=text, self=self_text(short=True))
        model = FRONT_MODEL or s.FAST_STEP_MODEL
        plan = None
        for _try in range(2):  # an empty or broken plan gets one more try, never silence
            reply, _c, _p = s.call_api(prompt, model, s.MODEL_ENDPOINTS.get(model, s.DEFAULT_ENDPOINT), token, config)
            head = reply.lstrip()[:60] if isinstance(reply, str) else ""
            if head.startswith(("[Error", "[bold red][Error]")):
                # An API error, not an empty plan: its JSON body isn't a plan. Only a
                # dropped connection or a 5xx is worth one more send.
                print(f"[front brain] {head}", file=sys.stderr)
                if head.startswith("[Error connecting") or re.match(r"\[Error HTTP 5\d\d\]", head):
                    continue
                return None
            m = re.search(r"\{[\s\S]*\}", reply or "")
            try:
                data = json.loads(m.group(0)) if m else {}
            except ValueError:
                data = {}
            plan = {k: (data.get(k) or None) for k in FRONT_KEYS}
            if any(plan.values()):
                break
        if not plan or not any(plan.values()):
            return None
        try:
            _rotate(DOTS_DIR / "front.log")
            with open(DOTS_DIR / "front.log", "a", encoding="utf-8") as f:
                f.write(redact(json.dumps({"t": _stamp(), "text": text[:300],
                                           "plan": {k: v for k, v in plan.items() if v}}, ensure_ascii=False)) + "\n")
        except Exception:
            pass
        return plan
    except Exception as e:
        print(f"[front brain] {e}", file=sys.stderr)
        return None
    finally:
        s._console_override.console = None


def _conversation_for(chat):
    """The chat log with this person: what they said and Dot's quick replies. It never
    runs anything itself; each job is its own task."""
    mine = [d for d in all_dots() if d.reply_to == chat and d.kind == "chat"]
    if mine:
        def last_said(x):
            rows = x.chat()
            return rows[-1].get("t", x.updated) if rows else x.updated
        d = max(mine, key=last_said)
        if _now() - last_said(d) < CONVERSATION_GAP_SEC:
            return d
    d = Dot(id=datetime.datetime.now().strftime("%m%d-") + uuid.uuid4().hex[:5], name="Chat", goal="chat",
            created=_now(), source="text", reply_to=chat, kind="chat", status="done")
    d.save()
    return d


SCREEN_PC_RE = r"^(ss|screenshot|screen|my screen|show (me )?(my|the) screen|what'?s on my screen|send (me )?(a )?screenshot)[?.! ]*$"
SCREEN_VM_RE = r"^(your screen|show (me )?your screen|what'?s on your screen|dot ?pc|your (pc|computer))[?.! ]*$"
REPLAY_RE = r"^(replay|show me (a )?replay|show me how you did (it|that)|how'?d you do (it|that))[?.! ]*$"
STATUS_RE = r"^(status|update|updates|so|and|\?+|any update|whats? up with it|you there|hello\?*|you good)[?.! ]*$"
# "is it really happening?" questions: answered from what's actually running, never by the quick brain
DOING_RE = (r"^(what (are|r) (you|u) (doing|working on)( right ?n ?ow| rn| now)?|what'?s (running|going on)( right ?now| rn)?|"
            r"(are|r) (you|u) (actually |really |even )?(doing|working on|running) (that|it|this|anything)|"
            r"did (you|u) (actually |really |even )?(start|do) (that|it)|is (that|it) (actually |really )?(running|happening))[?.! ]*$")


def _ago(t):
    m = int((_now() - t) // 60)
    return "just now" if m < 1 else f"{m} min ago" if m < 90 else f"{m // 60}h ago"


def status_text(chat):
    """What's really going on, from the job records and their logs (nothing the model says)."""
    mine = [d for d in all_dots() if d.reply_to == chat and d.kind != "chat" and d.status in ACTIVE]
    if not mine:
        return "nothing is running right now, I'm free. if I said I'd do something, it didn't start: tell me again"
    lines = []
    for d in sorted(mine, key=lambda d: (d.status != "working", d.status == "sleeping", -d.updated))[:8]:
        what = d.label or d.name
        extra = ""
        if d.status == "working":
            if d.started:
                extra = f" (since {_clock(d.started)})"
            if d.step:
                extra += f", {d.step[0].lower() + d.step[1:]}"
            try:
                extra += f", last did something {_ago(d.log_path.stat().st_mtime)}"
            except OSError:
                pass
        elif d.status == "waiting" and d.question:
            extra = f": {d.question}"
        elif d.status == "sleeping" and d.next_run:
            extra = f" (next at {_clock(d.next_run)})"
        n, since = d.unread()
        if n:
            extra += f". hasn't read {n} message{'s' if n > 1 else ''} from you yet (oldest {_ago(since)})"
        lines.append(f"• {what}: {STATUS_PLAIN.get(d.status, d.status)}{extra}")
    return "\n".join(lines)


def stop_all(chat=None, names=None):
    """Stop every job: working, queued, waiting or asleep, from any chat (a job
    asleep on a timer woke up 30 minutes after "stop everything"). Repeating ones
    (watches, the brief) keep their schedule. The reply says what actually stopped."""
    tasks = stoppable_tasks()
    stopped = []
    for d in tasks:
        if d.schedule and d.kind == "job":
            # A repeating job they set up ("every day at 8am...") stops what it's
            # doing now but keeps its schedule; asleep, it's left alone.
            if d.status == "sleeping":
                continue
            kill_task(d.id, status="sleeping")
            _update(load_dot(d.id) or d, next_run=next_run_after(d.schedule) or _now() + 86400)
        else:
            kill_task(d.id)
        stopped.append(d)
    tasks = stopped
    stopped = [d.label or d.name for d in tasks]
    if names is not None:
        names.extend(stopped)
    if not stopped:
        return "I wasn't doing anything 🤷"
    return "ok, stopped everything: " + ", ".join(stopped[:8]) + (f" and {len(stopped) - 8} more" if len(stopped) > 8 else "")


def set_notify(what, on):
    st = settings()
    if what == "live_screen":
        st["live_screen"] = bool(on)
    else:
        st.setdefault("notify", {})[what] = bool(on)
        st.setdefault("notify_at", {})[what] = _now()  # a brief stopped after this turns it off again
    save_settings(st)
    if what == "brief":
        try:
            import pd_dotwatch
            pd_dotwatch.ensure_brief()
        except Exception:
            traceback.print_exc()


def go_live(chat):
    """Show what's happening right now: working jobs start their live screen."""
    if is_imessage_chat(chat):  # a text thread can't stream: a picture of the screen instead
        which = "pc" if computer_mode() == "pc" else "vm"
        _live().send_screenshot(chat, which)
        return "can't stream over text (the live feed is in our Discord DM), that's the screen right now"
    working = [t for t in active_tasks(chat) if t.status == "working"]
    for t in working:
        _update(t, live=True)
    if working:
        return "🔴 going live, the feed's coming up right here"
    which = "pc" if computer_mode() == "pc" else "vm"
    _live().send_screenshot(chat, which)
    where = "your screen" if which == "pc" else "my computer"
    return f"nothing's running right now, that's {where} as it is. tell me what to do and I'll stream it"


LIVE_RE = (r"^((give me |show me |send me )?(a |the )?(live|live ?feed|live ?view|live ?stream|stream)|go live|"
           r"let me (see|watch)( it| what'?s happening)?|watch live)[.!? ]*$")
KEEP_GOING_RE = r"^(keep going|continue|go on|carry on|finish it|keep at it)[.! ]*$"


def _instant(chat, action):
    """Screenshots, replays and remote control: answered without the agent."""
    L = _live()
    if action in ("screen_pc", "screen_vm"):
        sent = L.send_screenshot(chat, "vm" if action == "screen_vm" else "pc")
        note = ("[sent them a picture of " + ("my computer's" if action == "screen_vm" else "their") + " screen]"
                if sent else "[couldn't get the screenshot]")
    elif action == "replay":
        L.send_replay(chat)
        note = "[sent them a replay of my last job]"
    elif action in ("control_pc", "control_vm") and is_imessage_chat(chat):
        say_to(chat, "driving the screen yourself needs the tap grid in our Discord DM, it can't work over text. "
                     "or just tell me what to click and I'll do it")
        return True
    elif action in ("control_pc", "control_vm"):
        L.control_start(chat, "vm" if action == "control_vm" else "pc")
        note = "[handed them remote control]"
    else:
        return False
    try:  # so the chat history (and the quick brain) knows it happened
        _conversation_for(chat).add_message("dot", note)
    except Exception:
        pass
    return True


def handle_text(address, chat, text, files=(), msg_id=None):
    """A text to Dot: a yes/no it asked for, "stop", or anything else (quick brain)."""
    L = _live()
    channel = L.channel_of(chat)
    if msg_id:
        L.react(channel, msg_id, "👀")
    text = (text or "").strip()
    voice = [f for f in files if L.is_audio(f)]
    for f in voice:
        try:
            heard = L.transcribe(f)
        except Exception as e:
            print(f"[voice] {e}", file=sys.stderr)
            heard = ""
        if heard:
            text = (text + " " + heard).strip()
        elif not text:
            send_to(chat, "couldn't make out that voice message, mind trying again or typing it?")
            return
    files = [f for f in files if f not in voice]
    if is_imessage_chat(chat) and not files:
        # No buttons in a text thread: the application question showing gets this text as its answer,
        # and "2" picks option 2 of the last "text 1, 2 or 3" Dot sent.
        picked = _imsg_pick(chat, text)
        if picked is True:
            return
        if picked:
            text = picked
    if files:
        text += "".join(f'\n[they sent a file, saved at "{f}"' +
                        (" (a picture: use read_file on it to see it)]" if f.lower().endswith(
                            (".png", ".jpg", ".jpeg", ".gif", ".webp", ".heic")) else "]") for f in files)
    low = text.lower().strip()
    if L.control_handle(chat, text):
        return
    for pattern, action in ((SCREEN_PC_RE, "screen_pc"), (SCREEN_VM_RE, "screen_vm"), (REPLAY_RE, "replay")):
        if re.match(pattern, low):
            _instant(chat, action)
            return
    if re.match(LIVE_RE, low):
        say_to(chat, go_live(chat))
        return
    if re.match(MORE_RE, low):
        rest = _more_pop()
        if rest:
            say_to(chat, rest)
            if msg_id:
                L.react(channel, msg_id, "👀", on=False)
            return
    # Stop comes before any yes/no ("cancel" is a stop, not a "no"), and it's read
    # from the first line, so a file sent along with "stop everything" still stops.
    stopped = None
    if re.match(STOP_RE, _first_line(low)):
        stopped = []
        say_to(chat, stop_all(chat, stopped))
        rest = "\n".join(l for l in text.splitlines()[1:] if l.strip() and not l.strip().startswith("[they sent a file"))
        if not rest.strip():
            if msg_id:
                L.react(channel, msg_id, "👀", on=False)
            return
        text, low = rest.strip(), rest.strip().lower()
    else:
        m = re.match(STOP_AND_RE, text, re.I | re.S)
        if m and stoppable_tasks():
            stopped = []
            stop_all(chat, stopped)
            text = m.group("rest").strip()
            low = text.lower()
    # A bare yes/no answers the OK it asked for, if that's still fresh. "no, use the
    # other one" carries more than a no: the quick brain passes it on (approve + add_to).
    approving = sorted((t for t in all_dots() if t.status == "waiting" and t.asking == "ok"
                        and t.reply_to == chat and _fresh_question(t)), key=lambda t: -(t.asked_at or t.updated))
    if approving and (re.match(YES_RE, low) or re.match(NO_BARE_RE, low)):
        d = approving[0]
        d.add_message("you", text)
        _update(d, answer=text)
        if msg_id:
            L.react(channel, msg_id, "👀", on=False)
        return
    # Anything else while a job waits for an OK ("ok to what?", "send it but say X")
    # goes through as normal; the quick brain sees what's waiting and can explain
    # it or answer it ("approve").
    d = _conversation_for(chat)
    d.add_message("you", text)
    tasks = active_tasks(chat)
    if re.match(DOING_RE, low) or (re.match(STATUS_RE, low) and any(t.status in ("working", "queued") for t in tasks)):
        reply = status_text(chat)
        d.add_message("dot", reply)
        send_to(chat, reply)
        return
    # Everyday asks (volume, the LED strip, weather, prices, top HN post) are done in code:
    # no quick-brain send and no job (pd_fast). Anything it isn't sure of falls through.
    try:
        fast = None if files or stopped is not None else _sc_fast().answer(text)
    except Exception as e:
        print(f"[fast] {e}", file=sys.stderr)
        fast = None
    if fast:
        d.add_message("dot", fast)
        send_to(chat, fast)
        if msg_id:
            L.react(channel, msg_id, "👀", on=False)
        return
    # A bare yes/no/keep going only answers a question asked in the last 30 minutes.
    waiting = [t for t in tasks if t.status == "waiting" and t.asking == "question" and _fresh_question(t)]
    if len(waiting) == 1 and any(re.match(p, low) for p in (YES_RE, NO_BARE_RE, KEEP_GOING_RE)):
        plan = {"add_to": waiting[0].id, "add_text": text}  # a plain answer: no quick-brain call needed
    else:
        _typing_ping(chat)  # the quick brain answers in a few seconds
        plan = front_brain(text, chat)
    if plan is None:  # quick brain unavailable: a lone question waiting on them gets it, else it's a new job
        if approving and re.match(NO_RE, low):
            plan = {"approve": "no", "add_to": approving[0].id, "add_text": text}
        else:
            plan = {"add_to": waiting[0].id, "add_text": text} if len(waiting) == 1 else {"job": text}
    _carry_out(plan, chat, text, d, msg_id, stopped=stopped)
    # Several asks in one go ("send me a screenshot. also what are my lights doing"):
    # each extra one is carried out the same way, so none gets dropped.
    for extra in (plan.get("more") or [])[:4]:
        if isinstance(extra, dict):
            _carry_out(extra, chat, text, d, None, stopped=stopped)
    _wake.set()


def _fresh_question(t):
    """Its question was asked under 30 minutes ago (older ones count as unanswered)."""
    return _now() - (t.asked_at or t.updated or 0) < QUESTION_TIMEOUT_SEC


# One job per topic: a second "do my applications" joins the one already going
# (two application jobs undid each other's work).
JOB_TOPICS = {
    "applications": r"\b(appl(y|ying|ication|ications)|internships?|greenhouse|lever\.co|workday|ashby|job postings?)\b",
    "linkedin": r"\b(linkedin|referrals?)\b",
}


# A job about keeping records of the applications (a tracker spreadsheet) is its own job:
# folded into the applying job, it was never started.
NOT_A_TOPIC_JOB_RE = re.compile(r"\b(spreadsheets?|sheets?|trackers?|tracking|track|xlsx|csv|dashboard|log of)\b", re.I)


def _topic_of(text):
    if NOT_A_TOPIC_JOB_RE.search(text or ""):
        return None
    for topic, pattern in JOB_TOPICS.items():
        if re.search(pattern, text or "", re.I):
            return topic
    return None


def _lead(text):
    """The opening sentence: what a job is about, not what it mentions in passing."""
    return re.split(r"(?<=[.!?])\s", (text or "").strip(), maxsplit=1)[0][:200]


# 2026-11-04 owner ("why is it moving so slow i asked it multiple queries"): a Wells Fargo link, an Amazon link,
# "what should I do today" and a Garner email were all folded into the portal lane, which did them one by one
# between its own audits (40+ min). A lane only takes asks about running the lanes; anything else is its own job.
LANE_CONTROL_RE = re.compile(r"\b(stop|pause|halt|resume|restart|unpause|keep|go back to|start|continue|turn (on|off))\b"
                             r".{0,40}\b(appl\w*|lanes?|the run)\b|\b(lanes?|the run)\b.{0,20}\b(stop|pause|resume|restart)",
                             re.I)
LANE_SIDE_NOTE = ("(Separate from the application lanes, which keep running in the background: don't start, stop or "
                  "restart them. To apply to a role, check it and add it with ~/tools/owner_add.py, and the lanes apply; "
                  "apply yourself only if no lane can handle it.)")


def _is_lane(t):
    return str(getattr(t, "label", "") or "").startswith("Dot lane")


_RUN_JOB_RE = re.compile(r"\b(keep (applying|going)|running until|until (i|you|told)\b.{0,25}\bstop)", re.I)


def _joinable(t, goal):
    """One job per topic is for the long application RUN (two runs undid each other's work). A one-off ask
    ("apply to this link", "what should I do today") doesn't wait behind another one-off ask."""
    if _is_lane(t):
        return _lane_takes(t, goal)
    if _RUN_JOB_RE.search(f"{t.goal} {t.label}"):
        return True
    return not (re.search(r"https?://", t.goal or "") or re.search(r"https?://", goal or ""))  # a link is a one-off


_NEW_ASK_RE = re.compile(r"https?://|\b(make|create|gather|put|send|email|text|find|look up|search|build|write|upload|"
                         r"download|open|apply to|start with|go through|remind|schedule|tell me|what|why|how|when)\b", re.I)


def _lane_takes(t, text):
    """The background lane should get this text: it's about running the lanes, or answers the lane's own question.
    2026-11-11: while the lane was asking something, ANY text went to it: "start with math 21 and ask me before you
    do something" and the Drive-folder asks landed in the lane, which then looped 963 runs on that to-do list instead
    of applying. Only a short reply that isn't itself a new ask answers its question now."""
    if LANE_CONTROL_RE.search(text or ""):
        return True
    if not getattr(t, "asking", ""):
        return False
    return len((text or "").split()) <= 8 and not _NEW_ASK_RE.search(text or "")


def _same_topic_job(goal, chat):
    """A job in flight or asleep on the same topic as this new one, or None.
    Only the new job's opening sentence decides its topic: a calendar job that says
    "keep the internship application job separate" is not an applications job."""
    topic = _topic_of(_lead(goal))
    if not topic:
        return None
    same = [t for t in active_tasks(chat, sleeping=True) if t.kind in ("task", "job")
            and _topic_of(f"{t.label} {_lead(t.goal)}") == topic and _joinable(t, goal)]
    # (2026-11-10 audit: the job's own opening decides its topic too. "Review the message ... in the Roblox
    # email" mentioned an "intern application" further on, so "send the link for capital one" ran inside it.)
    return sorted(same, key=lambda t: (t.status != "working", -t.updated))[0] if same else None


def _pass_on(target, text):
    """Give a job more to know or do: it reads it at once if it's running, or wakes for it."""
    target.push_followup(text)
    if target.asking == "ok":
        return  # paused on an OK: it reads the answer, then picks this up when that step ends
    if target.status != "working":
        _update(target, status="queued", question=None, asking="", answer=None, next_run=_now(),
                runs_this_goal=0, wait_wakes=0)


_CLAIMS_WORK_RE = re.compile(r"\b((i['’]?ll|i will) (?!be\b|let\b|keep\b|stay\b|wait\b|ping\b|text\b|tell\b|remember\b|"
                             r"note\b|try\b|leave\b|hold\b|not\b|never\b|skip\b|stop\b|pause\b|hang\b|check with\b)|i['’]?m (starting|setting|getting|going to|on it|pulling|searching|making|building)|"
                             r"starting (it|that|this|the|now|on)|on it)\b", re.I)
_CLAIMS_STOP_RE = re.compile(r"\b(stopped|stopping|cancell?ed|cancell?ing|dropped|killed|halted|shut (it|that|them) down)\b", re.I)


# 2026-11-05 audit: "email profesor gregg sayin ill miss lecture tmrw" became a job that said "The user explicitly
# authorizes sending without further approval" (and "create an email to hrt" did the same on 10-22). Jobs run on full
# auto, so the job's prompt is the only draft-first gate, and that line overrode it: the email went out unseen.
OWNER_SEND_RE = re.compile(r"(?<!my )(?<!the )(?<!ur )(?<!your )(?<!an )(?<!a )(?<!in )(?<!this )(?<!that )"
                           r"\b(e-?m[ai]{1,2}l+|text|txt|msg|message|dm|reply( back)?( to)?|respond( to)?|write( back)?( to)?|"
                           r"follow up with|(send|create|craete|creat|make|write|draft|compose) (an? |the )?"
                           r"(e-?m[ai]{1,2}l+|text|message|note|reply|dm)( to)?)\s+"
                           r"(?!me\b|myself\b|u\b|from\b|for\b|about\b|inbox|thread|account|address)\w", re.I)
OWNER_SAYS_SEND_RE = re.compile(r"\bsend (it|that|this|them|those|both|the (e-?mail|text|message|reply|draft)s?)\b|"
                                r"\b(just|go ahead and|ok) send\b|\bsend\b[^.?!\n]{0,60}\b(now|rn|asap)\b|"
                                r"\bdon'?t (ask|show) me\b|\bno need to (ask|show)\b|\bwithout asking\b", re.I)
_PRE_OK_RE = re.compile(r"[^.\n]*\b(authori[sz]\w*|without (further |another |any )?(approval|confirmation|asking|"
                        r"draft review|review))\b[^.\n]*\.?", re.I)
DRAFT_FIRST_NOTE = ("(They haven't seen this message yet: write it, then show them who it goes to, the subject and the "
                    "full text, and ask \"QUESTION: send it?\" before sending anything.)")


# The job itself sends something to someone (live case V1: "do the same for the wells fargo one" became "Draft and send
# a concise sincere apology in the correct verified Wells Fargo thread", though their text named no send at all).
JOB_SENDS_RE = re.compile(r"(?<!not )(?<!never )(?<!n't )(?<!no )\b(draft and send|send (a|an|the|this|that|it|them|both)\b(?! (user|owner)\b)|send(ing)? (an? )?"
                          r"(e-?mail|text|message|reply|apology|follow[- ]?up|note)|reply (to|in|on)|email (the|their|his|her)\b)",
                          re.I)


def _draft_first(job, text):
    """A job that writes to someone for them starts at a draft, unless their own text says to send it."""
    if not job or OWNER_SAYS_SEND_RE.search(text or ""):
        return job
    if not (OWNER_SEND_RE.search(text or "") or JOB_SENDS_RE.search(job)):
        return job
    kept = _PRE_OK_RE.sub(lambda m: "" if re.search(r"\b(send\w*|repl\w*|e-?mail\w*|text\w*|messag\w*)\b",
                                                   m.group(0), re.I) else m.group(0), job)
    return re.sub(r"\s{2,}", " ", kept).strip() + "\n" + DRAFT_FIRST_NOTE


def _carry_out(plan, chat, text, d, msg_id=None, stopped=None):
    """Do what the quick brain decided for one request. Every part of the plan is
    done (no part ends it early), in this order: settings, cancel, approve, then
    add_to / job / reminder / repeat, the instant action, the watch, and last the
    reply. `stopped`: names of jobs a stop in this same text already ended."""
    L = _live()
    channel = L.channel_of(chat)
    say = plan.get("say")
    answered = False  # something already replied for this request (so `say` isn't sent too)
    job = plan.get("job")
    if plan.get("remember"):
        remember(plan["remember"])
    if isinstance(plan.get("notify"), dict):
        for what, on in plan["notify"].items():
            if what in ("inbox", "texts", "deadlines", "brief", "live_screen", "followups"):
                set_notify(what, bool(on))
    if isinstance(plan.get("standing"), dict):
        for topic, rule in plan["standing"].items():
            set_standing(topic, rule)
    if plan.get("computer"):
        said = set_computer_mode(str(plan["computer"]).lower())
        if said and not say and not job and not plan.get("add_to"):
            d.add_message("dot", said)
            send_to(chat, said)
            answered = True
    # 1. cancel (any of its jobs, from any chat)
    cancelled = list(stopped or [])
    ids = plan.get("cancel") or []
    for tid in ([ids] if isinstance(ids, str) else ids):
        t = load_dot(str(tid))
        if t and t.kind not in NEVER_RUN and t.status in ACTIVE:
            kill_task(t.id)
            cancelled.append(t.label or t.name)
    # 2. approve the newest OK it's waiting on
    if plan.get("approve") in ("yes", "no"):
        waiting_ok = sorted((w for w in all_dots() if w.status == "waiting" and w.asking == "ok"
                             and w.reply_to == chat), key=lambda w: -(w.asked_at or w.updated))
        if waiting_ok:
            _update(waiting_ok[0], answer=plan["approve"])
    # 3. the work: add to a job, start one, a reminder, a repeat
    used_job = False  # the job text went into a reminder or a repeat instead
    if plan.get("remind_at"):
        try:
            when = datetime.datetime.fromisoformat(str(plan["remind_at"])).timestamp()
            r = new_dot(f"⏰ {job or text}", source="text", reply_to=chat, kind="reminder")
            _update(r, status="sleeping", next_run=when, goal=_reminder_text(text))
            say = say or f"got it, I'll remind you at {_clock(when)}"
            used_job = True
        except Exception:
            pass
    if plan.get("repeat") and job and not used_job:
        r = new_dot(job, schedule=plan["repeat"], source="text", reply_to=chat, kind="job")
        _update(r, label=plan.get("label") or r.name)
        used_job = True
    target = load_dot(str(plan["add_to"])) if plan.get("add_to") else None
    if target is not None and (target.reply_to != chat or target.status not in ACTIVE + ("done", "stuck")):
        target = None  # never revives a stopped job
    if target is not None and _is_lane(target) and not _lane_takes(target, text):
        job = job or text  # a one-off ask: its own job starts now instead of waiting behind the lane's work
        target = None
    started = None
    if target is not None:
        note = plan.get("add_text") or text
        if target.status == "waiting" and target.asking == "question" and plan.get("add_text") and \
                len((text or "").split()) <= 6 and len(note) > 3 * len(text or "") and \
                (text or "").strip().lower() not in note.lower():
            # Their own words go first: the job checks them against its question (a reply like "the thing" or
            # "lol ok" is not an answer, whatever the quick read says).
            note = (f'Their reply to your question, word for word: "{(text or "").strip()[:600]}"\n'
                    f"(The quick read of it, which can be wrong: {note})")
        _pass_on(target, note)
        started = target
    if plan.get("fast") and not used_job and target is None:
        try:  # an everyday command (volume, lights, weather...): done in code, no job (pd_fast)
            done = _sc_fast().run_spec(plan["fast"], text)
        except Exception as e:
            print(f"[fast] {e}", file=sys.stderr)
            done = None
        if done:
            say, job = done, None  # already done: what happened is the reply
        elif not job:
            job = text  # the quick way didn't work: the full agent does it
    if not job and not used_job and target is None and say and "?" not in say and _CLAIMS_WORK_RE.search(say) and not any(
            plan.get(k) for k in ("remember", "standing", "notify", "computer", "cancel", "approve",
                                  "action", "watch", "remind_at", "fast")):
        job = text  # it said it would do something: that something starts as a job
    if job and not used_job:
        job = _draft_first(job, text)
        same = _same_topic_job(job, chat)
        if same is not None and NOT_A_TOPIC_JOB_RE.search(plan.get("label") or ""):
            same = None  # named as a tracker, not more applying: it runs as its own job
        if same is not None:  # one job per topic: this joins the one already on it
            if target is None or same.id != target.id:
                _pass_on(same, job)
            started = started or same
        else:
            context = "\n".join(f"{'them' if m['from'] == 'you' else 'you'}: {m['text'][:300]}"
                                for m in chat_history(chat, 8))
            if any(_is_lane(t) for t in active_tasks(chat, sleeping=True)):
                context = (context + "\n" + LANE_SIDE_NOTE).strip()
            new = new_dot(job, source="text", reply_to=chat, kind="task")
            looks = plan.get("look")
            _update(new, label=plan.get("label") or new.name, context=context,
                    live=bool(plan.get("live") or plan.get("action") == "live"),
                    look=([looks] if isinstance(looks, str) else [str(x) for x in looks if x][:3])
                    if isinstance(looks, (str, list)) else [])
            started = started or new
    # 4. the instant action
    action = plan.get("action")
    if action == "live" and not job:
        reply = go_live(chat)
        d.add_message("dot", reply)
        send_to(chat, reply)
        answered = True
    elif action and action != "live" and _instant(chat, action):
        if action.startswith("control") and not (job or plan.get("add_to")):
            answered = True  # control mode explains itself
    # 5. a watch
    if plan.get("watch"):
        every = str(plan.get("watch_every") or "30 minutes")
        goal = (f"Keep an eye on this for them: {plan['watch']}\nEach check: look it up. If there's news "
                f"worth a text since your last check, text it in one or two lines. If nothing changed, reply "
                f"with exactly {NOTHING_NEW}. If it's over for good (it happened, or can't happen anymore), "
                f"tell them and add {STOP_WATCHING} at the end.")
        w = new_dot(goal, schedule=f"every {every}", source="text", reply_to=chat, kind="watch",
                    model=getattr(sc(), "FAST_STEP_MODEL", ""))
        w.name = _short_name(plan["watch"])
        _update(w, name=w.name, label=plan.get("label") or w.name)
        say = say or f"got it, I'll check every {every} and text you when something changes"
    # 6. the reply. It never claims a stop the code didn't do.
    # (A pause through "standing", or heads-ups turned off, is a real stop of its own kind.)
    if say and _CLAIMS_STOP_RE.search(say) and not cancelled and not any(
            plan.get(k) for k in ("standing", "notify", "computer", "add_to")):
        say = "hm, I didn't have anything like that running, so there was nothing to stop" + (
            ". on the rest of it now" if started is not None else "")
    if say and not answered:
        tell_user(d, say)
        if target is not None:
            try:  # the job's own process sees this quick reply and doesn't repeat it
                _update(target, told_at=_now())
            except Exception:
                pass
    elif started is not None and not answered and is_imessage_chat(chat) and not (msg_id and line.private_api()):
        tell_user(d, "on it 👍" if job else "got it 👍")  # no tapback to show it took the job, so a short text
    if msg_id:
        if started is not None:
            _triggers[started.id] = (chat, msg_id)
            _update(started, trigger=str(msg_id))  # its texts reply to this message (jobs run in their own process)
            if is_imessage_chat(chat):
                line.react(chat, msg_id, "like")  # 👍 on their text: it's queued (Private API only)
        else:
            L.react(channel, msg_id, "👀", on=False)


_WHEN = (r"(in\s+(a|an|\d+)\s*(sec\w*|min\w*|hours?|hrs?|days?)|at\s+\d{1,2}(:\d{2})?\s*(am|pm)?|"
         r"tomorrow( morning| night| at \d{1,2}(:\d{2})?\s*(am|pm)?)?|tonight|this (morning|afternoon|evening)|"
         r"on\s+\w+day|later)")


def _reminder_text(text):
    """'remind me in 2 minutes to drink water' -> 'hey, reminder: drink water'."""
    t = re.sub(r"(?i)^\s*(hey\s+|yo\s+)?(dot\s*,?\s*)?(can you\s+|could you\s+|please\s+|pls\s+)?remind me\s*", "", text)
    for _ in range(2):  # the time can come before or after the thing ("in 5 min to X", "to X at 5")
        t = re.sub(rf"(?i)^\s*{_WHEN}\s*(,\s*)?", "", t)
        t = re.sub(rf"(?i)\s*,?\s*{_WHEN}\s*[.!]?\s*$", "", t)
    t = re.sub(r"(?i)^\s*(to|that|about)\s+", "", t).strip(" .!") or text
    return f"hey, reminder: {t}"


STATUS_PLAIN = {"queued": "up next", "working": "working on it", "waiting": "waiting on you",
                "sleeping": "sleeping", "done": "done", "failed": "hit a problem", "stuck": "stuck"}


def line_loop():
    import queue
    failing = {}
    while True:
        # Live DMs from the gateway are handled the moment they arrive; the
        # polling below is the fallback (every 5 s, or 30 s while live).
        deadline = _now() + (30 if gateway.connected else LINE_POLL_SEC)
        while _now() < deadline:
            try:
                item = gateway.incoming.get(timeout=0.5)
            except queue.Empty:
                continue
            _safe_handle(*_take_burst(item))
        for ch in CHANNELS:
            name = type(ch).__name__
            if ch is line and _imsg_loop_on[0]:
                continue  # imessage_loop checks Dot's line every 2 s and queues its texts
            try:
                if ch.connected():
                    for item in ch.poll():
                        _safe_handle(*item)
                failing[name] = False
            except Exception as e:
                if not failing.get(name):
                    print(f"[{name}] {e}", file=sys.stderr)
                failing[name] = True


def _take_burst(item):
    """People text in bursts ("yo" / "find me a flight" / "to nyc"). Texts from the same
    chat that land within BURST_SEC of each other become one message: one quick-brain
    call instead of three, and no half-understood jobs."""
    import queue
    address, chat, text, files, msg_id = (list(item) + [(), None])[:5]
    files, held = list(files or ()), []
    quick = lambda t: _is_quick(t) or bool(re.match(NO_RE, _first_line(t).lower()))
    wait = IMSG_BURST_SEC if is_imessage_chat(chat) else BURST_SEC  # iMessage arrives by polling, so a longer window
    while not quick(text):
        try:
            nxt = gateway.incoming.get(timeout=wait)
        except queue.Empty:
            break
        n_addr, n_chat, n_text, n_files, n_id = (list(nxt) + [(), None])[:5]
        if n_chat != chat or quick(n_text):
            held.append(nxt)
            break
        text = "\n".join(t for t in (text, n_text) if t)
        files += list(n_files or ())
        if n_id:
            if msg_id:
                _live().react(_live().channel_of(chat), msg_id, "👀")
                pending_merge(msg_id, n_id, text)
            msg_id = n_id
    for h in reversed(held):
        _put_front(gateway.incoming, h)  # it was next in line, so it stays next
    return address, chat, text, files, msg_id


def _put_front(q, item):
    with q.mutex:
        q.queue.appendleft(item)
        q.unfinished_tasks += 1
        q.not_empty.notify()


def enqueue(address, chat, text, files=(), msg_id=None):
    """Hand a text to the one loop that handles texts in order (so each sees the jobs
    the one before it started)."""
    gateway.incoming.put((address, chat, text, list(files), msg_id))


def _safe_handle(address, chat, text, files=(), msg_id=None):
    try:
        handle_text(address, chat, text, files, msg_id)
    except Exception:
        traceback.print_exc()
    finally:
        pending_done(msg_id)


# --- the page --------------------------------------------------------------------

def access_key():
    if not KEY_PATH.exists():
        KEY_PATH.parent.mkdir(parents=True, exist_ok=True)
        KEY_PATH.write_text(secrets.token_urlsafe(18), encoding="utf-8")
    return KEY_PATH.read_text(encoding="utf-8").strip()


def page_links():
    key = access_key()
    links = [f"http://localhost:{PORT}/?k={key}"]
    ip = _tailscale_ip()
    if ip:
        links.append(f"http://{ip}:{PORT}/?k={key}")
    return links


def _tailscale_ip():
    import subprocess
    try:
        out = subprocess.run(["tailscale", "ip", "-4"], capture_output=True, text=True, timeout=5,
                             creationflags=0x08000000 if sys.platform == "win32" else 0).stdout.strip()
        return out.splitlines()[0] if out else ""
    except Exception:
        return ""


class Handler(BaseHTTPRequestHandler):
    server_version = "Dots/1"

    def log_message(self, *a):
        pass

    def _authed(self):
        key = access_key()
        q = parse_qs(urlparse(self.path).query)
        if q.get("k", [""])[0] == key:
            return True
        cookie = self.headers.get("Cookie", "")
        return f"dotkey={hashlib.sha256(key.encode()).hexdigest()}" in cookie

    def _send(self, code, body, ctype="application/json", extra=None):
        data = body if isinstance(body, bytes) else (json.dumps(body) if ctype == "application/json" else body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def _body(self):
        n = int(self.headers.get("Content-Length") or 0)
        try:
            return json.loads(self.rfile.read(n) or b"{}")
        except Exception:
            return {}

    def do_GET(self):
        if not self._authed():
            return self._send(403, "Open the link Period shows (python pd_dots.py link).", "text/plain")
        path = urlparse(self.path).path
        if path == "/":
            cookie = f"dotkey={hashlib.sha256(access_key().encode()).hexdigest()}; Path=/; Max-Age=31536000; SameSite=Strict"
            return self._send(200, PAGE_HTML, "text/html; charset=utf-8", {"Set-Cookie": cookie})
        if path == "/chat":  # iMessage-style chat window (phone/chat.html), shown by the Dot Mac app (mac/DotChatApp.swift)
            cookie = f"dotkey={hashlib.sha256(access_key().encode()).hexdigest()}; Path=/; Max-Age=31536000; SameSite=Strict"
            page = (HERE / "phone" / "chat.html").read_bytes()
            return self._send(200, page, "text/html; charset=utf-8", {"Set-Cookie": cookie})
        if path == "/icon.png":
            return self._send(200, (HERE / "phone" / "icon.png").read_bytes(), "image/png")
        if path == "/avatar.jpg":  # the chat's picture of Dot: phone/avatar.jpg if you add one, else the icon
            pic = HERE / "phone" / "avatar.jpg"
            if pic.exists():
                return self._send(200, pic.read_bytes(), "image/jpeg")
            return self._send(200, (HERE / "phone" / "icon.png").read_bytes(), "image/png")
        if path == "/api/dots":
            return self._send(200, {"dots": [d.public() for d in all_dots()], "running": sorted(_procs),
                                    "line": line.connected(), "vm": _vm_ready()})
        m = re.match(r"^/api/dots/([\w-]+)$", path)
        if m:
            d = load_dot(m.group(1))
            if not d:
                return self._send(404, {"error": "no such Dot"})
            return self._send(200, {"dot": d.public(), "log": d.log_tail(30000)})
        if path == "/api/memory":
            return self._send(200, {"text": memory_text()})
        if path == "/api/chat":
            chat = parse_qs(urlparse(self.path).query).get("chat", [""])[0]
            rows = []
            for d in all_dots():
                if d.reply_to == chat:
                    rows += [dict(m, dot=d.id, status=d.status) for m in d.chat()]
            return self._send(200, {"chat": sorted(rows, key=lambda m: m.get("t", 0))})
        if path == "/api/live":
            try:
                import pd_vm
                return self._send(200, {"url": pd_vm.DotPC.live_url(with_password=True)})  # signed-in page on this PC only
            except Exception as e:
                return self._send(500, {"error": str(e)})
        if path == "/api/screen.jpg":
            try:
                from PIL import Image
                import pd_vm
                if not pd_vm.DotPC.running():
                    return self._send(204, b"", "image/jpeg")
                img = Image.open(io.BytesIO(pd_vm.DotPC.screenshot_png())).convert("RGB")
                buf = io.BytesIO()
                img.save(buf, "JPEG", quality=60)
                return self._send(200, buf.getvalue(), "image/jpeg")
            except Exception as e:
                return self._send(500, {"error": str(e)})
        return self._send(404, {"error": "not found"})

    def do_POST(self):
        if not self._authed():
            return self._send(403, {"error": "not allowed"})
        path = urlparse(self.path).path
        body = self._body()
        if path == "/api/dots":
            goal = str(body.get("goal") or "").strip()
            if not goal:
                return self._send(400, {"error": "say what it should do"})
            d = new_dot(goal, computer=str(body.get("computer") or "auto"), schedule=str(body.get("schedule") or ""),
                        kind="job")
            d.add_message("you", goal)
            return self._send(200, {"dot": d.public()})
        m = re.match(r"^/api/dots/([\w-]+)/(answer|say|stop|again|delete)$", path)
        if m:
            d = load_dot(m.group(1))
            if not d:
                return self._send(404, {"error": "no such Dot"})
            act, text = m.group(2), str(body.get("text") or "").strip()
            if d.kind in NEVER_RUN and act in ("answer", "say", "again"):
                if not (text and d.reply_to):
                    return self._send(409, {"error": "that's an old chat log, text Dot instead"})
                enqueue("local", d.reply_to, text)  # routed like a new text
                return self._send(200, {"dot": d.public()})
            if act == "answer" and d.asking == "ok":
                d.add_message("you", text or "no")
                _update(d, answer=text or "no")
            elif act in ("answer", "say"):  # a reply to its question is just the next message
                if d.asking == "ok":
                    return self._send(409, {"error": "answer its yes/no question first"})
                if text:
                    d.add_message("you", text)
                    d.push_followup(text)
                    if d.status != "working":
                        _update(d, force=True, status="queued", question=None, asking="", answer=None,
                                next_run=_now(), runs_this_goal=0)
            elif act == "stop":
                kill_task(d.id)
            elif act == "again":
                _update(d, force=True, status="queued", next_run=_now(), runs_this_goal=0)
            elif act == "delete":
                if d.id in _procs:
                    return self._send(409, {"error": "it's busy right now; stop it first"})
                import shutil
                shutil.rmtree(d.folder, ignore_errors=True)
                return self._send(200, {"ok": True})
            _wake.set()
            return self._send(200, {"dot": d.public()})
        if path == "/api/dm" and self.client_address[0] == "127.0.0.1":
            # Test a conversation exactly like a DM, without messaging anyone:
            # replies are only recorded (see GET /api/chat?chat=local:...).
            chat = "local:" + re.sub(r"[^\w-]", "", str(body.get("chat") or "test"))
            enqueue("local", chat, str(body.get("text") or ""))  # in order, like DMs
            return self._send(200, {"chat": chat})
        if path == "/api/memory":
            MEMORY_PATH.parent.mkdir(parents=True, exist_ok=True)
            MEMORY_PATH.write_text(str(body.get("text") or ""), encoding="utf-8")
            return self._send(200, {"ok": True})
        if path == "/api/vm":
            import pd_vm
            if body.get("action") == "start":
                return self._send(200, {"status": pd_vm.DotPC.start()})
            if body.get("action") == "stop":
                pd_vm.DotPC.stop()
                return self._send(200, {"status": "stopped"})
        return self._send(404, {"error": "not found"})


def _vm_ready():
    try:
        import pd_vm
        return pd_vm.DotPC.available()
    except Exception:
        return False


def _running_daemon():
    """pid of another live Dots daemon, or None (a reused pid doesn't count)."""
    try:
        other = int((DOTS_DIR / "daemon.pid").read_text())
        import psutil
        if other != os.getpid() and psutil.pid_exists(other) \
                and "pd_dots" in " ".join(psutil.Process(other).cmdline()):
            return other
    except Exception:
        pass
    return None


ARCHIVE_AFTER_DAYS = 7


def archive_old_dots(days=ARCHIVE_AFTER_DAYS):
    """Finished jobs (done, stopped, failed) untouched for a week move to
    DOTS_DIR/archive/, so every scan of the folder stays quick. Returns their ids."""
    import shutil
    moved = []
    cutoff = _now() - days * 86400
    archive = DOTS_DIR / "archive"
    for d in all_dots():
        if d.status not in ("done", "stopped", "failed") or (d.updated or d.created) > cutoff:
            continue
        if d.id in _procs:
            continue
        try:
            archive.mkdir(parents=True, exist_ok=True)
            dest = archive / d.id
            if dest.exists():
                dest = archive / f"{d.id}-{int(_now())}"
            shutil.move(str(d.folder), str(dest))
            _dots_cache.pop(d.id, None)
            moved.append(d.id)
        except Exception as e:
            print(f"[archive] {d.id}: {e}", file=sys.stderr)
    return moved


class _StampedLog(io.TextIOBase):
    """A daemon log file where each line starts with the time it was written."""

    def __init__(self, f):
        self.f, self._fresh_line, self._lock = f, True, threading.Lock()

    def write(self, s):
        if not s:
            return 0
        with self._lock:
            out = []
            for piece in s.splitlines(keepends=True):
                if self._fresh_line:
                    out.append(time.strftime("[%m-%d %H:%M:%S] "))
                out.append(piece)
                self._fresh_line = piece.endswith("\n")
            self.f.write("".join(out))
            self.f.flush()
        return len(s)

    def flush(self):
        try:
            self.f.flush()
        except ValueError:  # already closed
            pass


def _daemon_logs():
    """The login task runs the daemon with pythonw, which has no stdout/stderr, so every [watch],
    [codes] and [login renew] line and every traceback went nowhere (daemon.err.txt stopped on
    2026-10-25 7:49 AM while Dot kept running). They go to daemon.out.txt / daemon.err.txt, stamped."""
    for name, fname in (("stdout", "daemon.out.txt"), ("stderr", "daemon.err.txt")):
        if getattr(sys, name) is None:
            path = DOTS_DIR / fname
            _rotate(path)
            setattr(sys, name, _StampedLog(open(path, "a", encoding="utf-8")))


def serve(replace=False):
    DOTS_DIR.mkdir(parents=True, exist_ok=True)
    _daemon_logs()
    other = _running_daemon()
    if other and replace:
        import psutil
        print(f"Closing the old Dot (pid {other})…")
        psutil.Process(other).kill()
        psutil.Process(other).wait(10) if psutil.pid_exists(other) else None
    elif other:
        print(f"Dot is already running in another window (pid {other}). Close it first, or run:\n"
              f"  python \"{HERE / 'pd_dots.py'}\" restart")
        return
    (DOTS_DIR / "daemon.pid").write_text(str(os.getpid()))
    try:
        old = archive_old_dots()
        if old:
            print(f"Archived {len(old)} finished jobs older than {ARCHIVE_AFTER_DAYS} days.")
    except Exception as e:
        print(f"[archive] {e}", file=sys.stderr)
    hosts =["127.0.0.1"] + ([_tailscale_ip()] if _tailscale_ip() else [])
    for host in hosts:
        srv = ThreadingHTTPServer((host, PORT), Handler)
        threading.Thread(target=srv.serve_forever, daemon=True, name=f"dots-http-{host}").start()
    try:
        n = replay_pending()
        if n:
            print(f"Replaying {n} text(s) a restart cut off.")
    except Exception as e:
        print(f"[replay] {e}", file=sys.stderr)
    threading.Thread(target=line_loop, daemon=True, name="dot-line").start()
    threading.Thread(target=imessage_loop, daemon=True, name="dot-imessage").start()
    gateway.start()
    import pd_dotwatch
    threading.Thread(target=pd_dotwatch.watch_loop, daemon=True, name="dot-watch").start()
    threading.Thread(target=_live().warm_up_voice, daemon=True, name="dot-voice").start()
    threading.Thread(target=_inventory_loop, daemon=True, name="dot-inventory").start()
    print("Dot is running. Page:", *page_links(), sep="\n  ")
    worker()


def supervise():
    """Run the daemon and start it again if it ever dies (the login task runs this)."""
    import subprocess
    while True:
        started = _now()
        subprocess.run([sys.executable, str(HERE / "pd_dots.py"), "serve"])
        time.sleep(5 if _now() - started > 60 else 30)  # a crash loop shouldn't spin


LAUNCHD_LABEL = "com.period.dot"


def launchd_plist(keep_awake=False):
    """The Mac's login job: `pd_dots.py supervise` in the background (no window, no Dock icon), with the
    Claude-only backend and a PATH that finds Homebrew, Lima and Claude Code. keep_awake wraps it in
    `caffeinate -i` so the Mac doesn't idle-sleep while Dot runs (closing the lid still sleeps it)."""
    import plistlib
    home = Path.home()
    args = [sys.executable, str(HERE / "pd_dots.py"), "supervise"]
    if keep_awake:
        args = ["/usr/bin/caffeinate", "-i"] + args
    path = ":".join([str(home / ".local" / "bin"), "/opt/homebrew/bin", "/opt/homebrew/sbin", "/usr/local/bin",
                     "/usr/bin", "/bin", "/usr/sbin", "/sbin"])
    env = {"PATH": path, "PERIOD_BACKEND": os.environ.get("PERIOD_BACKEND") or "claude",
           "PYTHONUNBUFFERED": "1", "LANG": "en_US.UTF-8"}
    return plistlib.dumps({
        "Label": LAUNCHD_LABEL, "ProgramArguments": args, "WorkingDirectory": str(HERE),
        "EnvironmentVariables": env, "RunAtLoad": True, "KeepAlive": {"SuccessfulExit": False},
        "ProcessType": "Background", "ThrottleInterval": 30,
        "StandardOutPath": str(DOTS_DIR / "launchd.out.log"), "StandardErrorPath": str(DOTS_DIR / "launchd.err.log"),
    })


def install_launchd(keep_awake=False):
    """Mac: start Dot at login and now. Returns (ok, message)."""
    import subprocess
    agents = Path.home() / "Library" / "LaunchAgents"
    agents.mkdir(parents=True, exist_ok=True)
    DOTS_DIR.mkdir(parents=True, exist_ok=True)
    plist = agents / f"{LAUNCHD_LABEL}.plist"
    plist.write_bytes(launchd_plist(keep_awake=keep_awake))
    domain = f"gui/{os.getuid()}"
    subprocess.run(["launchctl", "bootout", domain, str(plist)], capture_output=True, text=True)  # an old copy
    r = subprocess.run(["launchctl", "bootstrap", domain, str(plist)], capture_output=True, text=True)
    if r.returncode != 0:  # older macOS
        r = subprocess.run(["launchctl", "load", "-w", str(plist)], capture_output=True, text=True)
    return r.returncode == 0, (r.stdout or r.stderr or str(plist)).strip()


def uninstall_launchd():
    import subprocess
    if sys.platform != "darwin":
        return False, "only for a Mac (on Windows, delete the \\Period\\Dots daemon task)"
    plist = Path.home() / "Library" / "LaunchAgents" / f"{LAUNCHD_LABEL}.plist"
    subprocess.run(["launchctl", "bootout", f"gui/{os.getuid()}", str(plist)], capture_output=True, text=True)
    plist.unlink(missing_ok=True)
    return True, ""


def doctor(live=True):
    """Plain-English checks for a new install. live=False skips the one real Claude call."""
    import shutil
    import subprocess
    s = sc()
    ok_all = True

    def line(ok, what, fix=""):
        nonlocal ok_all
        ok_all = ok_all and ok is not False
        mark = {True: "OK  ", False: "FIX ", None: "--  "}[ok]
        print(f"  {mark} {what}" + (f"\n         -> {fix}" if fix and ok is not True else ""))

    print("Checking Dot on this computer:\n")
    only = bool(getattr(s, "claude_only", None) and s.claude_only())
    line(True if only else None, "Thinks with your own Claude plan (Claude-only mode)" if only else
         "Thinks with the server's AI (Claude-only mode is off)",
         "set PERIOD_BACKEND=claude (the Mac installer does this)")
    import pd_claudecall as cc
    exe = cc.cli()[0]
    have = Path(exe).exists()
    line(have, f"Claude Code is installed ({exe})" if have else "Claude Code is installed",
         "install it: curl -fsSL https://claude.ai/install.sh | bash   then run `claude` once to sign in")
    if have and only and live:
        os.environ.setdefault("PERIOD_DOT_CLAUDE_CLI", exe)  # a real call from here, not a test run
        reply, _c, _p = cc.call_only(s, "Reply with exactly: ok", "claude-haiku-5-5")
        good = isinstance(reply, str) and not reply.startswith("[Error") and "ok" in reply.lower()
        line(good, "Claude Code answers (signed in, plan has room)",
             (reply or "")[:200] + "  -> open Terminal, run `claude`, and sign in with your Claude account")
    talk = []
    try:
        if s.discord_connected() and settings().get("discord_dm"):
            talk.append("Discord")
    except Exception:
        pass
    st = settings()
    if st.get("line_mode") == "self" or st.get("line_allowed"):
        talk.append("iMessage")
    line(bool(talk), "You can text Dot: " + (", ".join(talk) if talk else "nothing connected yet"),
         f"run: python3 \"{HERE / 'pd_dots.py'}\" connect-discord")
    try:
        import pd_vm
        vm = pd_vm.DotPC.available()
    except Exception:
        vm = False
    line(True if vm else None, "Dot's own computer (the Dot PC VM) is set up" if vm else
         "No Dot PC VM (Dot works on this computer only; it asks before anything risky)",
         "optional: bash mac/setup-dotpc.sh" if sys.platform == "darwin" else "see docs/DOTS.md")
    if sys.platform == "darwin":
        plist = Path.home() / "Library" / "LaunchAgents" / f"{LAUNCHD_LABEL}.plist"
        r = subprocess.run(["launchctl", "list", LAUNCHD_LABEL], capture_output=True, text=True)
        line(plist.exists() and r.returncode == 0, "Dot starts by itself when you log in",
             f"run: python3 \"{HERE / 'pd_dots.py'}\" install")
        line(True if shutil.which("tailscale") or Path("/Applications/Tailscale.app").exists() else None,
             "Tailscale (opens the Dots page from your phone)", "optional: install Tailscale from the App Store")
    print("\nAll set." if ok_all else "\nFix the FIX lines above, then run this again.")
    return ok_all


def _ask_yes(question, default=False):
    try:
        got = input(f"{question} [{'Y/n' if default else 'y/N'}] ").strip().lower()
    except EOFError:
        return default
    return default if not got else got.startswith("y")


def setup_mac():
    """The Mac installer's second half (mac/install-dot.sh runs it): Claude-only, owner add-ons off,
    chat connected, start at login, then the doctor. Safe to run again."""
    if sys.platform != "darwin":
        print("This is the Mac setup. On Windows use: python pd_dots.py install")
        return False
    s = sc()
    os.environ["PERIOD_BACKEND"] = "claude"
    ui = s._ui_settings()
    ui["backend"] = "claude"
    s.UI_PATH.parent.mkdir(parents=True, exist_ok=True)
    s.UI_PATH.write_text(json.dumps(ui, indent=2), encoding="utf-8")
    print("Dot will think with your own Claude plan (Claude Code), never anyone else's.\n")
    try:
        connected = s.discord_connected() and settings().get("discord_dm")
    except Exception:
        connected = False
    if not connected:
        print("Next: connect Discord so you can text Dot from your phone.")
        if _ask_yes("Set up Discord now?", default=True):
            connect_discord()
    st = settings()
    st["keep_awake"] = _ask_yes("Keep this Mac awake while Dot runs? (uses more battery; closing the lid "
                                "still puts it to sleep)", default=bool(st.get("keep_awake")))
    save_settings(st)
    ok, msg = install_launchd(keep_awake=st["keep_awake"])
    print("Dot now starts by itself when you log in, and it's running now." if ok else
          f"Couldn't set Dot to start at login: {msg}")
    print()
    return doctor(live=True)


def install_login_task():
    """Start the daemon hidden at login (Task Scheduler, no window; launchd on a Mac)."""
    import subprocess
    if sys.platform == "darwin":
        return install_launchd(keep_awake=bool(settings().get("keep_awake")))
    pyw = Path(sys.executable).with_name("pythonw.exe")
    cmd = f'"{pyw if pyw.exists() else sys.executable}" "{HERE / "pd_dots.py"}" supervise'
    r = subprocess.run(["schtasks", "/Create", "/F", "/SC", "ONLOGON", "/RL", "LIMITED",
                        "/TN", r"\Period\Dots daemon", "/TR", cmd],
                       capture_output=True, text=True, creationflags=0x08000000)
    return r.returncode == 0, (r.stdout or r.stderr).strip()


def connect_line():
    s = sc()
    print("Dot's own iMessage line: a second BlueBubbles server on your Mac, signed into an\n"
          "Apple ID made just for Dot (see docs/DOTS.md). Leave blank to keep what's saved.")
    url = input("Its address (e.g. http://your-mac:1235): ").strip()
    if url:
        s._secret_set(_LINE_URL, url)
    import getpass
    pw = getpass.getpass("Its BlueBubbles password: ").strip()
    if pw:
        s._secret_set(_LINE_PW, pw)
    st = settings()
    who = input("Your phone number or Apple ID email, to let Dot answer only you "
                f"[{', '.join(st.get('line_allowed', []))}]: ").strip()
    if who:
        st["line_allowed"] = [w.strip() for w in who.split(",") if w.strip()]
        st["line_notify"] = st["line_allowed"][0]
    save_settings(st)
    try:
        line._call("GET", "/server/info")
        print("Connected. Text Dot from your phone to give it a job.")
    except Exception as e:
        print(f"Saved, but couldn't reach it yet: {e}")


def connect_discord():
    """Talk to Dot in Discord DMs: connect the bot, then find the user once."""
    s = sc()
    if not s.discord_connected() and not s.connect_discord_wizard():
        return
    print("\nNow, in any channel of your server that the bot can see, send this message:  hi dot")
    print("Waiting up to 3 minutes…")
    channels = []
    for g in s._discord("GET", "/users/@me/guilds"):
        channels += [c["id"] for c in s._discord("GET", f"/guilds/{g['id']}/channels") if c.get("type") == 0]
    if not channels:
        print("The bot isn't in a server yet. Do step 3 of the setup (the OAuth2 link), then run this again.")
        return
    started = datetime.datetime.now(datetime.timezone.utc)
    user = None
    deadline = _now() + 180
    while _now() < deadline and not user:
        for cid in channels:
            try:
                for m in s._discord("GET", f"/channels/{cid}/messages", params={"limit": 5}) or []:
                    when = datetime.datetime.fromisoformat(m["timestamp"].replace("Z", "+00:00"))
                    if (m.get("content") or "").strip().lower() == "hi dot" and when >= started \
                            and not m["author"].get("bot"):
                        user = m["author"]
                        break
            except Exception:
                continue  # a channel the bot can't read
            if user:
                break
        time.sleep(3)
    if not user:
        print("Didn't see it. Check the bot has Message Content Intent turned on and can see that channel.")
        return
    dm = s._discord("POST", "/users/@me/channels", json={"recipient_id": user["id"]})["id"]
    st = settings()
    st.update(discord_user=user["id"], discord_dm=dm)
    save_settings(st)
    discord.send(dm, f"Hi {user.get('global_name') or user['username']}, I'm Dot. DM me a job, like "
                     "\"find cheap flights to Chicago for Thanksgiving\", and I'll get on it. "
                     "Say \"status\" to see what I'm doing, or \"stop\".")
    print(f"Done. Dot just DM'd you on Discord ({user['username']}). Only you can give it jobs.")


def connect_self():
    """Use the user's own iCloud: they text themselves, Dot answers in that chat."""
    s = sc()
    if not s.imessage_connected():
        print("First connect iMessage in Period (say \"connect imessage\"), then run this again.")
        return
    who = input("Your own phone number or Apple ID email (the one you'll text yourself at): ").strip()
    if not who:
        return
    handle = re.sub(r"[^\d+]", "", who) if re.search(r"\d{7,}", who) else who.lower()
    if handle and handle[0] != "+" and re.fullmatch(r"\d{10}", handle):
        handle = "+1" + handle
    st = settings()
    st.update(line_mode="self", self_chat=f"iMessage;-;{handle}", line_notify="self")
    save_settings(st)
    try:
        line.send("self", "I'm set up. Text this chat to give me a job.")
        print("Done. Check your note-to-self chat in Messages: Dot just said hi there.")
    except Exception as e:
        print(f"Saved, but couldn't send the hello text yet: {e}")


PAGE_HTML = (HERE / "phone" / "dots.html").read_text(encoding="utf-8") if (HERE / "phone" / "dots.html").exists() else "<p>phone/dots.html is missing</p>"


def _hide_child_windows():
    """pythonw has no console, so every command-line program Dot or a job starts (shell commands, wsl, git,
    tailscale...) would pop a black window over whatever the owner is doing, games included. Default every
    child to no window; a caller that asks for its own console or a detached process keeps that."""
    import subprocess
    if sys.platform != "win32" or getattr(subprocess.Popen.__init__, "_dot_no_window", False):
        return
    orig = subprocess.Popen.__init__

    def no_window(self, *a, **kw):
        flags = kw.get("creationflags", 0) or 0
        if not flags & (0x00000010 | 0x00000008):  # CREATE_NEW_CONSOLE, DETACHED_PROCESS
            kw["creationflags"] = flags | 0x08000000  # CREATE_NO_WINDOW
        return orig(self, *a, **kw)
    no_window._dot_no_window = True
    subprocess.Popen.__init__ = no_window


def main(argv):
    _hide_child_windows()
    cmd = argv[1] if len(argv) > 1 else "serve"
    if cmd == "serve":
        serve()
    elif cmd == "restart":
        serve(replace=True)
    elif cmd == "supervise":
        supervise()
    elif cmd == "run" and len(argv) > 2:
        run_task_process(argv[2])
    elif cmd == "new":
        d = new_dot(" ".join(argv[2:]))
        print(f"Added {d.id}: {d.goal}")
    elif cmd == "list":
        for d in all_dots():
            print(f"{d.id}  {d.status:9} {d.name}")
    elif cmd == "link":
        print(*page_links(), sep="\n")
    elif cmd == "install":
        ok, msg = install_login_task()
        print("Installed: the Dots daemon starts when you log in." if ok else f"Couldn't install: {msg}")
    elif cmd == "connect-line":
        connect_line()
    elif cmd == "connect-discord":
        connect_discord()
    elif cmd == "connect-self":
        connect_self()
    elif cmd == "setup-mac":
        sys.exit(0 if setup_mac() else 1)
    elif cmd == "doctor":
        sys.exit(0 if doctor(live="--no-call" not in argv) else 1)
    elif cmd == "uninstall":
        ok, msg = uninstall_launchd()
        print("Removed: Dot no longer starts at login." if ok else f"Couldn't remove: {msg}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
