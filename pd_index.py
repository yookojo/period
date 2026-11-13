"""Dot's local mail, deadline and calendar index.

Why: "when are my interviews due?" is the owner's most common slow ask (median
269 s from text to answer, 9.5 min on 2026-11-05). The job's first look-ups
searched Gmail and Outlook live (26 s on average, up to 58 s, and "Found 0" when
they timed out), got back only subject lines, then opened mail one email per
step. With this index the prefetch reads SQLite in ~50 ms and carries the
deadline sentences, so the job's first reply can answer.

A hidden process (`pythonw pd_index.py loop`, one at a time, started on demand
by `ensure_running()`) keeps ~/.period_dots/index.db up to date:
- Gmail (each connected account, one read-only IMAP session on All Mail):
  60-day header backfill, new mail every 60 s, flags every cycle for 3 days and
  a full 60-day reconcile (flags, deletes) every 15 min.
- Outlook (reached the same way the live mail tools reach it: s._outlook joins
  the running Outlook or starts it with no window): mail folders every 2 min
  through Folder.GetTable, a full reconcile every 15 min, the calendar every
  5 min. Each pass runs on one COM thread under a 90 s watchdog.
- Canvas due dates (and Google Calendar when connected) every 10 min.

Privacy (the PC has a known infostealer, so keep little on disk):
- 60 days only; older rows are deleted, the file is vacuumed weekly.
- Full text (8,000 chars at most) only for recruiting / assessment / interview /
  offer / course mail. Everything else is a header row (Outlook also keeps its
  own ~250-char preview).
- Codes, one-time passwords, verification, password-reset and sign-in mail keep
  no text at all, and digits in their subject are masked.
- Readers drop Gmail rows in remote-only mode. `index_off` in DOTS_DIR turns
  the whole thing off (the loop exits, readers return None).

Readers never raise and return None to mean "use the live tool"; pd_fast falls
back to today's live look-ups whenever the index is stale, missing, can't
translate the query, or finds nothing. Nothing here sends, buys or deletes mail:
IMAP is opened read-only and Outlook is only read.
"""
import datetime
import email as email_lib
import email.utils
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import threading
import time
from pathlib import Path

KEEP_DAYS = 60
BODY_MAX = 8000
BODY_FETCH = 300000            # bytes of each candidate message fetched (no attachment downloads)
GMAIL_EVERY = 60
OUTLOOK_EVERY = 120
RECONCILE_EVERY = 15 * 60
CAL_EVERY = 5 * 60
CANVAS_EVERY = 10 * 60
SPAWN_EVERY = 10 * 60          # ensure_running tries at most this often
PASS_TIMEOUT = 90              # an Outlook pass that takes longer is marked stale
MAIL_MAX_AGE = 5 * 60          # older than this and search() says "use live"
CAL_MAX_AGE = 15 * 60
CANVAS_MAX_AGE = 25 * 60
VACUUM_EVERY = 7 * 86400
CANDIDATE_KINDS = ("recruiting", "assessment", "interview", "offer", "course", "deadline")
CREATE_NO_WINDOW, DETACHED_PROCESS, CREATE_NEW_PROCESS_GROUP = 0x08000000, 0x00000008, 0x00000200

S = None                        # tests put a fake period here
_ALLOW_SPAWN_IN_TESTS = False   # ensure_running never starts a real process under pytest unless a test says so


def _s(s=None):
    global S
    if s is not None:
        return s
    if S is None:
        import period
        S = period
    return S


def dots_dir():
    return Path(os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))


def db_path():
    return dots_dir() / "index.db"


def is_off():
    return ((dots_dir() / "index_off").exists()
            or os.environ.get("PERIOD_DOT_INDEX", "").lower() in ("off", "0", "no"))


def _log(msg):
    try:
        path = dots_dir() / "index.log"
        if path.exists() and path.stat().st_size > 2_000_000:
            path.replace(path.with_suffix(".log.1"))
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%m-%d %H:%M:%S')} {msg}\n")
    except Exception:
        pass


# --- storage -------------------------------------------------------------------

SCHEMA = """
CREATE TABLE IF NOT EXISTS msgs(
  rid INTEGER PRIMARY KEY, account TEXT NOT NULL, id TEXT NOT NULL, entry_id TEXT, msgid_hdr TEXT,
  folder TEXT, date_ts REAL, date_str TEXT, from_txt TEXT, to_txt TEXT, subject TEXT, unread INTEGER,
  snippet TEXT, body TEXT, kind TEXT, synced_ts REAL, uid INTEGER, inbox INTEGER DEFAULT 0,
  sent INTEGER DEFAULT 0, in_default INTEGER DEFAULT 1, meeting INTEGER DEFAULT 0, body_state INTEGER DEFAULT 0,
  UNIQUE(account, id));
CREATE INDEX IF NOT EXISTS msgs_date ON msgs(account, date_ts);
CREATE INDEX IF NOT EXISTS msgs_uid ON msgs(account, uid);
CREATE VIRTUAL TABLE IF NOT EXISTS msgs_fts USING fts5(subject, from_txt, snippet, body,
  content='msgs', content_rowid='rid', tokenize='unicode61 remove_diacritics 2');
CREATE TRIGGER IF NOT EXISTS msgs_ai AFTER INSERT ON msgs BEGIN
  INSERT INTO msgs_fts(rowid, subject, from_txt, snippet, body)
  VALUES (new.rid, new.subject, new.from_txt, new.snippet, new.body); END;
CREATE TRIGGER IF NOT EXISTS msgs_ad AFTER DELETE ON msgs BEGIN
  INSERT INTO msgs_fts(msgs_fts, rowid, subject, from_txt, snippet, body)
  VALUES ('delete', old.rid, old.subject, old.from_txt, old.snippet, old.body); END;
CREATE TRIGGER IF NOT EXISTS msgs_au AFTER UPDATE OF subject, from_txt, snippet, body ON msgs BEGIN
  INSERT INTO msgs_fts(msgs_fts, rowid, subject, from_txt, snippet, body)
  VALUES ('delete', old.rid, old.subject, old.from_txt, old.snippet, old.body);
  INSERT INTO msgs_fts(rowid, subject, from_txt, snippet, body)
  VALUES (new.rid, new.subject, new.from_txt, new.snippet, new.body); END;
CREATE TABLE IF NOT EXISTS events(source TEXT, id TEXT, start_ts REAL, end_ts REAL, title TEXT,
  location TEXT, data TEXT, PRIMARY KEY(source, id));
CREATE TABLE IF NOT EXISTS sync_state(source TEXT PRIMARY KEY, last_ok_ts REAL, last_err TEXT, cursor TEXT);
CREATE TABLE IF NOT EXISTS deadlines(account TEXT, id TEXT, company TEXT, what TEXT, due_ts REAL,
  approx INTEGER, evidence TEXT, status TEXT, msg_ts REAL, kind TEXT, PRIMARY KEY(account, id));
"""


def connect():
    """A writer connection (one per thread)."""
    path = db_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(str(path), timeout=30)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.executescript(SCHEMA)
    return conn


def _reader():
    path = db_path()
    if not path.exists():
        return None
    conn = sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True, timeout=2)
    conn.row_factory = sqlite3.Row
    return conn


def _state(conn, source):
    row = conn.execute("SELECT last_ok_ts, last_err, cursor FROM sync_state WHERE source=?", (source,)).fetchone()
    if not row:
        return None, None, {}
    try:
        cur = json.loads(row[2]) if row[2] else {}
    except ValueError:
        cur = {"raw": row[2]}
    return row[0], row[1], cur if isinstance(cur, dict) else {"raw": cur}


def _set_state(conn, source, ok=None, err=None, cursor=None):
    last_ok, last_err, cur = _state(conn, source)
    if cursor is not None:
        cur = cursor
    conn.execute("INSERT INTO sync_state(source, last_ok_ts, last_err, cursor) VALUES(?,?,?,?) "
                 "ON CONFLICT(source) DO UPDATE SET last_ok_ts=excluded.last_ok_ts, last_err=excluded.last_err, "
                 "cursor=excluded.cursor",
                 (source, time.time() if ok else last_ok, None if ok else (str(err)[:300] if err else last_err),
                  json.dumps(cur)))
    conn.commit()


def _record_err(source, err):
    try:
        conn = connect()
        _set_state(conn, source, ok=False, err=err)
        conn.close()
    except Exception:
        pass
    _log(f"{source}: {str(err)[:300]}")


def prune(conn, now=None):
    now = time.time() if now is None else now
    cut = now - KEEP_DAYS * 86400
    conn.execute("DELETE FROM msgs WHERE date_ts < ?", (cut,))
    conn.execute("DELETE FROM deadlines WHERE msg_ts < ?", (cut,))
    conn.commit()


def maybe_vacuum(conn, now=None):
    now = time.time() if now is None else now
    last, _err, _cur = _state(conn, "vacuum")
    if last and now - last < VACUUM_EVERY:
        return False
    prune(conn, now)
    conn.execute("VACUUM")
    _set_state(conn, "vacuum", ok=True)
    return True


# --- what kind of mail it is (decides what is kept) ------------------------------

try:  # the inbox watcher's patterns (plain regexes; importing it starts nothing)
    from pd_dotwatch import _ALWAYS_LOOK as _WATCH_LOOK, _NOISE_SUBJECT as _WATCH_NOISE
except Exception:  # pragma: no cover
    _WATCH_LOOK = re.compile(r"interview|offer|assessment|coding (challenge|test)|hirevue|codesignal|"
                             r"hackerrank|schedule|next round|final round", re.I)
    _WATCH_NOISE = re.compile(r"newsletter|digest|webinar|receipt|unsubscribe|% off|sale\b", re.I)

SECRET_RE = re.compile(
    r"verification|verify|security code|one[- ]?time|\bOTP\b|pass ?code|password|sign[- ]?in\b|sign[- ]?on\b|"
    r"log[- ]?in\b|login|confirm your (e-?mail|account|identity|sign)|two[- ]factor|\b2fa\b|2-step|magic link|"
    r"access code|authenticat|security alert|\bcodes?\b|\bPIN\b|reset", re.I)
SECRET_SENDER_RE = re.compile(r"accounts\.google|account-?security|security@|verify@|verification@|otp\.|"
                              r"(no-?reply|mail)@.*(auth|login|verify|secure)\.", re.I)
PROMO_RE = re.compile(r"% off|\bsale\b|\bdeals?\b|save \$|\bcoupon|free shipping|black friday|cyber monday|"
                      r"newsletter|digest|webinar|job alert|jobs? (for you|you may|recommended)|is hiring|"
                      r"new jobs|recommended jobs|your (next )?order|has shipped|out for delivery|receipt", re.I)
ATS_SENDER_RE = re.compile(
    r"greenhouse|lever\.co|hire\.lever|myworkday|workday|smartrecruiters|ashbyhq|icims|jobvite|taleo|"
    r"successfactors|eightfold|avature|phenom|hackerrank|codesignal|hirevue|hireflix|codility|coderpad|karat|"
    r"testgorilla|pymetrics|harver|modernhire|sparkhire|paradox\.ai|goodtime|careers?@|recruit|talent|"
    r"university ?relations|campus", re.I)
OFFER_RE = re.compile(r"offer (letter|of employment|details|package)|job offer|your offer|extend(ing)? (you )?an offer",
                      re.I)
ASSESS_RE = re.compile(r"assessment|hackerrank|codesignal|codility|coderpad|karat|testgorilla|pymetrics|harver|"
                       r"\bOA\b|online test|coding (challenge|test|exercise|assignment)|take[- ]home|aptitude|"
                       r"cognitive|game[- ]based|technical (test|challenge|exercise)", re.I)
INTERVIEW_RE = re.compile(r"interview|hirevue|hireflix|spark ?hire|modern ?hire|superday|final round|next round|"
                          r"onsite|on-site|phone screen|recruiter (call|chat)|schedul|availability", re.I)
COURSE_RE = re.compile(
    r"\b(CS|MATH|CHEM|PHYSICS|PHYS|ECON|STATS?|EE|ME|ENGR|PSYCH|BIO|CME|HUMBIO|PWR|THINK|COLLEGE|SOC|"
    r"POLISCI|ARTHIST|HISTORY|PHIL|LINGUIST|DATASCI|SYMSYS)\s?\d{1,3}[A-Z]?\b|problem set|\bpset\b|homework|"
    r"midterm|final exam|\bquiz\b|gradescope|canvas|ed discussion|piazza", re.I)
COURSE_SENDER_RE = re.compile(r"instructure|canvas|gradescope|edstem|piazza|remote\.edu", re.I)
RECRUIT_SUBJECT_RE = re.compile(r"next steps|application|applied|candidate|recruit|position|internship|new grad|"
                                r"\brole\b|opportunit|hiring", re.I)
LIST_SENDER_RE = re.compile(r"@lists\.|-bounces@|mailman|listserv", re.I)
DEADLINE_SUBJECT_RE = re.compile(r"deadline|\bdue\b(?!\s+to)|expir|last day|final reminder|action required", re.I)


def classify(subject, sender):
    """Header-only decision: 'secret' (keep no text), a candidate kind (keep the text), or None."""
    subject, sender = subject or "", sender or ""
    if SECRET_RE.search(subject) or SECRET_SENDER_RE.search(sender):
        return "secret"
    if LIST_SENDER_RE.search(sender):  # mailing lists (career-event lists included): school mail or a dated ask
        if COURSE_RE.search(subject):
            return "course"
        if DEADLINE_SUBJECT_RE.search(subject) and not PROMO_RE.search(subject):
            return "deadline"
        return None
    ats = bool(ATS_SENDER_RE.search(sender))
    if PROMO_RE.search(subject) and not ats:
        return None
    if OFFER_RE.search(subject):
        return "offer"
    if ASSESS_RE.search(subject) or re.search(r"hackerrank|codesignal|codility|coderpad|karat|testgorilla|"
                                              r"pymetrics|harver", sender, re.I):
        return "assessment"
    if INTERVIEW_RE.search(subject) or re.search(r"hirevue|hireflix|sparkhire|modernhire|goodtime|paradox",
                                                 sender, re.I):
        if not (COURSE_RE.search(subject) and not ats):
            return "interview"
    if COURSE_RE.search(subject) or (COURSE_SENDER_RE.search(sender) and DEADLINE_SUBJECT_RE.search(subject)) \
            or re.search(r"instructure|gradescope|edstem|piazza", sender, re.I):
        return "course"
    if ats or (RECRUIT_SUBJECT_RE.search(subject) and _WATCH_LOOK.search(subject)):
        return "recruiting"
    if ats is False and RECRUIT_SUBJECT_RE.search(subject) and re.search(r"next steps|your application|candidate",
                                                                         subject, re.I):
        return "recruiting"
    if DEADLINE_SUBJECT_RE.search(subject) and not _WATCH_NOISE.search(subject):
        return "deadline"
    return None


def _mask_digits(text):
    return re.sub(r"\b[A-Z]{0,3}-?\d{4,8}\b", "••••", text or "")


def _clean_text(text):
    text = (text or "").replace("\r\n", "\n").replace("\r", "\n").replace("‌", "").replace("\xa0", " ")
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n\s*\n+", "\n\n", text)
    return text.strip()


def _snippet(text, n=240):
    return re.sub(r"\s+", " ", text or "").strip()[:n]


# --- deadlines -----------------------------------------------------------------------

_MONTHS = (r"(?:jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|june?|july?|aug(?:ust)?|"
           r"sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)")
_TZS = {"pt": "America/Los_Angeles", "pst": "America/Los_Angeles", "pdt": "America/Los_Angeles",
        "pacific": "America/Los_Angeles", "et": "America/New_York", "est": "America/New_York",
        "edt": "America/New_York", "eastern": "America/New_York", "ct": "America/Chicago",
        "cst": "America/Chicago", "cdt": "America/Chicago", "central": "America/Chicago",
        "mt": "America/Denver", "mst": "America/Denver", "mdt": "America/Denver", "mountain": "America/Denver",
        "utc": "UTC", "gmt": "UTC"}
_TZ_PAT = r"(?:PT|PST|PDT|ET|EST|EDT|CT|CST|CDT|MT|MST|MDT|UTC|GMT|Pacific|Eastern|Central|Mountain)"
DATE_RES = [
    re.compile(rf"\b(?:(?:mon|tues?|wed(?:nes)?|thu(?:rs)?|fri|sat(?:ur)?|sun)(?:day)?\.?,?\s+)?{_MONTHS}\.?\s+"
               r"\d{1,2}(?:st|nd|rd|th)?\b(?:,?\s+(\d{4})\b)?", re.I),
    re.compile(rf"\b\d{{1,2}}(?:st|nd|rd|th)?\s+(?:of\s+)?{_MONTHS}\b(?:,?\s+(\d{{4}})\b)?", re.I),
    re.compile(r"\b(\d{4})-\d{2}-\d{2}\b"),
    re.compile(r"\b\d{1,2}/\d{1,2}(?:/(\d{2,4}))?\b(?!\s*(?:hours|days|pm|am))"),
]
TIME_RE = re.compile(rf"\b(\d{{1,2}})(?::(\d{{2}}))?\s*([ap])\.?m\b\.?(?:\s*\(?({_TZ_PAT})\b\)?)?|"
                     rf"\b(\d{{1,2}}):(\d{{2}})\b(?:\s*\(?({_TZ_PAT})\b\)?)?|\b(noon|midnight)\b(?:\s*\(?({_TZ_PAT})\b\)?)?",
                     re.I)
_NUMW = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9,
         "ten": 10, "fourteen": 14, "twenty-four": 24, "forty-eight": 48, "seventy-two": 72, "a": 1}
_N = r"(\d{1,3}|one|two|three|four|five|six|seven|eight|nine|ten|fourteen|twenty-four|forty-eight|seventy-two)"
REL_RE = re.compile(rf"\b(?:within|in the next|next|in)\s+{_N}\s*(?:\(\d+\)\s*)?(business|calendar|working)?\s*"
                    r"(hours?|hrs?|days?|weeks?)\b|"
                    rf"\b{_N}\s*(?:\(\d+\)\s*)?(business|calendar|working)?\s*(hours?|hrs?|days?|weeks?)\s+"
                    r"(?:from|after|of)\s+(?:the\s+(?:date|time)\s+of\s+)?(?:this|receiv|receipt|today)", re.I)
WEEKDAY_RE = re.compile(r"\bby\s+(?:this\s+|next\s+)?(monday|tuesday|wednesday|thursday|friday|saturday|sunday)\b", re.I)
CUE_RE = re.compile(
    r"\bdue\b(?!\s+to\b)|\bdeadline|\bexpir(?:e|es|ed|ation|y)\b|\bcomplete[ds]?\b[^.\n]{0,60}?\b(?:by|before|within)\b|"
    r"no later than|\bwithin\s+\S+\s+(?:\(\d+\)\s*)?(?:business |calendar |working )?(?:days?|hours?|hrs?|weeks?)\b|"
    r"\bschedul|\bavailability\b|interviews?\s+(?:is\s+|will be\s+|has been\s+)?(?:on|at|scheduled|confirmed)\b|"
    r"\bsubmit\b[^.\n]{0,40}\bby\b|\bby\s+(?:11:59|midnight|end of (?:the )?day|eod)\b", re.I)
NOT_OWNER_RE = re.compile(r"get back to you|be in touch|hear (?:back )?from us|you(?:'ll| will) hear|"
                          r"review (?:your|all|every) application|reach out to you|unsubscribe|privacy (?:policy|notice)|"
                          r"terms of (?:use|service)|\bdue to\b|cookie", re.I)
ACTION_RE = re.compile(r"\b(complete|submit|respond|reply|confirm|sign|schedule|select|choose|book|accept|upload|"
                       r"take|finish|record|start|access|pick|register|rsvp|turn in)\b", re.I)
DONE_RES = [re.compile(r"thank(?:s| you) for completing", re.I),
            re.compile(r"assessment (?:has been |was )?(?:successfully )?(?:completed|submitted|received)", re.I),
            re.compile(r"(?:we(?:'ve| have)|has been) received your (?:completed )?(?:assessment|submission|"
                       r"responses|video interview|test)", re.I),
            re.compile(r"you(?:'ve| have) (?:successfully )?(?:completed|submitted) (?:your|the)", re.I)]
REJECT_RE = re.compile(r"not (?:be )?moving forward|move forward with other|other candidates|regret to inform|"
                       r"decided not to (?:proceed|move)|will not be (?:moving|proceeding)|position has been filled|"
                       r"no longer (?:under consideration|being considered)", re.I)
_GENERIC_NAME = re.compile(r"\b(university |campus |global |early |emerging )?(recruiting|recruitment|recruiter|careers?|"
                           r"talent( acquisition)?|hiring( team)?|team|no[- ]?reply|notifications?|via \w+|"
                           r"relations|jobs|people|hr|staffing|programs?)\b", re.I)
_PLATFORM = re.compile(r"hackerrank|codesignal|hirevue|hireflix|greenhouse|lever|workday|smartrecruiters|ashby|"
                       r"icims|jobvite|taleo|successfactors|codility|coderpad|karat|testgorilla|pymetrics|harver|"
                       r"modern ?hire|spark ?hire|eightfold|avature|phenom|paradox|goodtime|calendly|gmail|outlook|"
                       r"yahoo|hotmail|icloud|remote|linkedin|handshake|joinhandshake|indeed|google calendar", re.I)
_SUBJ_STOP = re.compile(r"\b(online|assessment|interview|invitation|invite|software|engineer(ing)?|intern(ship)?|"
                        r"summer|fall|spring|winter|new|grad(uate)?|analyst|program|position|role|application|"
                        r"next|steps|your|the|coding|challenge|test|video|technical|update|\d{4})\b.*$", re.I)


def _company(from_txt, subject, body=""):
    """Best guess at which company a recruiting mail is about (used to close items and in the digest)."""
    name, addr = email.utils.parseaddr(from_txt or "")
    subject = subject or ""
    pats = [r"([A-Z][\w&.'\-]*(?:\s+[A-Z][\w&.'\-]*){0,3})['’]s\b",
            r"\b(?:with|at|from|for|to join|join|to)\s+([A-Z][\w&.'\-]*(?:\s+(?:[A-Z][\w&.'\-]*|&)){0,3})",
            r"^\s*(?:re:|fwd?:)?\s*([A-Z][\w&.'\-]*(?:\s+[A-Z][\w&.'\-]*){0,3})\s*[-|:–—]"]
    for p in pats:
        for m in re.finditer(p, subject):
            cand = _SUBJ_STOP.sub("", m.group(1)).strip(" -|:&'.")
            if re.fullmatch(r"(?:(?:action|required|reminder|important|urgent|final|new|thank|thanks|you|your|"
                            r"invitation|invite|update|hello|hi|dear|re|fwd?|please|complete|congratulations)\s*)+",
                            cand, re.I):
                continue
            if len(cand) >= 2 and not _PLATFORM.search(cand) and cand.lower() not in (
                    "you", "your", "our", "us", "we", "action", "reminder", "important", "thank", "thanks",
                    "congratulations", "hi", "hello", "re", "fwd", "update", "invitation", "the", "a", "an"):
                return cand
    domain = (addr.split("@")[-1] if "@" in addr else "").lower()
    parts = [p for p in domain.split(".") if p and p not in ("com", "org", "net", "io", "co", "us", "edu", "ai",
                                                             "mail", "email", "e", "em", "info", "careers", "jobs",
                                                             "recruiting", "talent", "hr", "notifications", "us")]
    sld = parts[-1] if parts else ""
    clean = _GENERIC_NAME.sub("", name or "").strip(" -|:,.")
    if clean and not _PLATFORM.search(clean) and not re.fullmatch(r"[A-Z][a-z]+ [A-Z][a-z]+", clean):
        return clean
    if sld and not _PLATFORM.search(sld):
        return sld.capitalize()
    if clean and not _PLATFORM.search(clean):
        return clean
    # Sent through a hiring platform under its own name: the company is usually named in the first lines.
    m = re.search(r"\b(?:interest in|position at|role at|careers? at|team at|joining|applying to|application to|"
                  r"application with|on behalf of)\s+([A-Z][\w&.'\-]*(?:\s+(?:[A-Z][\w&.'\-]*|&)){0,3})",
                  (body or "")[:1500])
    if m:
        cand = _SUBJ_STOP.sub("", m.group(1)).strip(" -|:&'.")
        if len(cand) >= 2 and not _PLATFORM.search(cand):
            return cand
    return "?"


def _course(subject, from_txt):
    """Which class a course email is about: its code, or the course name Canvas / Gradescope put after ':'."""
    m = re.search(r"\b(CS|MATH|CHEM|PHYSICS|PHYS|ECON|STATS?|EE|ME|ENGR|PSYCH|BIO|CME|HUMBIO|PWR|THINK|"
                  r"COLLEGE|SOC|POLISCI|DATASCI|SYMSYS)\s?\d{1,3}[A-Z]?\b", subject or "")
    if m:
        return m.group(0)
    if re.search(r"instructure|gradescope|canvas", from_txt or "", re.I) and ":" in (subject or ""):
        tail = subject.rsplit(":", 1)[1].strip()
        if tail:
            return re.split(r",", tail)[0][:40]
    m = re.match(r"\s*\[([^\]]+)\]", subject or "")
    if m:
        return m.group(1)[:30]
    name = email.utils.parseaddr(from_txt or "")[0]
    return (name or "school")[:40]


def _norm_company(c):
    c = re.sub(r"[^a-z0-9]", "", (c or "").lower())
    return re.sub(r"(inc|llc|corp|corporation|group|company|co|bank|financial|technologies|tech|labs?)$", "", c) or c


def _same_company(a, b):
    a, b = _norm_company(a), _norm_company(b)
    if not a or not b or a == "?" or b == "?":
        return False
    return a == b or (min(len(a), len(b)) >= 4 and (a.startswith(b) or b.startswith(a)))


def sentences(text):
    text = _clean_text(text)
    out = []
    for chunk in re.split(r"\n+", text):
        for sent in re.split(r"(?<=[.!?])\s+(?=[A-Z0-9\"(])", chunk):
            sent = sent.strip(" -•*>\t")
            if len(sent) >= 12:
                out.append(sent[:300])
    return out


def evidence_sentences(text, limit=3):
    seen, out = set(), []
    for sent in sentences(text):
        if CUE_RE.search(sent) and not NOT_OWNER_RE.search(sent):
            key = sent.lower()
            if key not in seen:
                seen.add(key)
                out.append(sent)
                if len(out) >= limit:
                    break
    return out


def _local_ts(dt):
    return dt.timestamp() if dt.tzinfo else time.mktime(dt.timetuple())


def _find_time(sent, after=0):
    best = None
    for m in TIME_RE.finditer(sent):
        if m.group(1):
            h, mi, ap, tz = int(m.group(1)), int(m.group(2) or 0), m.group(3).lower(), m.group(4)
            if h > 12:
                continue
            h = (h % 12) + (12 if ap == "p" else 0)
        elif m.group(5):
            h, mi, tz = int(m.group(5)), int(m.group(6)), m.group(7)
            if h > 23 or mi > 59:
                continue
        else:
            h, mi, tz = (12, 0) if m.group(8).lower() == "noon" else (23, 59), m.group(9)
        cand = (h, mi, tz)
        if m.start() >= after:
            return cand
        best = best or cand
    return best


def parse_due(sent, received_ts):
    """(due_ts, approx) from one sentence, or (None, None). Absolute dates are read with
    dateutil; 'within N (business|calendar) days/hours' counts from the email's date (approx)."""
    from dateutil import parser as dparser
    from dateutil import tz as dtz
    recv = datetime.datetime.fromtimestamp(received_ts)
    for rx in DATE_RES:
        for m in rx.finditer(sent):
            raw = re.sub(r"(\d)(st|nd|rd|th)\b", r"\1", m.group(0))
            raw = re.sub(r"\bof\b", " ", raw)
            raw = re.sub(r"^\s*(mon|tues?|wed(nes)?|thu(rs)?|fri|sat(ur)?|sun)(day)?\.?,?\s+", "", raw, flags=re.I)
            try:
                d = dparser.parse(raw, default=recv.replace(hour=0, minute=0, second=0, microsecond=0))
            except (ValueError, OverflowError, TypeError):
                continue
            has_year = bool(m.lastindex and m.group(m.lastindex)) or bool(re.search(r"\d{4}", raw))
            if not has_year and d < recv - datetime.timedelta(days=60):
                d = d.replace(year=d.year + 1)
            t = _find_time(sent, m.end()) or _find_time(sent)
            h, mi, tzname = t if t else (23, 59, None)
            d = d.replace(hour=h, minute=mi, second=0, microsecond=0, tzinfo=None)
            if tzname:
                zone = dtz.gettz(_TZS.get(tzname.lower(), ""))
                if zone is not None:
                    d = d.replace(tzinfo=zone)
            ts = _local_ts(d)
            if ts < received_ts - 2 * 86400:
                continue  # a date before the email (its own sent date, a past event): not a deadline
            return ts, False
    m = REL_RE.search(sent)
    if m and (ACTION_RE.search(sent) or re.search(r"expir", sent, re.I)):
        g = m.groups()
        num, kind, unit = (g[0], g[1], g[2]) if g[0] else (g[3], g[4], g[5])
        n = _NUMW.get(num.lower()) if not num.isdigit() else int(num)
        unit, kind = unit.lower(), (kind or "").lower()
        if n:
            if unit.startswith(("hour", "hr")):
                return received_ts + n * 3600, True
            if unit.startswith("week"):
                return received_ts + n * 7 * 86400, True
            if kind in ("business", "working"):
                d, left = recv, n
                while left:
                    d += datetime.timedelta(days=1)
                    if d.weekday() < 5:
                        left -= 1
                return _local_ts(d), True
            return received_ts + n * 86400, True
    m = WEEKDAY_RE.search(sent)
    if m:
        want = ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"].index(m.group(1).lower())
        d = recv + datetime.timedelta(days=(want - recv.weekday()) % 7)
        return _local_ts(d.replace(hour=23, minute=59, second=0, microsecond=0)), True
    return None, None


def _status(text):
    head = (text or "")[:4000]
    if REJECT_RE.search(head):
        return "rejected"
    for rx in DONE_RES:
        for m in rx.finditer(head):
            before = head[max(0, m.start() - 14):m.start()].lower()
            if not re.search(r"\b(once|after|when|if|until)\s*$", before):
                return "done"
    return None


def extract_deadline(subject, from_txt, body, received_ts, kind):
    """The deadlines row for one candidate email, or None."""
    if kind not in CANDIDATE_KINDS:
        return None
    if kind == "course" and re.search(r"edstem|piazza", from_txt or "", re.I):
        return None  # forum digests: other students' questions, not their deadlines
    text = f"{subject or ''}.\n{body or ''}"
    company = _course(subject, from_txt) if kind == "course" else _company(from_txt, subject, body)
    status = _status(text) if kind != "course" else None
    ev = evidence_sentences(body or "")
    if not ev and kind != "course" and CUE_RE.search(subject or ""):
        ev = [(subject or "")[:300]]
    due, approx = None, None
    for sent in ev + [re.sub(r"\s+", " ", subject or "")]:  # "...expires in 2 days" is often only in the subject
        due, approx = parse_due(sent, received_ts)
        if due:
            break
    plain = re.sub(r"^(re|fwd?):\s*", "", re.sub(r"\s+", " ", subject or "").strip(), flags=re.I)
    what = f"{kind}: {plain[:90]}"
    if status:
        return dict(company=company, what=what, due_ts=None, approx=0, evidence=ev[:1] or [(subject or "")[:300]],
                    status=status, kind=kind)
    if due is None and kind not in ("interview", "assessment", "offer"):
        return None
    if kind in ("recruiting", "deadline") and due and approx and not any(ACTION_RE.search(e) for e in ev):
        return None
    return dict(company=company, what=what, due_ts=due, approx=1 if approx else 0, evidence=ev, status="open",
                kind=kind)


def _save_body(conn, account, mid, subject, from_txt, date_ts, kind, body):
    body = _clean_text(body)[:BODY_MAX]
    conn.execute("UPDATE msgs SET body=?, snippet=?, body_state=1 WHERE account=? AND id=?",
                 (body, _snippet(body), account, mid))
    row = extract_deadline(subject, from_txt, body, date_ts or time.time(), kind)
    if row:
        conn.execute("INSERT OR REPLACE INTO deadlines(account, id, company, what, due_ts, approx, evidence, status, "
                     "msg_ts, kind) VALUES(?,?,?,?,?,?,?,?,?,?)",
                     (account, mid, row["company"], row["what"], row["due_ts"], row["approx"],
                      json.dumps(row["evidence"], ensure_ascii=False), row["status"], date_ts, row["kind"]))
    else:
        conn.execute("DELETE FROM deadlines WHERE account=? AND id=?", (account, mid))


EXTRACT_VERSION = 4# bump when the deadline rules change: stored text is re-read on the next start


def rebuild_deadlines(conn, force=False):
    """Re-run the deadline rules over the text already stored (no mail is fetched)."""
    _ok, _err, cur = _state(conn, "deadlines")
    if not force and cur.get("version") == EXTRACT_VERSION:
        return 0
    for rid, subject in conn.execute("SELECT rid, subject FROM msgs WHERE subject LIKE '%' || char(10) || '%' "
                                     "OR subject LIKE '%' || char(13) || '%' OR subject LIKE '%' || char(9) || '%'"
                                     ).fetchall():
        conn.execute("UPDATE msgs SET subject=? WHERE rid=?", (re.sub(r"\s+", " ", subject).strip(), rid))
    # The kind rules may have changed too: new candidates get their text fetched on the next pass, and
    # mail that no longer qualifies loses the text it had (the privacy rule applies to old rows too).
    for rid, subject, from_txt, kind, has_body in conn.execute(
            "SELECT rid, subject, from_txt, kind, body IS NOT NULL FROM msgs").fetchall():
        new = classify(subject, from_txt)
        if new == kind:
            continue
        if new in CANDIDATE_KINDS:
            conn.execute("UPDATE msgs SET kind=?, body_state=CASE WHEN body IS NULL THEN 0 ELSE body_state END "
                         "WHERE rid=?", (new, rid))
        elif new == "secret":
            conn.execute("UPDATE msgs SET kind=?, body=NULL, snippet=NULL, body_state=3, subject=? WHERE rid=?",
                         (new, _mask_digits(subject), rid))
        else:
            conn.execute("UPDATE msgs SET kind=?, body=NULL, body_state=3, snippet=CASE WHEN account='outlook' "
                         "THEN snippet ELSE NULL END WHERE rid=?", (new, rid))
    conn.commit()
    n = 0
    for account, mid, subject, from_txt, date_ts, kind, body in conn.execute(
            "SELECT account, id, subject, from_txt, date_ts, kind, body FROM msgs WHERE body IS NOT NULL").fetchall():
        row = extract_deadline(subject, from_txt, body, date_ts or time.time(), kind)
        conn.execute("DELETE FROM deadlines WHERE account=? AND id=?", (account, mid))
        if row:
            conn.execute("INSERT INTO deadlines(account, id, company, what, due_ts, approx, evidence, status, msg_ts, "
                         "kind) VALUES(?,?,?,?,?,?,?,?,?,?)",
                         (account, mid, row["company"], row["what"], row["due_ts"], row["approx"],
                          json.dumps(row["evidence"], ensure_ascii=False), row["status"], date_ts, row["kind"]))
            n += 1
    conn.commit()
    _set_state(conn, "deadlines", ok=True, cursor={"version": EXTRACT_VERSION, "rows": n})
    return n


def upsert_header(conn, row):
    """Insert a header row, or refresh the flags of one already there. Returns True if it was new."""
    row = dict(row, subject=re.sub(r"\s+", " ", row.get("subject") or "").strip())  # folded headers
    kind = classify(row.get("subject"), row.get("from_txt"))
    subject = _mask_digits(row.get("subject")) if kind == "secret" else row.get("subject")
    snippet = None if kind == "secret" else (_snippet(row.get("snippet"), 300) or None)
    cur = conn.execute(
        "INSERT INTO msgs(account, id, entry_id, msgid_hdr, folder, date_ts, date_str, from_txt, to_txt, subject, "
        "unread, snippet, body, kind, synced_ts, uid, inbox, sent, in_default, meeting, body_state) "
        "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,NULL,?,?,?,?,?,?,?,?) ON CONFLICT(account, id) DO NOTHING",
        (row["account"], row["id"], row.get("entry_id"), row.get("msgid_hdr"), row.get("folder"), row.get("date_ts"),
         row.get("date_str"), row.get("from_txt"), row.get("to_txt"), subject, 1 if row.get("unread") else 0,
         snippet, kind, time.time(), row.get("uid"), 1 if row.get("inbox") else 0, 1 if row.get("sent") else 0,
         1 if row.get("in_default", True) else 0, 1 if row.get("meeting") else 0,
         0 if kind in CANDIDATE_KINDS else 3))
    if cur.rowcount:
        return True
    conn.execute("UPDATE msgs SET unread=?, folder=?, inbox=?, sent=?, in_default=?, synced_ts=? "
                 "WHERE account=? AND id=?",
                 (1 if row.get("unread") else 0, row.get("folder"), 1 if row.get("inbox") else 0,
                  1 if row.get("sent") else 0, 1 if row.get("in_default", True) else 0, time.time(),
                  row["account"], row["id"]))
    return False


# --- Gmail ---------------------------------------------------------------------

_MON = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
HEADER_ITEMS = "(UID X-GM-MSGID X-GM-LABELS FLAGS INTERNALDATE BODY.PEEK[HEADER.FIELDS (FROM TO SUBJECT DATE MESSAGE-ID)])"


def _imap_date(ts):
    d = datetime.date.fromtimestamp(ts)
    return f"{d.day:02d}-{_MON[d.month - 1]}-{d.year}"


def _uidset(uids):
    uids = sorted({int(u) for u in uids})
    parts, i = [], 0
    while i < len(uids):
        j = i
        while j + 1 < len(uids) and uids[j + 1] == uids[j] + 1:
            j += 1
        parts.append(str(uids[i]) if i == j else f"{uids[i]}:{uids[j]}")
        i = j + 1
    return ",".join(parts)


def _fetch_parts(data):
    """imaplib FETCH data -> [(meta bytes, literal bytes or None)]. Items after a literal arrive
    as the next bytes element; they are joined back onto that message's meta."""
    out, prev_tuple = [], False
    for part in data or []:
        if isinstance(part, tuple):
            out.append([part[0], part[1]])
            prev_tuple = True
        elif isinstance(part, (bytes, bytearray)):
            if prev_tuple and out:
                out[-1][0] = out[-1][0] + b" " + bytes(part)
            elif re.search(rb"\bUID \d+", part):
                out.append([bytes(part), None])
            prev_tuple = False
    return [(m, lit) for m, lit in out]


def _decode(s, value):
    fn = getattr(s, "_decode_header", None)
    if fn:
        try:
            return fn(value)
        except Exception:
            pass
    from email.header import decode_header, make_header
    try:
        return str(make_header(decode_header(value or "")))
    except Exception:
        return value or ""


class GmailSync:
    def __init__(self, address, s=None):
        self.address, self.s, self.conn = address, _s(s), None
        self.source = f"gmail:{address}"
        self.last_reconcile = 0.0

    def close(self):
        if self.conn is not None:
            try:
                self.conn.logout()
            except Exception:
                pass
        self.conn = None

    def _open(self):
        self.close()
        conn = self.s._imap(self.address)
        typ, _ = conn.select('"[Gmail]/All Mail"', readonly=True)
        if typ != "OK":
            raise RuntimeError("couldn't open All Mail")
        try:
            conn.socket().settimeout(45)  # Gmail sometimes stalls mid-session; fail fast, reconnect, resume
        except Exception:
            pass
        uv = None
        try:
            _typ, val = conn.response("UIDVALIDITY")
            uv = int((val or [b"0"])[0] or 0)
        except Exception:
            pass
        self.conn, self.uidvalidity = conn, uv

    def _ensure(self):
        if self.conn is not None:
            try:
                self.conn.noop()
                return
            except Exception:
                self.close()
        self._open()

    def _headers(self, db, uids, step=250):
        """Headers for these UIDs, skipping ones already stored, committed per batch, so a backfill that
        times out part way picks up where it stopped on the next try."""
        new = 0
        have = {r[0] for r in db.execute("SELECT uid FROM msgs WHERE account=?", (self.address,))}
        uids = sorted({int(u) for u in uids} - have)
        for i in range(0, len(uids), step):
            t0 = time.time()
            typ, data = self.conn.uid("FETCH", _uidset(uids[i:i + step]), HEADER_ITEMS)
            for meta, raw in _fetch_parts(data):
                row = self._row(meta, raw)
                if row and upsert_header(db, row):
                    new += 1
            db.commit()
            if time.time() - t0 > 20:
                _log(f"gmail {self.address}: {step} headers took {time.time() - t0:.0f}s")
        return new

    def _row(self, meta, raw):
        u = re.search(rb"\bUID (\d+)", meta)
        g = re.search(rb"X-GM-MSGID (\d+)", meta)
        if not u:
            return None
        labels = (re.search(rb"X-GM-LABELS \(([^)]*)\)", meta) or [None, b""])[1] or b""
        flags = (re.search(rb"FLAGS \(([^)]*)\)", meta) or [None, b""])[1] or b""
        h = email_lib.message_from_bytes(raw or b"")
        ts = None
        try:
            import imaplib
            tt = imaplib.Internaldate2tuple(meta)
            ts = time.mktime(tt) if tt else None
        except Exception:
            ts = None
        if ts is None:
            try:
                ts = email.utils.parsedate_to_datetime(h.get("Date")).timestamp()
            except Exception:
                ts = time.time()
        return {"account": self.address, "id": g.group(1).decode() if g else u.group(1).decode(),
                "uid": int(u.group(1)), "msgid_hdr": (h.get("Message-ID") or "").strip(), "folder": None,
                "date_ts": ts, "date_str": h.get("Date", ""), "from_txt": _decode(self.s, h.get("From")),
                "to_txt": _decode(self.s, h.get("To")), "subject": _decode(self.s, h.get("Subject")),
                "unread": b"\\Seen" not in flags, "inbox": b"\\Inbox" in labels or b"\\\\Inbox" in labels,
                "sent": b"\\Sent" in labels, "in_default": True}

    def _flags(self, db, uids):
        uids = sorted({int(u) for u in uids})
        for i in range(0, len(uids), 1000):
            typ, data = self.conn.uid("FETCH", _uidset(uids[i:i + 1000]), "(UID FLAGS X-GM-LABELS)")
            for meta, _lit in _fetch_parts(data):
                u = re.search(rb"\bUID (\d+)", meta)
                if not u:
                    continue
                labels = (re.search(rb"X-GM-LABELS \(([^)]*)\)", meta) or [None, b""])[1] or b""
                flags = (re.search(rb"FLAGS \(([^)]*)\)", meta) or [None, b""])[1] or b""
                db.execute("UPDATE msgs SET unread=?, inbox=?, sent=? WHERE account=? AND uid=?",
                           (0 if b"\\Seen" in flags else 1, 1 if b"\\Inbox" in labels else 0,
                            1 if b"\\Sent" in labels else 0, self.address, int(u.group(1))))
        db.commit()

    def _search_since(self, ts):
        typ, data = self.conn.uid("SEARCH", None, f"SINCE {_imap_date(ts)}")
        return [int(x) for x in (data[0] or b"").split()] if data else []

    def bodies(self, db, budget=180.0):
        """Fetch the text of candidate mail still missing it (first 300 KB of each, no attachments)."""
        t0, done = time.time(), 0
        while time.time() - t0 < budget:
            rows = db.execute("SELECT id, uid, subject, from_txt, date_ts, kind FROM msgs WHERE account=? AND "
                              "body_state=0 ORDER BY date_ts DESC LIMIT 25", (self.address,)).fetchall()
            if not rows:
                break
            by_uid = {r[1]: r for r in rows if r[1]}
            got = set()
            if by_uid:
                typ, data = self.conn.uid("FETCH", _uidset(by_uid), f"(UID BODY.PEEK[]<0.{BODY_FETCH}>)")
                for meta, raw in _fetch_parts(data):
                    u = re.search(rb"\bUID (\d+)", meta)
                    if not u or int(u.group(1)) not in by_uid or raw is None:
                        continue
                    r = by_uid[int(u.group(1))]
                    try:
                        text = self.s._body_text(email_lib.message_from_bytes(raw))
                    except Exception:
                        text = ""
                    _save_body(db, self.address, r[0], r[2], r[3], r[4], r[5], text)
                    got.add(r[0])
                    done += 1
            for r in rows:
                if r[0] not in got:
                    db.execute("UPDATE msgs SET body_state=2 WHERE account=? AND id=?", (self.address, r[0]))
            db.commit()
        return done

    def cycle(self, db, full=False):
        """One sync pass. Returns counts."""
        self._ensure()
        now = time.time()
        _ok, _err, cur = _state(db, self.source)
        if cur.get("uidvalidity") != self.uidvalidity or not cur.get("backfilled"):
            if cur.get("uidvalidity") not in (None, self.uidvalidity):
                db.execute("DELETE FROM msgs WHERE account=?", (self.address,))
                db.execute("DELETE FROM deadlines WHERE account=?", (self.address,))
                db.commit()
            uids = self._search_since(now - KEEP_DAYS * 86400)
            new = self._headers(db, uids)
            cur = {"uidvalidity": self.uidvalidity, "last_uid": max(uids) if uids else 0, "backfilled": True}
            full = True
        else:
            last = int(cur.get("last_uid") or 0)
            typ, data = self.conn.uid("FETCH", f"{last + 1}:*", HEADER_ITEMS)
            new = 0
            for meta, raw in _fetch_parts(data):
                row = self._row(meta, raw)
                if row and row["uid"] > last and upsert_header(db, row):
                    new += 1
                if row:
                    cur["last_uid"] = max(int(cur.get("last_uid") or 0), row["uid"])
            db.commit()
        if full or now - self.last_reconcile >= RECONCILE_EVERY:
            present = set(self._search_since(now - KEEP_DAYS * 86400))
            if present:
                gone = [r[0] for r in db.execute("SELECT uid FROM msgs WHERE account=? AND date_ts > ?",
                                                 (self.address, now - (KEEP_DAYS - 2) * 86400)) if r[0] not in present]
                for u in gone:
                    db.execute("DELETE FROM msgs WHERE account=? AND uid=?", (self.address, u))
                db.commit()
                self._flags(db, present)
            self.last_reconcile = now
        else:
            recent = [r[0] for r in db.execute("SELECT uid FROM msgs WHERE account=? AND date_ts > ?",
                                               (self.address, now - 3 * 86400)) if r[0]]
            if recent:
                self._flags(db, recent)
        bodies = self.bodies(db)
        prune(db, now)
        cur["pending_bodies"] = db.execute("SELECT COUNT(*) FROM msgs WHERE account=? AND body_state=0",
                                           (self.address,)).fetchone()[0]
        _set_state(db, self.source, ok=True, cursor=cur)
        return {"new": new, "bodies": bodies}


# --- Outlook ---------------------------------------------------------------------

_OL_SKIP_NAMES = {"calendar", "contacts", "tasks", "notes", "journal", "conversation action settings",
                  "quick step settings", "rss feeds", "rss subscriptions", "sync issues", "conflicts",
                  "local failures", "server failures", "yammer root", "externalcontacts", "files",
                  "social activity notifications", "conversation history", "deleted items", "junk email",
                  "outbox", "drafts", "suggested contacts", "personmetadata", "archive settings"}
_PR = "http://schemas.microsoft.com/mapi/proptag/"
OL_COLUMNS = ["EntryID", "Subject", "SenderName", "ReceivedTime", "UnRead", "MessageClass", "To",
              _PR + "0x5D01001F", _PR + "0x3FD9001F", _PR + "0x1035001F"]


def _ol_ns():
    """Outlook's MAPI namespace, the same way the live mail tools get it (s._outlook: joins the running
    Outlook, or starts it with no window, as every live mail_search already does)."""
    return _s()._outlook()[1]


def _ol_short(entry_id):
    return "o" + hashlib.sha1(entry_id.encode()).hexdigest()[:8]  # the same id outlook_search hands out


def _naive(t):
    return datetime.datetime(t.year, t.month, t.day, t.hour, t.minute, t.second)


def _retry_busy(fn, tries=3):
    for i in range(tries):
        try:
            return fn()
        except Exception as e:
            if i == tries - 1 or not ("rejected by callee" in str(e).lower() or "-2147418111" in str(e)
                                      or "call was rejected" in str(e).lower()):
                raise
            time.sleep(2 + i * 2)


def _ol_folders(ns):
    """[(folder, name, in_default_scope)] for every mail folder in the default store."""
    skip_ids = set()
    for n in (3, 4, 16, 23):  # Deleted Items, Outbox, Drafts, Junk
        try:
            skip_ids.add(ns.GetDefaultFolder(n).EntryID)
        except Exception:
            pass
    inbox, sent = ns.GetDefaultFolder(6), ns.GetDefaultFolder(5)
    default = {inbox.EntryID, sent.EntryID}
    for sub in inbox.Folders:
        default.add(sub.EntryID)
    root = inbox.Parent
    out, stack = [], [root]
    while stack:
        f = stack.pop()
        for sub in f.Folders:
            try:
                if sub.EntryID in skip_ids or sub.Name.lower() in _OL_SKIP_NAMES or sub.DefaultItemType != 0:
                    continue
                name = sub.Name
                out.append((sub, name, sub.EntryID in default or name.lower() == "archive"))
                stack.append(sub)
            except Exception:
                continue
    return out, inbox.EntryID, sent.EntryID


def outlook_mail_pass(full=False, s=None, budget=60.0):
    s = _s(s)
    db = connect()
    try:
        last, _err, cur = _state(db, "outlook")
        now = time.time()
        if full or not cur.get("backfilled"):
            since = now - KEEP_DAYS * 86400
        else:
            since = max(now - KEEP_DAYS * 86400, min((last or now) - 600, now - 86400))
        ns = _retry_busy(_ol_ns)
        folders, inbox_id, sent_id = _retry_busy(lambda: _ol_folders(ns))
        stamp = datetime.datetime.fromtimestamp(since).strftime("%m/%d/%Y %I:%M %p")
        seen, new, failed = set(), 0, 0
        for f, name, in_default in folders:
            try:
                table = _retry_busy(lambda: f.GetTable(f"[ReceivedTime] >= '{stamp}'", 0))
                cols = table.Columns
                cols.RemoveAll()
                have = []
                for c in OL_COLUMNS:
                    try:
                        cols.Add(c)
                        have.append(c)
                    except Exception:
                        pass
                fid = f.EntryID
                while not table.EndOfTable:
                    rows = table.GetArray(500)
                    if not rows:
                        break
                    for vals in rows:
                        v = dict(zip(have, vals))
                        mclass = str(v.get("MessageClass") or "")
                        if not mclass.startswith(("IPM.Note", "IPM.Schedule.Meeting")):
                            continue
                        eid = str(v.get("EntryID") or "")
                        when = v.get("ReceivedTime")
                        if not eid or when is None:
                            continue
                        naive = _naive(when)
                        sender = str(v.get("SenderName") or "?")
                        smtp = str(v.get(_PR + "0x5D01001F") or "")
                        row = {"account": "outlook", "id": _ol_short(eid), "entry_id": eid,
                               "msgid_hdr": str(v.get(_PR + "0x1035001F") or "").strip(), "folder": name,
                               "date_ts": time.mktime(naive.timetuple()),
                               "date_str": naive.strftime("%a %b %d %Y %I:%M%p").replace(" 0", " "),
                               "from_txt": f"{sender} <{smtp}>" if smtp else sender, "to_txt": str(v.get("To") or ""),
                               "subject": str(v.get("Subject") or "(no subject)"), "unread": bool(v.get("UnRead")),
                               "snippet": str(v.get(_PR + "0x3FD9001F") or ""), "inbox": fid == inbox_id,
                               "sent": fid == sent_id, "in_default": in_default,
                               "meeting": mclass.startswith("IPM.Schedule.Meeting")}
                        seen.add(row["id"])
                        if upsert_header(db, row):
                            new += 1
                db.commit()
            except Exception as e:
                failed += 1
                _log(f"outlook folder {name}: {e}")
        if (full or not cur.get("backfilled")) and not failed:  # a folder that failed isn't evidence of deletes
            gone = [r[0] for r in db.execute("SELECT id FROM msgs WHERE account='outlook' AND date_ts >= ?",
                                             (since + 86400,)) if r[0] not in seen]
            for mid in gone:
                db.execute("DELETE FROM msgs WHERE account='outlook' AND id=?", (mid,))
            db.commit()
            cur["backfilled"] = True
            cur["last_full"] = now
        t0, bodies = time.time(), 0
        while time.time() - t0 < budget:
            rows = db.execute("SELECT id, entry_id, subject, from_txt, date_ts, kind FROM msgs WHERE account='outlook' "
                              "AND body_state=0 ORDER BY date_ts DESC LIMIT 20").fetchall()
            if not rows:
                break
            for mid, eid, subject, from_txt, date_ts, kind in rows:
                try:
                    it = _retry_busy(lambda: ns.GetItemFromID(eid))
                    _save_body(db, "outlook", mid, subject, from_txt, date_ts, kind, it.Body or "")
                    bodies += 1
                except Exception:
                    db.execute("UPDATE msgs SET body_state=2 WHERE account='outlook' AND id=?", (mid,))
            db.commit()
        prune(db, now)
        cur["pending_bodies"] = db.execute("SELECT COUNT(*) FROM msgs WHERE account='outlook' AND body_state=0"
                                           ).fetchone()[0]
        _set_state(db, "outlook", ok=True, cursor=cur)
        return {"new": new, "bodies": bodies, "folders": len(folders)}
    finally:
        db.close()


def _jsonable(ev):
    return {k: (v.isoformat() if isinstance(v, datetime.datetime) else v) for k, v in ev.items()}


def _store_events(source, events):
    db = connect()
    try:
        db.execute("DELETE FROM events WHERE source=?", (source,))
        for e in events:
            st, en = e.get("start"), e.get("end") or e.get("start")
            if not isinstance(st, datetime.datetime):
                continue
            key = e.get("key") or f"{e.get('id') or hashlib.sha1(str(e.get('subject')).encode()).hexdigest()[:8]}" \
                                  f"@{st.isoformat()}"
            db.execute("INSERT OR REPLACE INTO events(source, id, start_ts, end_ts, title, location, data) "
                       "VALUES(?,?,?,?,?,?,?)",
                       (source, key, time.mktime(st.timetuple()), time.mktime(en.timetuple()),
                        e.get("subject") or "", e.get("location") or "", json.dumps(_jsonable(e), default=str)))
        _set_state(db, source, ok=True, cursor={"count": len(events)})
        db.commit()
    finally:
        db.close()


def _window():
    now = datetime.datetime.now()
    return now - datetime.timedelta(days=1), now + datetime.timedelta(days=32)


def outlook_calendar_pass(s=None):
    s = _s(s)
    start, end = _window()
    events = _retry_busy(lambda: s.outlook_events(start, end))
    _store_events("outlook_cal", events)
    return len(events)


def canvas_pass(s=None):
    s = _s(s)
    n = {}
    start, end = _window()
    if s.canvas_connected():
        items = s.canvas_calendar_items(start, end)
        _store_events("canvas", items)
        n["canvas"] = len(items)
    if getattr(s, "google_connected", lambda: False)():
        items = s.google_calendar_events(start, end)
        _store_events("google_cal", items)
        n["google_cal"] = len(items)
    return n


class _Worker:
    """One long-lived thread that runs every Outlook pass (COM is initialised on it once). The caller
    waits at most `timeout`; a pass that hangs marks its source stale and no new pass is queued until
    it ends, so hung COM calls never pile up."""

    def __init__(self, name="index-outlook-com"):
        import queue
        self.q, self.busy = queue.Queue(), threading.Event()
        self.th = threading.Thread(target=self._run, daemon=True, name=name)
        self.th.start()

    def _run(self):
        try:
            import pythoncom
            pythoncom.CoInitialize()
        except Exception:
            pass
        while True:
            fn, box, done = self.q.get()
            try:
                box["r"] = fn()
            except Exception as e:
                box["e"] = e
            finally:
                self.busy.clear()
                done.set()

    def run(self, fn, timeout):
        if self.busy.is_set():
            return {"e": RuntimeError("previous pass still stuck")}
        box, done = {}, threading.Event()
        self.busy.set()
        self.q.put((fn, box, done))
        if not done.wait(timeout):
            return {"e": RuntimeError(f"pass took over {timeout:.0f} s")}
        return box


_worker = []
_worker_lock = threading.Lock()


def watchdog(source, fn, timeout=PASS_TIMEOUT):
    """Run one Outlook pass on the COM worker with a timeout; on a hang or error, record it and go on."""
    with _worker_lock:
        if not _worker:
            _worker.append(_Worker())
    box = _worker[0].run(fn, timeout)
    if "e" in box:
        _record_err(source, box["e"])
        return None
    return box.get("r")


# --- readers (job side): never raise, None means "use the live tool" ------------------

def _ages(conn, sources):
    out = {}
    for src in sources:
        last, _err, cur = _state(conn, src)
        out[src] = (time.time() - last) if last else None
        if src.startswith(("gmail:", "outlook")) and src != "outlook_cal" and not cur.get("backfilled"):
            out[src] = None
    return out


def fresh(source, max_age=MAIL_MAX_AGE):
    try:
        if is_off():
            return False
        conn = _reader()
        if conn is None:
            return False
        try:
            age = _ages(conn, [source]).get(source)
        finally:
            conn.close()
        return age is not None and age <= max_age
    except Exception:
        return False


def _mail_sources(s):
    srcs = []
    try:
        if s.outlook_available():
            srcs.append("outlook")
    except Exception:
        pass
    try:
        if not s.remote_only():
            srcs += [f"gmail:{a}" for a in s.email_accounts()]
    except Exception:
        pass
    return srcs


def _ago(sec):
    sec = max(0, int(sec or 0))
    return "just now" if sec < 60 else f"{sec // 60} min ago"


class Unsupported(Exception):
    pass


_TOKEN_RE = re.compile(r'\s*(?:(\()|(\))|(\{)|(\})|(-?)(\w+):("[^"]*"|[^\s(){}"]+)|(-?)"([^"]*)"|(-?)([^\s(){}"]+))')


def _tokens(query):
    pos, out, q = 0, [], query or ""
    while pos < len(q):
        m = _TOKEN_RE.match(q, pos)
        if not m or m.end() == pos:
            if q[pos:].strip():
                raise Unsupported(q[pos:])
            break
        pos = m.end()
        if m.group(1):
            out.append(("(",))
        elif m.group(2):
            out.append((")",))
        elif m.group(3):
            out.append(("{",))
        elif m.group(4):
            out.append(("}",))
        elif m.group(6):
            out.append(("op", bool(m.group(5)), m.group(6).lower(), m.group(7).strip('"')))
        elif m.group(9) is not None:
            out.append(("phrase", bool(m.group(8)), m.group(9)))
        elif m.group(11):
            w = m.group(11)
            if w in ("OR", "|"):
                out.append(("OR",))
            elif w == "AND":
                continue
            elif w.endswith(":"):
                raise Unsupported(w)  # from:(a OR b) and the like
            else:
                out.append(("word", bool(m.group(10)), w))
    return out


def _parse_time_val(val):
    for fmt in ("%Y/%m/%d", "%Y-%m-%d", "%m/%d/%Y", "%Y/%m/%d"):
        try:
            return time.mktime(datetime.datetime.strptime(val, fmt).timetuple())
        except ValueError:
            continue
    raise Unsupported(val)


class _Query:
    """Gmail-style search words -> one SQL condition over msgs (text words through FTS5)."""

    def __init__(self, query, now=None):
        self.now = time.time() if now is None else now
        self.params, self.lower, self.has_in = [], None, False
        self.toks, self.i = _tokens(query), 0
        self.sql = self._and(None) or "1"

    def _peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def _and(self, until, top=True):
        parts = []
        while self._peek() is not None and self._peek()[0] != until:
            if self._peek()[0] in (")", "}"):
                raise Unsupported("unbalanced")
            parts.append(self._or(top))
        return " AND ".join(f"({p})" for p in parts if p) if parts else ""

    def _or(self, top):
        before = self.lower
        left = self._atom(top)
        alts = [left]
        while self._peek() is not None and self._peek()[0] == "OR":
            self.i += 1
            alts.append(self._atom(False))
        if len(alts) == 1:
            return left
        self.lower = before  # a date inside an OR doesn't bound the whole search
        return " OR ".join(f"({a or '1'})" for a in alts)

    def _atom(self, top):
        tok = self._peek()
        if tok is None:
            raise Unsupported("dangling")
        self.i += 1
        if tok[0] == "(":
            inner = self._and(")", top=False)
            if self._peek() is None:
                raise Unsupported("unclosed (")
            self.i += 1
            return inner or "1"
        if tok[0] == "{":
            alts = []
            while self._peek() is not None and self._peek()[0] != "}":
                if self._peek()[0] == "OR":
                    self.i += 1
                    continue
                alts.append(self._atom(False))
            if self._peek() is None:
                raise Unsupported("unclosed {")
            self.i += 1
            return " OR ".join(f"({a or '1'})" for a in alts) if alts else "1"
        if tok[0] == "OR":
            raise Unsupported("OR")
        neg = tok[1]
        sql = self._leaf(tok, top and not neg)
        return f"NOT ({sql})" if neg and sql != "1" else sql

    def _fts(self, text, prefix):
        terms = re.findall(r"\w+", text)
        if not terms:
            return "1"
        q = '"' + text.replace('"', '""') + '"' + ("*" if prefix else "")
        self.params.append(q)
        return "rid IN (SELECT rowid FROM msgs_fts WHERE msgs_fts MATCH ?)"

    def _like(self, col, val):
        self.params.append(f"%{val}%")
        return f"{col} LIKE ?"

    def _bound(self, ts, top):
        if top:
            self.lower = ts if self.lower is None else max(self.lower, ts)

    def _leaf(self, tok, top):
        kind = tok[0]
        if kind == "phrase":
            return self._fts(tok[2], False)
        if kind == "word":
            w = tok[2]
            return self._fts(w, len(w) >= 4 and re.fullmatch(r"\w+", w) is not None)
        _, neg, key, val = tok
        low = val.lower()
        if key == "from":
            if low == "me":
                raise Unsupported("from:me")
            return self._like("from_txt", val)
        if key == "to":
            if low == "me":
                raise Unsupported("to:me")
            return self._like("to_txt", val)
        if key == "subject":
            return self._like("subject", val)
        if key in ("newer_than", "older_than"):
            m = re.fullmatch(r"(\d+)([hdwmy])", low)
            if not m:
                raise Unsupported(val)
            sec = int(m.group(1)) * {"h": 3600, "d": 86400, "w": 7 * 86400, "m": 30 * 86400, "y": 365 * 86400}[m.group(2)]
            ts = self.now - sec
            self.params.append(ts)
            if key == "newer_than":
                self._bound(ts, top)
                return "date_ts >= ?"
            return "date_ts < ?"
        if key in ("after", "before"):
            ts = _parse_time_val(val)
            self.params.append(ts)
            if key == "after":
                self._bound(ts, top)
                return "date_ts >= ?"
            return "date_ts < ?"
        if key == "is":
            if low == "unread":
                return "unread = 1"
            if low == "read":
                return "unread = 0"
            raise Unsupported(f"is:{val}")
        if key == "in":
            if neg and low in ("spam", "trash", "chats", "chat"):
                return "1"  # the index never holds those anyway
            if neg:
                raise Unsupported(f"-in:{val}")
            self.has_in = True
            if low == "inbox":
                return "inbox = 1"
            if low == "sent":
                return "sent = 1"
            if low in ("anywhere", "all", "everywhere"):
                return "1"
            raise Unsupported(f"in:{val}")
        raise Unsupported(f"{key}:")


def _line(r):
    flags = (" UNREAD" if r["unread"] else "") + (" [meeting invite]" if r["meeting"] else "")
    where = f" in {r['folder']}" if r["account"] == "outlook" and r["folder"] else ""
    one = lambda v: re.sub(r"\s+", " ", str(v or "")).strip()
    return (f"- id={r['id']} account={r['account']}{where} | {one(r['date_str'])} | From: {one(r['from_txt'])} | "
            f"{one(r['subject'])}{flags}")


def _evidence_line(conn, r):
    if r["kind"] not in CANDIDATE_KINDS:
        return None
    d = conn.execute("SELECT evidence FROM deadlines WHERE account=? AND id=?", (r["account"], r["id"])).fetchone()
    text = None
    if d and d[0]:
        try:
            ev = json.loads(d[0])
            text = ev[0] if ev else None
        except ValueError:
            text = None
    if not text and r["kind"] in ("interview", "assessment", "offer"):  # list / course mail: only a real deadline line
        text = (r["snippet"] or "")[:240]
    text = re.sub(r"\s+", " ", text or "").strip()[:240]
    return f"  > {text}" if text else None


def search(query, count=25, s=None, now=None):
    """mail_search's answer from the index, in mail_search's own shape, or None (use live)."""
    try:
        if is_off():
            return None
        conn = _reader()
        if conn is None:
            return None
        try:
            return _search(conn, _s(s), query or "", max(1, min(50, int(count or 25))), now)
        finally:
            conn.close()
    except Exception as e:
        _log(f"search {query!r}: {e}")
        return None


last_hits = [0, None]  # (rows, oldest source age) of the last search(), for pd_fast's log


def _search(conn, s, query, count, now):
    now = time.time() if now is None else now
    last_hits[0], last_hits[1] = 0, None
    sources = _mail_sources(s)
    if not sources:
        return None
    ages = _ages(conn, sources)
    if any(a is None or a > MAIL_MAX_AGE for a in ages.values()):
        return None
    try:
        q = _Query(query, now)
    except Unsupported:
        return None
    cutoff = now - KEEP_DAYS * 86400
    if q.lower is not None and q.lower < cutoff - 3600:
        return None  # reaches past the 60 days the index keeps
    bounded = q.lower is not None
    order = {"outlook": "date_ts DESC"}
    rows_by = {}
    for src in sources:
        account = "outlook" if src == "outlook" else src.split(":", 1)[1]
        scope = " AND in_default = 1" if account == "outlook" and not q.has_in else ""
        sql = (f"SELECT * FROM msgs WHERE account = ? AND date_ts >= ?{scope} AND ({q.sql}) "
               f"ORDER BY {order.get(account, 'uid DESC, date_ts DESC')} LIMIT ?")
        rows = conn.execute(sql, [account, cutoff] + q.params + [count]).fetchall()
        if not bounded and len(rows) < count:
            return None  # with no date limit, live search could find older mail the index doesn't keep
        rows_by[account] = rows
    results = [r for src in sources for r in rows_by["outlook" if src == "outlook" else src.split(":", 1)[1]]]
    if "outlook" in rows_by:  # the remote backend mail forwarded into Gmail is the same message: show it once, from Outlook
        seen = {(r["subject"] or "").strip().lower() for r in rows_by["outlook"]}
        try:
            fwd = {f["into"] for f in s.email_forwards()}
        except Exception:
            fwd = set()
        results = [r for r in results if r["account"] == "outlook" or r["account"] not in fwd
                   or (r["subject"] or "").strip().lower() not in seen]
    if not results:
        return None
    # One list, newest first across accounts: the prefetch cuts each result at 3,500 characters, and
    # per-account order let 25 Outlook list emails crowd out every Gmail recruiting email.
    results.sort(key=lambda r: -(r["date_ts"] or 0))
    oldest = max(ages.values())
    last_hits[0], last_hits[1] = len(results), round(oldest, 1)
    src_names = (["Outlook (full the remote backend mailbox)"] if "outlook" in rows_by else []) + \
                [f"Gmail {a}" for a in rows_by if a != "outlook"]
    lines = [f"Emails matching {query!r}, newest first (searched: {', '.join(src_names)}; from Dot's "
             f"mail index, synced {_ago(oldest)}. The index has 60 days of every subject and sender plus the full "
             "text of recruiting, assessment, interview and course mail; run mail_search to search other mail's "
             "text). Open one with mail_read using its id and account:"]
    for r in results:
        if r["account"] == "outlook" and r["entry_id"]:
            try:
                s._ol_short(r["entry_id"])  # so a later live mail_read of this id finds it
            except Exception:
                pass
        lines.append(_line(r))
        ev = _evidence_line(conn, r)
        if ev:
            lines.append(ev)
    return "\n".join(lines)


def _day(ts, with_time=True):
    d = datetime.datetime.fromtimestamp(ts)
    out = d.strftime("%a %b %d").replace(" 0", " ")
    if with_time and not (d.hour == 23 and d.minute == 59) and (d.hour or d.minute):
        out += " " + d.strftime("%I:%M%p").lstrip("0").lower()
    return out


def deadline_digest(back_days=30, ahead_days=30, limit_chars=3500, s=None, now=None):
    """Open recruiting / assessment / interview / course deadlines found in mail, soonest first."""
    try:
        if is_off():
            return None
        conn = _reader()
        if conn is None:
            return None
        try:
            return _digest(conn, _s(s), back_days, ahead_days, limit_chars, now)
        finally:
            conn.close()
    except Exception as e:
        _log(f"digest: {e}")
        return None


def _digest(conn, s, back_days, ahead_days, limit_chars, now):
    now = time.time() if now is None else now
    sources = _mail_sources(s)
    if not sources:
        return None
    ages = _ages(conn, sources)
    if any(a is None or a > MAIL_MAX_AGE for a in ages.values()):
        return None
    accounts = ["outlook" if x == "outlook" else x.split(":", 1)[1] for x in sources]
    marks = ",".join("?" * len(accounts))
    rows = conn.execute(
        f"SELECT d.*, m.sent AS sent, m.from_txt AS from_txt FROM deadlines d JOIN msgs m "
        f"ON m.account = d.account AND m.id = d.id WHERE d.msg_ts >= ? AND d.account IN ({marks}) "
        f"ORDER BY d.msg_ts DESC", [now - back_days * 86400] + accounts).fetchall()
    try:
        mine = [a.lower() for a in s.email_accounts()]
    except Exception:
        mine = []
    # Their own mail (sent, or from their own address) is never a to-do from someone else.
    rows = [r for r in rows if not r["sent"] and not any(a in (r["from_txt"] or "").lower() for a in mine)]
    closers = [r for r in rows if r["status"] in ("done", "rejected")]
    groups = {"jobs": [], "school": []}
    past, closed_notes, keys = [], [], set()
    for r in rows:
        if r["status"] != "open":
            continue
        if any(c["msg_ts"] >= r["msg_ts"] and _same_company(c["company"], r["company"]) for c in closers):
            continue
        # The same mail forwarded from the remote backend into Gmail, or one reminder after another: shown once.
        what_key = re.sub(r"[^a-z0-9]", "", re.sub(r"^\w+:\s*|\[[^]]*\]", "", (r["what"] or "").lower()))[:40]
        key = (what_key, round((r["due_ts"] or 0) / 86400))
        if key in keys:
            continue
        keys.add(key)
        school = r["kind"] == "course"
        if r["due_ts"] and r["due_ts"] > now + (14 if school else ahead_days) * 86400:
            continue
        if r["due_ts"] and r["due_ts"] < now:
            if r["due_ts"] >= now - 7 * 86400 and not school:
                past.append(r)
            continue
        if school and not r["due_ts"]:
            continue
        groups["school" if school else "jobs"].append(r)
    for g in groups.values():
        g.sort(key=lambda r: (r["due_ts"] is None, r["due_ts"] or -r["msg_ts"]))
    seen_close = set()
    for c in closers:
        k = _norm_company(c["company"])
        if k in seen_close:
            continue
        seen_close.add(k)
        closed_notes.append(f"{c['company']} ({'not moving forward' if c['status'] == 'rejected' else 'done'} "
                            f"{_day(c['msg_ts'], False)})")
    head = (f"[Deadlines and to-dos found in their mail from the last {back_days} days, soonest first (Dot's mail "
            "index). ~ means estimated from \"within N days\" and the email's date; check the quoted line, and open "
            "the email with mail_read (id and account given) before relying on it.]")
    out, used = [head], len(head)
    tail_room = 450 if (past or closed_notes) else 0
    for title, items, share in (("Jobs and recruiting:", groups["jobs"], 0.65), ("School (next 2 weeks):",
                                                                                groups["school"], 1.0)):
        cap = used + int((limit_chars - used - tail_room) * share)
        out.append(title)
        used += len(title) + 1
        shown = 0
        for r in items:
            try:
                ev = json.loads(r["evidence"] or "[]")
            except ValueError:
                ev = []
            due = (f"due {_day(r['due_ts'], not r['approx'])}" + (" ~" if r["approx"] else "")) if r["due_ts"] \
                else "no date found"
            line = (f"- {due} · {r['company']} · {r['what']}" + (f" · \"{ev[0][:200]}\"" if ev else "")
                    + f" (id={r['id']} account={r['account']})")
            if used + len(line) + 1 > cap - 16:
                out.append(f"- …{len(items) - shown} more")
                used += 16
                break
            out.append(line)
            used += len(line) + 1
            shown += 1
        if not items:
            out.append("- nothing open found")
            used += 22
    for label, vals in (("Past due in the last week, no sign they were done", [
            f"{r['company']} {r['what'].split(':')[0]} ({_day(r['due_ts'], False)}, id={r['id']})" for r in past]),
                        ("Already finished or closed", closed_notes)):
        if vals:
            line = f"{label}: " + "; ".join(vals)
            room = limit_chars - used - 2
            if room > 40:
                out.append(line[:room])
                used += min(len(line), room) + 1
    text = "\n".join(out)
    return text[:limit_chars]


def _fmt_span(s_, e_, all_day=False):
    t = lambda d: d.strftime("%I:%M%p").lstrip("0").lower()
    if all_day:
        return s_.strftime("%a %b %d").replace(" 0", " ") + " (all day)"
    if e_ <= s_:
        return f"{s_.strftime('%a %b %d').replace(' 0', ' ')} by {t(s_)}"
    same = s_.date() == e_.date()
    return f"{s_.strftime('%a %b %d').replace(' 0', ' ')} {t(s_)}–{t(e_) if same else e_.strftime('%a %b %d ') + t(e_)}"


def _mark_clashes(events):
    timed = [e for e in events if not e["all_day"] and e["busy"] != "free" and e["end"] > e["start"]]
    for i, a in enumerate(timed):
        for b in timed[i + 1:]:
            if b["start"] < a["end"] and a["start"] < b["end"]:
                a.setdefault("clash", []).append(b["subject"])
                b.setdefault("clash", []).append(a["subject"])
    return events


def agenda(days=7, s=None, now=None):
    """calendar_list's answer (today for `days` days) from the index, in its own shape, or None."""
    try:
        if is_off():
            return None
        days = max(1, min(62, int(days or 7)))
        if days > 31:
            return None
        conn = _reader()
        if conn is None:
            return None
        try:
            return _agenda(conn, _s(s), days, now)
        finally:
            conn.close()
    except Exception as e:
        _log(f"agenda: {e}")
        return None


def _agenda(conn, s, days, now):
    now_dt = datetime.datetime.fromtimestamp(time.time() if now is None else now)
    start = now_dt.replace(hour=0, minute=0, second=0, microsecond=0)
    end = start + datetime.timedelta(days=days)
    need, labels = [], {}
    if s.outlook_available():
        need.append(("outlook_cal", CAL_MAX_AGE))
        labels["outlook_cal"] = "Outlook calendar"
    if s.canvas_connected():
        need.append(("canvas", CANVAS_MAX_AGE))
        labels["canvas"] = "Canvas due dates and course events"
    if getattr(s, "google_connected", lambda: False)():
        need.append(("google_cal", CANVAS_MAX_AGE))
        labels["google_cal"] = "Google Calendar"
    if not need:
        return None
    ages = _ages(conn, [n for n, _m in need])
    for name, max_age in need:
        if ages.get(name) is None or ages[name] > max_age:
            return None
    events = []
    marks = ",".join("?" * len(need))
    for (data,) in conn.execute(f"SELECT data FROM events WHERE source IN ({marks})", [n for n, _m in need]):
        e = json.loads(data)
        for k in ("start", "end"):
            e[k] = datetime.datetime.fromisoformat(e[k])
        e.setdefault("all_day", False)
        e.setdefault("busy", "busy")
        e.setdefault("location", "")
        e.setdefault("meeting", False)
        e.setdefault("response", "")
        e.setdefault("id", "")
        if e["start"] < end and (e["end"] > start or e["start"] >= start):
            events.append(e)
    events.sort(key=lambda e: e["start"])
    _mark_clashes(events)  # the same rules and format as calendar_list (copied: pure formatting)
    span = _fmt_span
    oldest = max(a for a in ages.values() if a is not None)
    lines = [f"Calendar {start:%a %b %d} to {end - datetime.timedelta(minutes=1):%a %b %d} "
             f"(sources: {', '.join(labels[n] for n, _m in need)}; from Dot's calendar index, synced {_ago(oldest)}). "
             "Times are the user's local time:"]
    for e in events:
        bits = [span(e["start"], e["end"], e["all_day"]), e["subject"]]
        if e["location"]:
            bits.append(f"@ {e['location']}")
        if e["meeting"] and e["response"]:
            bits.append(f"[{e['response']}]")
        if e.get("recurring"):
            bits.append("repeats (changing it changes the whole series)")
        if e.get("clash"):
            bits.append(f"CLASHES with {', '.join(e['clash'][:3])}")
        tag = f"{e.get('source', '')}" + (f" id={e['id']}" if e["id"] else "")
        lines.append(f"- {' · '.join(bits)}  ({tag})")
    return "\n".join(lines) if events else lines[0] + "\n(nothing scheduled)"


def mail_age_s(s=None):
    try:
        conn = _reader()
        if conn is None:
            return None
        try:
            ages = _ages(conn, _mail_sources(_s(s)))
        finally:
            conn.close()
        vals = [a for a in ages.values() if a is not None]
        return round(max(vals), 1) if vals else None
    except Exception:
        return None


# --- the background process -----------------------------------------------------------

def _lock_file():
    return dots_dir() / "index.lock"


def _try_lock():
    """An fd holding the single-instance lock, or None if another process holds it."""
    path = _lock_file()
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(str(path), os.O_RDWR | os.O_CREAT)
    try:
        if sys.platform == "win32":
            import msvcrt
            os.lseek(fd, 0, 0)
            msvcrt.locking(fd, msvcrt.LK_NBLCK, 1)
        else:  # pragma: no cover
            import fcntl
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fd
    except OSError:
        os.close(fd)
        return None


def _unlock(fd):
    try:
        if sys.platform == "win32":
            import msvcrt
            os.lseek(fd, 0, 0)
            msvcrt.locking(fd, msvcrt.LK_UNLCK, 1)
    except OSError:
        pass
    os.close(fd)


def lock_held():
    fd = _try_lock()
    if fd is None:
        return True
    _unlock(fd)
    return False


def _pythonw():
    exe = Path(sys.executable)
    w = exe.with_name("pythonw.exe")
    return str(w if w.exists() else exe)


def _detach(args):
    flags = CREATE_NO_WINDOW | DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP if sys.platform == "win32" else 0
    kw = dict(creationflags=flags, close_fds=True, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
              stderr=subprocess.DEVNULL, cwd=str(Path(__file__).resolve().parent))
    if sys.platform != "win32":  # pragma: no cover
        kw.pop("creationflags")
        kw["start_new_session"] = True
    return subprocess.Popen(args, **kw)


def ensure_running():
    """Start the index's hidden sync process if it isn't running. Never blocks, never shows a window."""
    try:
        if is_off():
            return False
        if "pytest" in sys.modules and not _ALLOW_SPAWN_IN_TESTS:
            return False
        if lock_held():
            return False
        stamp = dots_dir() / "index_spawn.stamp"
        try:
            if time.time() - stamp.stat().st_mtime < SPAWN_EVERY:
                return False
        except OSError:
            pass
        stamp.parent.mkdir(parents=True, exist_ok=True)
        stamp.write_text(str(time.time()), encoding="utf-8")
        # Two hops: this starts 'spawn', which starts 'loop' and exits at once, so the loop isn't
        # a child of the job (stopping a job kills its whole process tree).
        _detach([_pythonw(), str(Path(__file__).resolve()), "spawn"])
        return True
    except Exception as e:
        _log(f"ensure_running: {e}")
        return False


def _quiet_stdio():
    if sys.stdout is None or sys.stderr is None or sys.executable.lower().endswith("pythonw.exe"):
        try:
            f = open(dots_dir() / "index.log", "a", encoding="utf-8", buffering=1)
            sys.stdout = sys.stderr = f
        except Exception:
            pass


def _sleep(stop, sec):
    return stop.wait(sec)


def _gmail_thread(address, stop):
    sync, backoff = GmailSync(address), 5
    db = connect()
    while not stop.is_set():
        t0 = time.time()
        try:
            r = sync.cycle(db)
            if r["new"] or r["bodies"]:
                _log(f"gmail {address}: +{r['new']} new, {r['bodies']} bodies in {time.time() - t0:.1f}s")
            backoff = 5
            _sleep(stop, max(5, GMAIL_EVERY - (time.time() - t0)))
        except Exception as e:
            _record_err(sync.source, e)
            sync.close()
            _sleep(stop, backoff)
            backoff = min(300, backoff * 3)
    sync.close()


def _outlook_thread(stop):
    last_mail = last_full = last_cal = 0.0
    while not stop.is_set():
        now = time.time()
        if now - last_mail >= OUTLOOK_EVERY:
            full = now - last_full >= RECONCILE_EVERY
            r = watchdog("outlook", lambda: outlook_mail_pass(full=full), timeout=PASS_TIMEOUT)
            last_mail = now
            if r is not None and full:
                last_full = now
        if now - last_cal >= CAL_EVERY:
            watchdog("outlook_cal", outlook_calendar_pass, timeout=PASS_TIMEOUT)
            last_cal = now
        _sleep(stop, 10)


def _canvas_thread(stop):
    while not stop.is_set():
        try:
            canvas_pass()
        except Exception as e:
            _record_err("canvas", e)
        _sleep(stop, CANVAS_EVERY)


def loop():
    _quiet_stdio()
    if is_off():
        return 0
    fd = _try_lock()
    if fd is None:
        return 0  # another loop has it
    try:
        s = _s()
        stop = threading.Event()
        threads = [threading.Thread(target=_gmail_thread, args=(a, stop), daemon=True, name=f"index-gmail-{a}")
                   for a in s.email_accounts()]
        try:
            if s.outlook_available():
                threads.append(threading.Thread(target=_outlook_thread, args=(stop,), daemon=True,
                                                name="index-outlook"))
        except Exception:
            pass
        threads.append(threading.Thread(target=_canvas_thread, args=(stop,), daemon=True, name="index-canvas"))
        for th in threads:
            th.start()
        me = Path(__file__).resolve()
        born = me.stat().st_mtime
        db = connect()
        try:
            rebuild_deadlines(db)
        except Exception as e:
            _log(f"rebuild deadlines: {e}")
        _log(f"loop started, pid {os.getpid()}")
        while True:
            _set_state(db, "loop", ok=True, cursor={"pid": os.getpid(), "started": born})
            try:
                maybe_vacuum(db)
            except Exception as e:
                _log(f"vacuum: {e}")
            if is_off():
                _log("index_off: stopping")
                break
            try:
                if me.stat().st_mtime != born:
                    _log("pd_index.py changed: stopping so the new code starts next time")
                    break
            except OSError:
                pass
            if stop.wait(15):
                break
        stop.set()
        return 0
    finally:
        _unlock(fd)


def once(s=None):
    """One full sync pass of every source, then exit. Returns per-source counts and seconds."""
    s = _s(s)
    out = {}
    db = connect()
    out["deadlines_rebuilt"] = rebuild_deadlines(db)
    for a in s.email_accounts():
        t0 = time.time()
        sync = GmailSync(a, s)
        for attempt in range(3):  # a backfill that times out resumes where it stopped
            try:
                r = sync.cycle(db, full=True)
                out[f"gmail:{a}"] = dict(r, sec=round(time.time() - t0, 1), tries=attempt + 1)
                break
            except Exception as e:
                _record_err(sync.source, e)
                out[f"gmail:{a}"] = {"error": str(e)[:200], "tries": attempt + 1}
                sync.close()
        sync.close()
    try:
        has_outlook = s.outlook_available()
    except Exception:
        has_outlook = False
    if has_outlook:
        t0 = time.time()
        r = watchdog("outlook", lambda: outlook_mail_pass(full=True, s=s, budget=600), timeout=900)
        out["outlook"] = dict(r or {"error": "see sync_state"}, sec=round(time.time() - t0, 1))
        t0 = time.time()
        r = watchdog("outlook_cal", lambda: outlook_calendar_pass(s), timeout=PASS_TIMEOUT)
        out["outlook_cal"] = {"events": r, "sec": round(time.time() - t0, 1)}
    t0 = time.time()
    try:
        out["canvas"] = dict(canvas_pass(s), sec=round(time.time() - t0, 1))
    except Exception as e:
        _record_err("canvas", e)
        out["canvas"] = {"error": str(e)[:200]}
    db.close()
    return out


def status():
    conn = _reader()
    if conn is None:
        return "no index yet"
    try:
        lines = []
        for r in conn.execute("SELECT source, last_ok_ts, last_err, cursor FROM sync_state ORDER BY source"):
            age = _ago(time.time() - r["last_ok_ts"]) if r["last_ok_ts"] else "never"
            lines.append(f"{r['source']}: ok {age}" + (f", last error: {r['last_err']}" if r["last_err"] else "")
                         + f" {r['cursor'] or ''}"[:200])
        for acct, n, b in conn.execute("SELECT account, COUNT(*), SUM(body IS NOT NULL) FROM msgs GROUP BY account"):
            lines.append(f"mail {acct}: {n} rows, {b} with text")
        lines.append("events: " + ", ".join(f"{src} {n}" for src, n in conn.execute(
            "SELECT source, COUNT(*) FROM events GROUP BY source")))
        lines.append(f"deadlines: {conn.execute('SELECT COUNT(*) FROM deadlines').fetchone()[0]}")
        lines.append(f"lock held: {lock_held()}")
        return "\n".join(lines)
    finally:
        conn.close()


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "status"
    if cmd == "spawn":
        if not is_off() and not lock_held():
            _detach([_pythonw(), str(Path(__file__).resolve()), "loop"])
        return 0
    if cmd == "loop":
        return loop()
    if cmd == "once":
        t0 = time.time()
        r = once()
        print(json.dumps(r, indent=1, default=str))
        print(f"total {time.time() - t0:.1f}s")
        print(status())
        return 0
    if cmd == "status":
        print(status())
        return 0
    print("usage: pd_index.py loop | once | status | spawn")
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
