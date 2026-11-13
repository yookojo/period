"""Dot's speed reflex: notice the small asks that keep coming back and take minutes, and script them.

Owner 2026-11-06: "how do I make it think like you, like 'there's so many [steps] and manually doing it is
inefficient, it should be a script'? ... if I tell it to check email, it realizes 4 min is absurd and makes a
script to speed it up?" "When are my interviews due?" took 8m 20s on 11-05 and the same ask came back three
more times in two days, each one 12-39 tool steps re-opening the same invite emails.

1. Measure. Every finished job adds a row to speed.jsonl (kind "job"): a task signature ("mail lookup:
   interview deadlines", "apply: amazon.jobs", "school: math 21"), seconds, model replies, tool steps, tool
   names and repeated identical calls (`record`, from Relay.finish). Older jobs are read from their folders
   (dot.json + log.txt) the same way (`history`).
2. Notice. `candidates` finds signatures that recur (3+ in 7 days or 2+ in 2 days) and are slow for what they
   are (median over 90 s, over 8 tool steps, or 3+ repeated identical calls), ranked by minutes a week they
   cost. A job's own "AUTOTOOL: ..." line (DOT_STYLE asks for one) counts as a vote for its signature.
3. Build. `tick` (from the daemon's queue sync, reloaded each time, at most every 2 h) starts one silent Dot
   job "autotool: <signature>" that writes a read-only plugin in autotools/<name>.py and runs
   `python pd_autotool.py bench <name>`. `bench` replays the recorded examples: kept only if it gives the same
   answer and is at least 2x faster; otherwise discarded and the signature isn't retried for 7 days. Every
   result goes in autotool_ledger.md. A kept plugin answers matching texts in pd_fast.answer (no model turn)
   and pre-answers matching jobs in pd_fast.prefetch_block.
4. Show. One short Discord line when a script is kept ("made 'interview deadlines' instant: 8 min -> 0.3 s"),
   nothing for discards.

Plugins never send, pay, submit or delete: READ_ONLY must be True or the plugin isn't loaded.
Off switch: <dots dir>/autotool_off. Never raises out of tick/record/fast_answer.
"""
import datetime
import importlib.util
import json
import os
import re
import statistics
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS_DIR = HERE / "autotools"
TICK_EVERY = 2 * 3600
RETRY_AFTER = 7 * 86400
FAST_SEC = 15            # what a scripted answer is allowed to cost; the rest of a run counts as waste
SLOW_MEDIAN = 90
SLOW_STEPS = 8
REPEATS = 3
MIN_SPEEDUP = 2.0
MIN_MATCH = 0.8          # share of the old answer's dated items the new one must also give, per example
BUILD_LABEL = "autotool: "


def dots_dir():
    return Path(os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))


def _state_path():
    return dots_dir() / "autotool.json"


def _load_state():
    try:
        st = json.loads(_state_path().read_text(encoding="utf-8"))
        return st if isinstance(st, dict) else {}
    except (OSError, ValueError):
        return {}


def _save_state(st):
    try:
        p = _state_path()
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".tmp")
        tmp.write_text(json.dumps(st, indent=1), encoding="utf-8")
        os.replace(tmp, p)
    except OSError:
        pass


def is_off():
    return (dots_dir() / "autotool_off").exists() or os.environ.get("PERIOD_AUTOTOOL", "").lower() in (
        "off", "0", "no")


def _fmt(sec):
    sec = float(sec or 0)
    if sec < 10:
        return f"{sec:.1f} s"
    if sec < 90:
        return f"{round(sec)} s"
    return f"{sec / 60:.1f} min"


# --- 1. measure -------------------------------------------------------------------------------------------------

_COURSE_RE = re.compile(r"\b(math|cs|Econ|mse|cme|econ|phys|physics|chem|engr|stats?)\s?(\d{2,3}[a-z]?)\b|"
                        r"\b(investment (?:science|project)|stock simulation)\b", re.I)
_COURSE_ALIAS = {"investment": "econ 101", "stock": "econ 101"}
_URL_RE = re.compile(r"https?://([^/\s)'\"<>]+)")
_HOST_DROP = re.compile(r"^(www|apply|careers|jobs|boards|job-boards|join|hire)\.")
RULES = [
    ("claude", re.compile(r"^claude\b|\bclaude (message|session|edit|efficiency)|\b(to|with|ask|tell|message|prompt "
                          r"for|prompt to) claude\b", re.I)),
    ("outreach", re.compile(r"\b(outreach|reach out|connection notes?|dms?)\b.{0,80}\brecruit|\brecruit\w*\b.{0,40}"
                            r"\b(outreach|reach out|linkedin)\b", re.I)),
    ("apply", re.compile(r"^\s*(?:the user wants to\s+)?apply\b|\bapply to\b.{0,120}https?://", re.I)),
    ("send", re.compile(r"\b(authori[sz]es|approved|explicitly requests)\b.{0,60}\b(send|sending|email|reply|"
                        r"outreach)\b|\bsend(ing)?\b.{0,40}\b(email|reply|apology)\b", re.I)),
    ("interviews", re.compile(r"\b(interviews?|assessments?|OAs?|hackerranks?|codesignal|codility|coding tests?)\b",
                              re.I)),
    ("brief", re.compile(r"\b(morning (prep|brief)|get my day ready|plan (out )?my day)\b", re.I)),
    ("course", _COURSE_RE),
    ("calendar", re.compile(r"\bcalendar\b|\bfree time\b|\bwhen am i free\b", re.I)),
    ("places", re.compile(r"\b(route|restaurants?|sushi|food|gas|gyms?|showers?|librar(y|ies)|nearby|near me|"
                          r"sightseeing|directions)\b", re.I)),
    ("alarm", re.compile(r"\balarms?\b", re.I)),
    ("mail", re.compile(r"\b(e-?mails?|mail|inbox|gmail|outlook)\b", re.I)),
]
_DUE_RE = re.compile(r"\b(due|deadlines?|upcoming|still need|need to (do|complete)|have to do|pending|current|"
                     r"check|status|what .{0,25}\bhave|when)\b", re.I)
_TOPIC_STOP = {"the", "a", "an", "my", "and", "of", "to", "for", "me", "it", "s", "on", "in", "up", "that", "send",
               "find", "check", "email", "mail", "user", "user's", "users", "what", "when"}


def _host(url_host):
    h = _HOST_DROP.sub("", url_host.lower().split(":")[0])
    parts = h.split(".")
    return ".".join(parts[-2:]) if len(parts) > 2 and parts[-1] in ("com", "org", "io", "net") else h


def _topic(label, n=3):
    words = [w for w in re.findall(r"[a-z0-9&]+", (label or "").lower()) if w not in _TOPIC_STOP]
    return " ".join(words[:n]) or "misc"


def signature(label="", goal="", tools=(), kind="task"):
    """A job -> its normalised intent ("mail lookup: interview deadlines"), or "" for jobs that aren't one ask
    (the application lanes, the autotool builds themselves, chats)."""
    label, goal = str(label or ""), str(goal or "")
    if kind in ("chat", "reminder", "watch") or label.startswith(("Dot lane", BUILD_LABEL)):
        return ""
    if kind == "brief":
        return "brief: morning prep"
    # The label (a few words the quick brain picked) says what the ask is; the goal's opening decides only when
    # the label doesn't, or only says "mail" (goals mention interviews, Claude or calendars in passing).
    by_label = _rule_sig(label, label, goal)
    if by_label and not by_label.startswith("mail lookup: "):
        return by_label
    by_goal = _rule_sig(goal[:250], label, goal)
    if by_goal and not by_goal.startswith("mail lookup: "):
        return by_goal
    if by_label or by_goal:
        return by_label or by_goal
    tools = set(tools or ())
    if tools and tools <= {"mail_search", "mail_read"}:
        return f"mail lookup: {_topic(label)}"
    return f"task: {_topic(label)}"


def _rule_sig(text, label, goal):
    for name, rx in RULES:
        m = rx.search(text or "")
        if not m:
            continue
        if name == "claude":
            return "pc: talk to claude"
        if name == "outreach":
            return "send: recruiter outreach"
        if name == "apply":
            hosts = _URL_RE.findall(goal)
            return f"apply: {_host(hosts[0])}" if hosts else f"apply: {_topic(label, 2)}"
        if name == "send":
            return "send: email"
        if name == "interviews":
            if text is label or _DUE_RE.search(text[:200]):
                return "mail lookup: interview deadlines"
            continue
        if name == "brief":
            return "brief: morning prep"
        if name == "course":
            if m.group(3):
                return f"school: {_COURSE_ALIAS[m.group(3).split()[0].lower()]}"
            return f"school: {m.group(1).lower().replace('mse', 'Econ')} {m.group(2).lower()}"
        if name == "calendar":
            return "calendar: free time" if re.search(r"free time|when am i free|availab", text, re.I) \
                else "calendar: add or update"
        if name == "places":
            return "places: local look-up"
        if name == "alarm":
            return "pc: alarm"
        if name == "mail":
            return f"mail lookup: {_topic(label)}"
    return ""


_DUR_RE = re.compile(r"^[✓•■✗⚠] [A-Z][A-Z ]+ · (?:(\d+)h )?(?:(\d+)m )?(\d+)s", re.M)
_STEP_RE = re.compile(r"^  (\S[^\n]*)\n  ⎿  ([^\n]*)", re.M)
_RESULT_TOOL = [
    (re.compile(r"^Found \d+ emails?|^No emails?", re.I), "mail_search"),
    (re.compile(r"^\d+ items\b", re.I), "calendar_list"),
    (re.compile(r"^exit -?\d+", re.I), "run_command"),
    (re.compile(r"^Found \d+ results", re.I), "web_search"),
    (re.compile(r"^Read .*KB|characters$", re.I), "web_fetch"),
    (re.compile(r"canvas", re.I), "canvas"),
    (re.compile(r"gradescope", re.I), "gradescope"),
    (re.compile(r"^Opened|^tab \d+|^Now on", re.I), "browser"),
    (re.compile(r"px, uploaded|^Showing it", re.I), "screenshot"),
]


def log_stats(log_text):
    """A job's log.txt -> (seconds over its runs, tool steps, {tool kind: n}, repeated identical calls)."""
    txt = log_text or ""
    sec = sum(int(h or 0) * 3600 + int(m or 0) * 60 + int(s) for h, m, s in _DUR_RE.findall(txt))
    tools, seen, repeats = {}, {}, 0
    for desc, result in _STEP_RE.findall(txt):
        kind = next((k for rx, k in _RESULT_TOOL if rx.search(result.strip())), "")
        if not kind:
            kind = "mail_read" if re.search(r"\b(e-?mail|invite|reply|letter|thread)\b", desc, re.I) else "other"
        tools[kind] = tools.get(kind, 0) + 1
        key = desc.strip().lower()
        seen[key] = seen.get(key, 0) + 1
        if seen[key] > 1:
            repeats += 1
    return sec, sum(tools.values()), tools, repeats


def _first_ask(folder, d=None):
    """What they actually texted: the last "them:" line of the job's context (the text that started it),
    else the goal."""
    if d is None:
        try:
            d = json.loads((Path(folder) / "dot.json").read_text(encoding="utf-8", errors="replace"))
        except (OSError, ValueError):
            d = {}
    said = [ln[6:].strip() for ln in str(d.get("context") or "").splitlines() if ln.startswith("them: ")]
    return said[-1] if said else str(d.get("goal") or "").strip()


_RUN_SPLIT = re.compile(r"^=== .* · run \d+\s*$", re.M)


def _answer_of(folder):
    """What the job answered: each run's closing prose in log.txt (after its last tool step), joined."""
    try:
        log = (Path(folder) / "log.txt").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    out = []
    for run in _RUN_SPLIT.split(log)[1:]:
        lines = run.splitlines()
        last_step = max((i for i, ln in enumerate(lines) if ln.startswith("  ⎿")), default=-1)
        while last_step >= 0 and last_step + 1 < len(lines) and re.match(r"^ \S", lines[last_step + 1]):
            last_step += 1  # a long tool result wraps onto lines with one leading space
        tail, note = [], False
        for ln in lines[last_step + 1:]:
            if note or ln.startswith("["):  # Dot's own [notes] (a quoted second-opinion check) can span lines
                note = not ln.rstrip().endswith("]")
                continue
            if ln.strip() and not re.match(r"^(━━|[✓■✗⚠] [A-Z]|• STOPPED|DONE\b|===|  Pausing|"
                                           r"  Something didn't work)", ln):
                tail.append(ln)
        if tail:
            out.append("\n".join(tail))
    return RUN_SEP.join(out)


RUN_SEP = "\n----\n"  # between runs' answers (a plugin's same() can tell a repeat from a second item)


def job_row(folder):
    """One job folder -> a measurement row, or None."""
    folder = Path(folder)
    try:
        d = json.loads((folder / "dot.json").read_text(encoding="utf-8", errors="replace"))
    except (OSError, ValueError):
        return None
    if not isinstance(d, dict):
        return None
    sig = signature(d.get("label") or d.get("name"), d.get("goal"), kind=d.get("kind", "task"))
    if not sig:
        return None
    try:
        log = (folder / "log.txt").read_text(encoding="utf-8", errors="replace")
    except OSError:
        log = ""
    sec, steps, tools, repeats = log_stats(log)
    est = False
    if not sec:  # cut off without a DONE line: when it last spoke, capped (a job left asleep isn't working)
        start = float(d.get("started") or d.get("created") or 0)
        end = float(d.get("told_at") or d.get("updated") or 0)
        sec, est = (min(max(0.0, end - start), 1800.0), True) if start and end else (0.0, True)
    if tools and set(tools) <= {"mail_search", "mail_read", "other"} and sig.startswith("task: "):
        sig = signature(d.get("label") or d.get("name"), d.get("goal"), tools=set(tools) - {"other"})
    return {"kind": "job", "job": d.get("id") or folder.name, "t": float(d.get("created") or 0), "sig": sig,
            "label": d.get("label") or d.get("name") or "", "sec": round(sec), "est": est,
            "replies": int(d.get("sends") or 0), "steps": steps, "tools": tools, "repeats": repeats,
            "status": d.get("status", ""), "source": d.get("source", "")}


def record(dot, relay):
    """End of a job run (Relay.finish): its measurement row into speed.jsonl. Never raises."""
    try:
        if relay is None or getattr(dot, "kind", "") not in ("task", "job", "brief"):
            return None
        sig = signature(getattr(dot, "label", "") or getattr(dot, "name", ""), getattr(dot, "goal", ""),
                        tools=set(getattr(relay, "tool_counts", {}) or {}), kind=getattr(dot, "kind", "task"))
        if not sig:
            return None
        counts = dict(getattr(relay, "tool_counts", {}) or {})
        row = {"kind": "job", "job": getattr(dot, "id", ""), "t": round(time.time()), "sig": sig,
               "label": str(getattr(dot, "label", "") or "")[:60],
               "sec": round(max(0.0, time.time() - float(getattr(relay, "began", time.time())))),
               "replies": int(getattr(relay, "turns", 0) or 0), "steps": sum(counts.values()), "tools": counts,
               "repeats": int(getattr(relay, "repeat_calls", 0) or 0), "run": int(getattr(dot, "runs", 0) or 0)}
        p = dots_dir() / "speed.jsonl"
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "a", encoding="utf-8") as f:
            f.write(json.dumps(row) + "\n")
        for ask in (getattr(relay, "tags", {}) or {}).get("autotool", []) or []:
            note_ask(dot, ask, sig)
        return row
    except Exception as e:
        print(f"[autotool] record: {e}", file=sys.stderr)
        return None


def note_ask(dot, line, sig=""):
    """A job's own "AUTOTOOL: <what to script and why>" line: a vote for its signature."""
    try:
        sig = sig or signature(getattr(dot, "label", ""), getattr(dot, "goal", ""), kind=getattr(dot, "kind", "task"))
        p = dots_dir() / "autotool_asks.jsonl"
        with open(p, "a", encoding="utf-8") as f:
            f.write(json.dumps({"t": round(time.time()), "job": getattr(dot, "id", ""), "sig": sig,
                                "ask": str(line or "")[:300]}) + "\n")
    except Exception as e:
        print(f"[autotool] ask: {e}", file=sys.stderr)


def _jsonl(path):
    try:
        lines = Path(path).read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []
    out = []
    for line in lines:
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if isinstance(r, dict):
            out.append(r)
    return out


def history(days=7, now=None):
    """Measurement rows for the jobs of the last `days`: speed.jsonl's own rows (real tool names) where a job has
    them, its folder (log.txt) otherwise. A job with several runs counts once (its first run's ask)."""
    now = time.time() if now is None else now
    since = now - days * 86400
    rows = {}
    base = dots_dir()
    for f in list(base.glob("*/dot.json")) + list(base.glob("archive/*/dot.json")):
        try:
            created = float(json.loads(f.read_text(encoding="utf-8", errors="replace")).get("created") or 0)
        except (OSError, ValueError, AttributeError):
            continue
        if not (since <= created <= now):
            continue
        r = job_row(f.parent)
        if r:
            rows[r["job"]] = r
    for r in _jsonl(base / "speed.jsonl"):
        if r.get("kind") != "job" or not (since <= float(r.get("t") or 0) <= now) or not r.get("sig"):
            continue
        old = rows.get(r.get("job"))
        if old is None or int(r.get("run") or 1) <= 1:
            rows[r["job"]] = dict(old or {}, **r)
    return sorted(rows.values(), key=lambda r: r["t"])


# --- 2. notice --------------------------------------------------------------------------------------------------

NOT_BUILDABLE = ("send:", "apply:", "pc: talk to claude")


def buildable(sig):
    """Sends and applications go through Dot's gates by design (a script would only skip the checks), and a
    Claude hand-off's time is Claude doing the work: none of them get a read-only fast path."""
    return not str(sig or "").startswith(NOT_BUILDABLE)


def candidates(days=7, now=None, rows=None):
    """Signatures that recur and are slow for what they are, most minutes wasted per week first."""
    now = time.time() if now is None else now
    rows = history(days, now) if rows is None else rows
    asks = {}
    for a in _jsonl(dots_dir() / "autotool_asks.jsonl"):
        if float(a.get("t") or 0) >= now - days * 86400 and a.get("sig"):
            asks.setdefault(a["sig"], []).append(a.get("ask", ""))
    groups = {}
    for r in rows:
        if r.get("sig") and r.get("sec", 0) > 0:
            groups.setdefault(r["sig"], []).append(r)
    out = []
    for sig, rs in groups.items():
        recent = [r for r in rs if r["t"] >= now - 2 * 86400]
        voted = bool(asks.get(sig))
        recurs = len(rs) >= 3 or len(recent) >= 2 or (voted and len(rs) >= 2)
        med = statistics.median(r["sec"] for r in rs)
        med_steps = statistics.median(r.get("steps", 0) for r in rs)
        repeats = max(r.get("repeats", 0) for r in rs)
        slow = med > SLOW_MEDIAN or med_steps > SLOW_STEPS or repeats >= REPEATS
        if not (recurs and slow):
            continue
        wasted = sum(max(0, r["sec"] - FAST_SEC) for r in rs) / 60 * 7 / days
        why = [w for w, on in ((f"median {_fmt(med)}", med > SLOW_MEDIAN),
                               (f"{med_steps:g} tool steps", med_steps > SLOW_STEPS),
                               (f"{repeats} repeated calls", repeats >= REPEATS)) if on]
        out.append({"sig": sig, "buildable": buildable(sig), "n": len(rs), "n_2d": len(recent), "median_s": round(med),
                    "median_steps": med_steps, "max_repeats": repeats, "total_s": sum(r["sec"] for r in rs),
                    "wasted_min_week": round(wasted, 1), "why": why, "asks": asks.get(sig, [])[-3:],
                    "jobs": [r["job"] for r in rs], "labels": list(dict.fromkeys(r.get("label", "") for r in rs))})
    out.sort(key=lambda c: -c["wasted_min_week"])
    return out


def report(days=7, top=5, now=None):
    cands = candidates(days, now)
    lines = [f"Speed reflex: recurring slow asks, last {days} days (most minutes a week first)"]
    for i, c in enumerate(cands[:top], 1):
        lines.append(f"{i}. {c['sig']}: {c['n']}x ({c['n_2d']} in 2 days), median {_fmt(c['median_s'])}, "
                     f"{c['median_steps']:g} tool steps, {c['wasted_min_week']} min/week; {', '.join(c['why'])}; "
                     f"jobs {', '.join(c['jobs'])}" + ("" if c["buildable"] else " [not scripted: a send, an application or a Claude hand-off]"))
    return "\n".join(lines if cands else lines + ["- none"])


# --- 3. build: plugins, the bench and the ledger -----------------------------------------------------------------

PLUGIN_CONTRACT = (
    "NAME (str), SIGNATURE (the candidate's signature), READ_ONLY = True, matches(text) -> bool (the whole text is "
    "just this ask), about(goal) -> bool (a job goal that includes it), run(text, now=None, fresh_only=True) -> "
    "answer text or None (None = let the normal way answer), same(old_answer, new_answer, now=None) -> "
    "{'score': 0..1, 'matched': [...], 'missed': [...]}")


def load_plugin(name):
    path = TOOLS_DIR / f"{name}.py"
    if not re.fullmatch(r"[a-z0-9_]+", name or "") or not path.is_file():
        return None
    spec = importlib.util.spec_from_file_location(f"autotools_{name}", path)
    mod = importlib.util.module_from_spec(spec)
    if str(HERE) not in sys.path:
        sys.path.insert(0, str(HERE))
    spec.loader.exec_module(mod)
    if getattr(mod, "READ_ONLY", False) is not True:
        return None
    return mod


def examples(sig, days=14, now=None, plugin=None):
    """Recorded jobs for a signature, with what they were asked, what they answered and how long it took."""
    now = time.time() if now is None else now
    out = []
    for r in history(days, now):
        if r["sig"] != sig or r.get("est"):
            continue
        folder = dots_dir() / r["job"]
        if not folder.exists():
            folder = dots_dir() / "archive" / r["job"]
        ask, ans = _first_ask(folder), _answer_of(folder)
        if not ask or not ans:
            continue
        if plugin is not None and not (plugin.matches(ask) or plugin.about(ask)):
            continue
        out.append({"job": r["job"], "t": r["t"], "ask": ask, "old": ans, "old_s": r["sec"], "label": r["label"]})
    return out


def bench(name, days=14, now=None, announce=True, write=True):
    """Replay a plugin on its signature's recorded examples (at each one's own time, so mail that came later
    doesn't count). Kept if every example matches (score >= MIN_MATCH) and it's >= 2x faster; else discarded,
    and its signature waits RETRY_AFTER before another try. -> result dict (also in the ledger)."""
    now = time.time() if now is None else now
    try:
        plugin = load_plugin(name)
    except Exception as e:
        plugin, err = None, f"didn't load: {e}"
    else:
        err = "" if plugin else "no read-only plugin by that name"
    sig = getattr(plugin, "SIGNATURE", name)
    res = {"name": name, "sig": sig, "t": round(now), "examples": [], "kept": False}
    exs = examples(sig, days, now, plugin) if plugin else []
    if plugin and not exs:
        err = "no recorded examples to check it against"
    for ex in exs:
        t0 = time.perf_counter()
        try:
            new = plugin.run(ex["ask"], now=ex["t"], fresh_only=False)
        except Exception as e:
            new = None
            ex["error"] = str(e)[:200]
        new_s = time.perf_counter() - t0
        cmp = plugin.same(ex["old"], new or "", now=ex["t"]) if new else {"score": 0.0, "matched": [], "missed": []}
        res["examples"].append({"job": ex["job"], "ask": ex["ask"][:120], "old_s": ex["old_s"], "new_s": round(new_s, 2),
                                "score": cmp["score"], "matched": len(cmp["matched"]), "missed": cmp["missed"][:5],
                                "answered": bool(new), **({"error": ex["error"]} if "error" in ex else {})})
    ok = [e for e in res["examples"] if e["answered"] and e["score"] >= MIN_MATCH]
    old_s = sum(e["old_s"] for e in res["examples"])
    new_s = sum(e["new_s"] for e in res["examples"]) or 0.01
    res.update(old_s=old_s, new_s=round(new_s, 2), speedup=round(old_s / new_s, 1) if res["examples"] else 0)
    if err:
        res["why"] = err
    elif len(ok) < len(res["examples"]):
        bad = [e for e in res["examples"] if e not in ok]
        res["why"] = f"{len(bad)} of {len(res['examples'])} examples didn't match (" + "; ".join(
            f"{e['job']}: score {e['score']}" + (f", missed {e['missed'][0][:60]!r}" if e["missed"] else "")
            for e in bad[:3]) + ")"
    elif res["speedup"] < MIN_SPEEDUP:
        res["why"] = f"only {res['speedup']}x faster"
    else:
        res["kept"] = True
        res["why"] = f"{len(ok)}/{len(ok)} examples match, {res['speedup']}x faster"
    if write:
        _settle(res, announce)
    return res


def _settle(res, announce=True):
    st = _load_state()
    if res["kept"]:
        n = len(res["examples"])
        st.setdefault("kept", {})[res["name"]] = {"sig": res["sig"], "t": res["t"], "old_s": res["old_s"] / max(1, n),
                                                  "new_s": res["new_s"] / max(1, n)}
        if announce:
            st.setdefault("announce", []).append(
                f"made '{res['sig'].split(': ', 1)[-1]}' instant: {_fmt(res['old_s'] / max(1, n))} -> "
                f"{_fmt(res['new_s'] / max(1, n))}")
    else:
        st.setdefault("cooldown", {})[res["sig"]] = res["t"] + RETRY_AFTER
        st.get("kept", {}).pop(res["name"], None)
    _save_state(st)
    ledger(res)


def ledger(res):
    """One entry per build result in <dots dir>/autotool_ledger.md."""
    try:
        p = dots_dir() / "autotool_ledger.md"
        new = not p.exists()
        when = datetime.datetime.fromtimestamp(res.get("t") or time.time()).strftime("%Y-%m-%d %H:%M")
        lines = (["# Dot's speed reflex: scripts built, kept and discarded\n"] if new else []) + [
            f"\n## {when} · {res.get('sig')} · {'KEPT' if res.get('kept') else 'discarded'} ({res.get('name')})",
            f"- {res.get('why', '')}"]
        if res.get("examples"):
            lines.append(f"- old {_fmt(res['old_s'])} total -> new {_fmt(res['new_s'])} total "
                         f"({res.get('speedup')}x) over {len(res['examples'])} recorded examples")
            lines += [f"  - {e['job']} {e['ask'][:60]!r}: {_fmt(e['old_s'])} -> {_fmt(e['new_s'])}, match "
                      f"{e['score']}" + (f", missed {e['missed'][:2]}" if e["missed"] else "")
                      for e in res["examples"]]
        if not res.get("kept"):
            lines.append(f"- not retried before {datetime.datetime.fromtimestamp(res.get('t', time.time()) + RETRY_AFTER):%Y-%m-%d}")
        with open(p, "a", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
    except Exception as e:
        print(f"[autotool] ledger: {e}", file=sys.stderr)


# --- the kept plugins at work (pd_fast) ------------------------------------------------------------------------

_loaded = {}


def kept_plugins():
    """The kept plugins, loaded (cached by file time, so a rebuilt one is picked up)."""
    if is_off():
        return []
    out = []
    for name in sorted((_load_state().get("kept") or {})):
        path = TOOLS_DIR / f"{name}.py"
        try:
            mt = path.stat().st_mtime
            hit = _loaded.get(name)
            if not hit or hit[0] != mt:
                _loaded[name] = (mt, load_plugin(name))
            if _loaded[name][1] is not None:
                out.append(_loaded[name][1])
        except Exception as e:
            print(f"[autotool] {name}: {e}", file=sys.stderr)
    return out


def fast_answer(text):
    """(answer, plugin name) when a kept plugin answers this whole text, else (None, "")."""
    try:
        for p in kept_plugins():
            if p.matches(text):
                out = p.run(text)
                if out:
                    return out, p.NAME
    except Exception as e:
        print(f"[autotool] fast: {e}", file=sys.stderr)
    return None, ""


def prefetch(goal):
    """[(name, answer)] from kept plugins whose ask is part of this job's goal (a job's first look-ups)."""
    out = []
    try:
        for p in kept_plugins():
            if p.about(goal or ""):
                ans = p.run(goal or "")
                if ans:
                    out.append((p.NAME, ans))
    except Exception as e:
        print(f"[autotool] prefetch: {e}", file=sys.stderr)
    return out


# --- the reflex on a timer (from the daemon's queue sync) -------------------------------------------------------

def build_goal(c):
    name = re.sub(r"[^a-z0-9]+", "_", c["sig"].split(": ", 1)[-1].lower()).strip("_")[:40] or "fast_path"
    exs = examples(c["sig"])[:4]
    shown = "\n".join(f"- {e['job']} ({_fmt(e['old_s'])}): {e['ask'][:160]!r}" for e in exs) or "- (see the job ids)"
    return name, (
        f"{BUILD_LABEL}{c['sig']}. Dot's speed reflex: this kind of ask came {c['n']} times in the last 7 days "
        f"(median {_fmt(c['median_s'])}, {c['median_steps']:g} tool steps; {', '.join(c['why'])}), about "
        f"{c['wasted_min_week']} min a week. Jobs: {', '.join(c['jobs'])}. What they asked:\n{shown}\n"
        + (f"Jobs' own notes: {' | '.join(c['asks'])}\n" if c["asks"] else "")
        + f"Make it a deterministic script so it answers in seconds. In {HERE} (Windows, run_command):\n"
        f"1. Read pd_autotool.py and autotools/interview_deadlines.py (a kept example). Write "
        f"autotools/{name}.py with this contract: {PLUGIN_CONTRACT}. Read the answer from local data only: "
        "Dot's index ~/.period_dots/index.db through pd_index (mail, calendar, Canvas, deadlines tables, opened "
        "read-only), or other local files. It must never send, pay, submit, delete or change anything.\n"
        f"2. Write autotools/test_{name}.py (pytest) covering matches/about/run/same and run it.\n"
        f"3. Run `python pd_autotool.py bench {name}`. It replays the recorded examples and keeps the script only if "
        "every answer matches and it's at least 2x faster; otherwise it's discarded and logged. Fix and re-run at "
        "most twice.\n"
        "If it can only be done on the Dot PC, write the script under ~/tools/_wip_autotool/ with vm_claude, test "
        "it there, install it with an atomic mv, run `bash ~/tools/self_audit.sh`, and log the result with "
        f"`python pd_autotool.py note \"{c['sig']}\" \"<kept|discarded>: <why>\"`.\n"
        "Don't edit pd_fast.py, pd_dots.py or period.py: a kept plugin is picked up on its own. Finish with "
        "one line: kept or discarded, and why.")


def tick():
    """At most every 2 h: say what got kept, then start one build for the top candidate. Never raises."""
    try:
        _tick()
    except Exception as e:
        print(f"[autotool] {e}", file=sys.stderr)


def _tick(now=None):
    now = time.time() if now is None else now
    if is_off():
        return None
    import pd_dots as d
    st = _load_state()
    if st.get("announce"):
        dm = d.discord.dm() if getattr(d, "discord", None) and d.discord.connected() else None
        if dm:
            for line in st["announce"][:3]:
                d.say_to("discord:" + dm, line)
            st["announce"] = []
            _save_state(st)
    if now - float(st.get("last_tick") or 0) < TICK_EVERY:
        return None
    st["last_tick"] = now
    _save_state(st)
    if any((t.label or "").startswith(BUILD_LABEL) for t in d.active_tasks(sleeping=True)):
        return None  # one build at a time
    kept_sigs = {k.get("sig") for k in (st.get("kept") or {}).values()}
    cool = st.get("cooldown") or {}
    for c in candidates(7, now):
        if not c["buildable"] or c["sig"] in kept_sigs or float(cool.get(c["sig"]) or 0) > now:
            continue
        name, goal = build_goal(c)
        job = d.new_dot(goal, computer="pc", source="autotool", reply_to="local:autotool", kind="task")
        d._update(job, label=f"{BUILD_LABEL}{c['sig']}"[:80])
        st = _load_state()
        st["building"] = {"job": job.id, "sig": c["sig"], "name": name, "t": now}
        st.setdefault("cooldown", {})[c["sig"]] = now + RETRY_AFTER  # bench clears it if kept
        _save_state(st)
        print(f"[autotool] building {name} for {c['sig']!r} in {job.id}", file=sys.stderr)
        return job.id
    return None


def note(sig, text):
    """A result logged by hand or by a VM build (no bench): ledger only."""
    kept = text.lower().startswith("kept")
    ledger({"sig": sig, "name": "vm", "kept": kept, "why": text, "t": time.time()})


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    cmd = argv[0] if argv else "report"
    if cmd == "report":
        print(report(int(argv[1]) if len(argv) > 1 else 7))
    elif cmd == "json":
        print(json.dumps(candidates(int(argv[1]) if len(argv) > 1 else 7), indent=1))
    elif cmd == "bench" and len(argv) > 1:
        res = bench(argv[1], announce="--quiet" not in argv, write="--dry" not in argv)
        print(json.dumps(res, indent=1))
        return 0 if res["kept"] else 1
    elif cmd == "note" and len(argv) > 2:
        note(argv[1], argv[2])
    else:
        print("usage: pd_autotool.py report [days] | json [days] | bench <name> [--dry] [--quiet] | note <sig> <text>")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
