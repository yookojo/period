"""Second opinion: a model from a different family than Dot's reads what Dot is about
to tell the owner, next to what actually happened, and says whether it holds up.

Two checks:
  check_claim(text, evidence)  - "done / sent / applied / added" against the tool results
  check_draft(draft, request)  - an email about to be OK'd against what they asked for

Calls are throttled across every job process (the checker models allow only a few
calls a minute), and a checker that can't be reached never blocks Dot: the verdict
is "unchecked" and Dot's own guards still apply."""
import io
import json
import os
import re
import sys
import time
from pathlib import Path


def _dir():
    mod = sys.modules.get("pd_dots")
    return Path(getattr(mod, "DOTS_DIR", None) or os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))


CHECKER_MODELS = [m for m in os.environ.get("PERIOD_DOT_CHECKER", "gpt-6.1-sol,gemini-3.8-flash").split(",") if m]
CALLS_PER_MIN = int(os.environ.get("PERIOD_DOT_CHECKER_RATE", "5"))
WAIT_FOR_SLOT_SEC = 45

CLAIM_RE = re.compile(
    r"\b(submitted|applied( to)?|went (in|through)|sent|emailed|going out|went out|uploaded|added|created|"
    r"booked|scheduled|shared|deleted|removed|signed (?:you )?up|(?:is|are|it'?s) (?:up|live|in)(?= on| at| your|[.!,]|$))\b", re.I)

CLAIM_PROMPT = """You are checking an assistant's message before it reaches its owner. The owner
has been burned by the assistant saying things were done when they weren't.

Message the assistant wants to send:
<<<
{text}
>>>

What its tools actually did and returned (newest last). "Earlier steps" are only
short descriptions from previous runs of the same job, without results:
<<<
{evidence}
>>>

RECORDS, looked up by a program just now from Dot's own application logs and the owner's
inbox. They are authoritative about what DOT's scripts did and what mail arrived. They do
not cover things the owner did himself (he may have applied somewhere on his own before).
<<<
{records}
>>>

Only judge claims that a concrete action WAS completed in the outside world: an email or
message sent, an application submitted, a file uploaded/shared/deleted, rows added to a
file, an account created, a payment made. Saying something "is going out", "is on its way",
"is sending now" or "is in" counts as claiming it was done.
- "wrong": such a claim is contradicted by a result or record (an error, "Not sent",
  "Nothing was sent", a failed or blocked status), or claims more than happened (says 5
  when results show 2), or claims such an action this run that has no trace at all in
  the results or records.
- "ok": those claims match the evidence, or the message makes no such claim. Do NOT flag
  explanations, plans, questions, what it is about to do, its own rules or limits ("I'm
  staying off your PC"), summaries of what it found, or statements about its own job
  status ("nothing left in this job") just because the evidence doesn't show them.
- "unsure": an action claim the evidence neither supports nor contradicts.

Reply with JSON only:
{{"verdict": "ok" | "wrong" | "unsure", "why": "<one short sentence>", "fixed": "<only if wrong: the same message rewritten to say only what really happened, same casual voice, lowercase ok>"}}"""

DRAFT_PROMPT = """You are checking an email an assistant drafted for its owner, before the owner is
asked to approve sending it.

What the owner asked for (their own words, newest last):
<<<
{request}
>>>

The draft:
<<<
{draft}
>>>

Decide if the draft does what the owner asked: right recipient, says what they wanted
said, doesn't add claims, promises or facts the owner never gave, isn't missing the
main point.
Reply with JSON only:
{{"verdict": "ok" | "wrong" | "unsure", "why": "<one short sentence the owner can read; if wrong, say exactly what's off>"}}"""


def _lock(timeout=10):
    lock = _dir() / "checker_calls.lock"
    end = time.time() + timeout
    while True:
        try:
            fd = os.open(str(lock), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.close(fd)
            return True
        except FileExistsError:
            try:
                if time.time() - lock.stat().st_mtime > 30:
                    lock.unlink()  # left behind by a killed process
                    continue
            except OSError:
                pass
            if time.time() > end:
                return False
            time.sleep(0.1)


def _unlock():
    try:
        (_dir() / "checker_calls.lock").unlink()
    except OSError:
        pass


def take_slot(wait=WAIT_FOR_SLOT_SEC, now=time.time, sleep=time.sleep):
    """One checker call allowed? Waits up to `wait` seconds for the per-minute budget."""
    _dir().mkdir(parents=True, exist_ok=True)
    calls_path = _dir() / "checker_calls.json"
    end = now() + wait
    while True:
        if _lock():
            try:
                try:
                    calls = json.loads(calls_path.read_text(encoding="utf-8"))
                except (OSError, ValueError):
                    calls = []
                t = now()
                calls = [c for c in calls if t - c < 60]
                if len(calls) < CALLS_PER_MIN:
                    calls.append(t)
                    calls_path.write_text(json.dumps(calls), encoding="utf-8")
                    return True
                free_in = 60 - (t - min(calls)) + 0.2
            finally:
                _unlock()
        else:
            free_in = 1
        if now() + free_in > end:
            return False
        sleep(min(free_in, max(0.1, end - now())))


def _ask(prompt, models=None):
    """Raw reply text from the first checker model that answers, plus which one."""
    import pd_dots
    s = pd_dots.sc()
    from rich.console import Console
    s._console_override.console = Console(file=io.StringIO())
    try:
        config = s.load_config()
        token = s.refresh_token(config, allow_browser_sync=False)
        if not token:
            return None, None
        for model in models or CHECKER_MODELS:
            if not take_slot():
                return None, None
            try:
                reply, _c, _p = s.call_api(prompt, model, s.MODEL_ENDPOINTS.get(model, s.DEFAULT_ENDPOINT), token, config)
            except Exception as e:
                print(f"[checker] {model}: {e}", file=sys.stderr)
                continue
            if isinstance(reply, str) and reply.strip() and not reply.lstrip().startswith(("[Error", "[bold red]")):
                return reply, model
            print(f"[checker] {model}: {str(reply)[:120]}", file=sys.stderr)
        return None, None
    finally:
        s._console_override.console = None


def _parse(reply):
    m = re.search(r"\{[\s\S]*\}", reply or "")
    try:
        data = json.loads(m.group(0)) if m else {}
    except ValueError:
        data = {}
    verdict = str(data.get("verdict") or "").lower()
    if verdict not in ("ok", "wrong", "unsure"):
        return None
    return {"verdict": verdict, "why": str(data.get("why") or "").strip(), "fixed": str(data.get("fixed") or "").strip()}


def _log(kind, dot_id, text, result):
    try:
        import pd_dots
        line = pd_dots.redact(json.dumps({"t": time.strftime("%Y-%m-%d %H:%M:%S"), "kind": kind, "dot": dot_id,
                                          "text": text[:400], **result}, ensure_ascii=False))
        with open(_dir() / "checker.log", "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def _run(kind, prompt, dot_id, text, ask=None):
    reply, model = (ask or _ask)(prompt)
    result = _parse(reply) if reply else None
    if result is None:
        result = {"verdict": "unchecked", "why": "checker unavailable" if not reply else "checker reply unreadable", "fixed": ""}
    result["model"] = model or ""
    _log(kind, dot_id, text, result)
    return result


def makes_claim(text):
    return bool(text and CLAIM_RE.search(text))


def check_claim(text, evidence, dot_id="", ask=None, records=None):
    ev = "\n".join(evidence[-60:]) if evidence else "(no tools were used)"
    rec = "\n".join(records or []) or "(nothing relevant on record)"
    return _run("claim", CLAIM_PROMPT.format(text=text[:3000], evidence=ev[-12000:], records=rec[-6000:]),
                dot_id, text, ask)


def check_draft(draft, request, dot_id="", ask=None):
    return _run("draft", DRAFT_PROMPT.format(draft=draft[:4000], request=request[-4000:] or "(not recorded)"),
                dot_id, draft, ask)
