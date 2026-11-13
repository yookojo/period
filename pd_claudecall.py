"""Claude Code as a Dot job's model (2026-11-05, "let it use my claude runs").

A Dot job still runs Period's own agent loop: the loop builds every prompt, parses
every tool block, and runs each tool through the same gates as before (pd_policy's money
and safety gate, CONFIRM_TOOLS, the Relay hooks, "QUESTION: send it?" approval). Only the
step that turns a prompt into a reply changes: inside the job process, s.call_api is
swapped for a wrapper that asks the owner's Claude plan through `claude -p` instead of
the remote backend's gateway.

Claude gets no tools of its own (--tools "" --strict-mcp-config --setting-sources "",
--permission-mode dontAsk), so all it can do is write text. Any action is still a tool
block that Dot's loop parses and gates. It never gets --dangerously-skip-permissions,
--bare or --allowedTools.

Why: a remote backend opus step takes a median 10-12 s (5.8 s to the first word), with a
6-a-minute pacing limit and 2-at-once slots shared with the application lanes. Lean
`claude -p` gives a first word in about 1.5 s and has no per-minute limit.

Falls back to the remote backend on its own: any failure (no output, error, empty reply, timeout,
the plan's usage limit) hands the same step to the remote backend. Mid-conversation, the remote backend gets a
replay of the task so far, so the job carries on instead of starting over.

Off switches: env PERIOD_DOT_CLAUDE=off, the file ~/.period_dots/claude_engine_off,
or Period's remote-only setting. Lanes, autonomous jobs, watches and reminders
always stay on the remote backend.
"""
import json
import os
import queue
import re
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from pathlib import Path

DOTS_DIR = Path(os.environ.get("PERIOD_DOTS_DIR", Path.home() / ".period_dots"))
ENGINE_DIR = DOTS_DIR / "claude_engine"       # claude's cwd (so --resume finds sessions) + <sid>.jsonl turns
LOG = DOTS_DIR / "claude_engine.jsonl"        # one row per call: timing, ok, why it fell back
BACKOFF = DOTS_DIR / "claude_engine_backoff.json"
OFF_FILE = DOTS_DIR / "claude_engine_off"

MODELS = {"claude-opus-5-5": "claude-opus-5-5", "claude-sonnet-5-5": "claude-sonnet-5-5"}
# Claude-only installs (no remote backend account, e.g. a friend's Mac): every model Period names maps to one
# their own Claude plan has. the remote backend's fast/other models (gpt-*, Kimi, gemini...) become the fast Claude model.
ONLY_MODELS = {**MODELS, "claude-haiku-5-5": "claude-haiku-5-5"}
ONLY_FAST_MODEL = os.environ.get("PERIOD_CLAUDE_FAST_MODEL", "claude-sonnet-5-5")
FIRST_EVENT_TIMEOUT = 60
TOTAL_TIMEOUT = 300
IDLE_TIMEOUT = 120      # started, then nothing at all for this long: stalled
REPLAY_CHARS = 60000
HIGH_USE = 0.9          # five-hour plan use at or above this: rest Claude for BUSY_REST_SEC
BUSY_REST_SEC = 1200
LIMIT_REST_SEC = 1800

SYS_PROMPT = ("You are the reasoning model inside Period/Dot. You have no tools of your own. The user "
              "messages contain your full instructions and tool format: act only by writing tool blocks exactly "
              "as those instructions describe; the tool results come back in the next message. Follow every rule "
              "in them, including asking QUESTION: before sending anything.")

# Same as pd_vmclaude._LIMIT_RE: the plan's usage limit, in Claude Code's own words.
_LIMIT_RE = re.compile(r"usage limit|limit (reached|exceeded)|out of (usage|credits)|hit your limit", re.I)
_LOGIN_RE = re.compile(r"not logged in|please run /login|invalid api key|oauth token (has )?expired|"
                       r"authentication_error|\b401\b", re.I)
LOGIN_REST_SEC = 600
_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
_OFF_WORDS = ("off", "0", "no", "false")
_log_lock = threading.Lock()


def cli():
    """The claude command as a list. PERIOD_DOT_CLAUDE_CLI may be a path or a JSON list."""
    raw = os.environ.get("PERIOD_DOT_CLAUDE_CLI", "").strip()
    if raw.startswith("["):
        try:
            got = [str(x) for x in json.loads(raw)]
            if got:
                return got
        except Exception:
            pass
    if raw:
        return [raw]
    default = Path.home() / ".local" / "bin" / ("claude.exe" if sys.platform == "win32" else "claude")
    if sys.platform != "win32" and not default.exists():
        # Mac/Linux: Homebrew (/opt/homebrew/bin) or npm installs; the login job's PATH may not have them.
        import shutil
        for cand in (shutil.which("claude"), "/opt/homebrew/bin/claude", "/usr/local/bin/claude"):
            if cand and Path(cand).exists():
                return [str(cand)]
    return [str(default)]


def _now():
    return time.time()


def _read_json(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception:
        return {}


def backoff_left():
    """Seconds Claude is resting for (the plan's limit, or close to it); 0 when it's free."""
    try:
        until = float(_read_json(BACKOFF).get("until") or 0)
    except Exception:
        return 0
    return max(0, until - _now())


def _set_backoff(seconds, why):
    try:
        BACKOFF.parent.mkdir(parents=True, exist_ok=True)
        BACKOFF.write_text(json.dumps({"until": _now() + seconds, "why": str(why)[:300],
                                       "set": time.strftime("%Y-%m-%d %H:%M:%S")}), encoding="utf-8")
    except Exception:
        pass


def _log(row):
    row = {"ts": time.strftime("%Y-%m-%d %H:%M:%S"), **row}
    try:
        with _log_lock:
            LOG.parent.mkdir(parents=True, exist_ok=True)
            with open(LOG, "a", encoding="utf-8") as f:
                f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except Exception:
        pass


def _under_tests():
    # A test that runs a real job must never reach the owner's real Claude plan. A real job is
    # always "pd_dots.py run <id>", so a library that happens to import unittest can't turn it off.
    if os.environ.get("PERIOD_DOT_CLAUDE_CLI"):
        return False
    if sys.argv and Path(sys.argv[0] or "").name.lower().startswith("pd_dots"):
        return False
    return "unittest" in sys.modules or "pytest" in sys.modules


def enabled(dot, s, is_lane=None, autonomous=None):
    """(True, "") when this job may think with Claude, else (False, why)."""
    if os.environ.get("PERIOD_DOT_CLAUDE", "").strip().lower() in _OFF_WORDS:
        return False, "turned off (PERIOD_DOT_CLAUDE)"
    if OFF_FILE.exists():
        return False, "turned off (claude_engine_off)"
    if _under_tests():
        return False, "test run"
    if not Path(cli()[0]).exists():
        return False, "Claude Code isn't installed"
    try:
        if getattr(s, "remote_only", None) and s.remote_only():
            return False, "remote-only mode"
    except Exception:
        pass
    if backoff_left() > 0:
        return False, f"Claude plan resting ({_read_json(BACKOFF).get('why') or 'limit'})"
    if dot is not None:
        label = str(getattr(dot, "label", "") or "")
        try:
            lane = is_lane(dot) if is_lane else label.startswith("Dot lane")
        except Exception:
            lane = label.startswith("Dot lane")
        if lane or label.startswith("Dot lane"):
            return False, "application lane"
        try:
            auto = autonomous(dot) if autonomous else bool(getattr(dot, "autonomous", False))
        except Exception:
            auto = False
        if auto:
            return False, "autonomous job"
        if getattr(dot, "kind", "") in ("watch", "reminder"):
            return False, f"{dot.kind} job"
    return True, ""


class _Failed(Exception):
    pass


def _kill(p):
    if p is None or p.poll() is not None:
        return
    if sys.platform == "win32":
        try:
            subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)], capture_output=True, timeout=15,
                           creationflags=_NO_WINDOW)
        except Exception:
            pass
    try:
        p.kill()
    except Exception:
        pass


def _child_env():
    env = dict(os.environ)
    env.pop("ANTHROPIC_API_KEY", None)  # always the owner's plan, never pay-per-use API billing
    env.pop("ANTHROPIC_AUTH_TOKEN", None)  # (a bearer token would bill the API the same way)
    env.pop("CLAUDECODE", None)
    return env


def command(model, sid, resume, stream_input=False):
    """The exact claude command line (kept separate so it's testable). The prompt goes on stdin
    (plain text, or one stream-json user message when it carries pictures)."""
    return cli() + ["-p", "--output-format", "stream-json", "--verbose", "--include-partial-messages",
                    "--model", ONLY_MODELS.get(model, model), "--tools", "", "--strict-mcp-config",
                    "--setting-sources", "", "--permission-mode", "dontAsk", "--disable-slash-commands",
                    "--system-prompt", SYS_PROMPT] + \
        (["--input-format", "stream-json"] if stream_input else []) + \
        (["--resume", sid] if resume else ["--session-id", sid])


def stream_message(prompt, images):
    """One stream-json user message: the prompt plus pictures given as data: URLs."""
    content = [{"type": "text", "text": prompt}]
    for url in images or []:
        m = re.match(r"data:([\w/+.-]+);base64,(.*)", str(url or ""), re.S)
        if m:
            content.append({"type": "image", "source": {"type": "base64", "media_type": m.group(1),
                                                        "data": m.group(2)}})
    return (json.dumps({"type": "user", "message": {"role": "user", "content": content}}) + "\n").encode("utf-8")


def _five_hour_use(info):
    try:
        w = ((info or {}).get("unifiedWindows") or {}).get("five_hour") or {}
        u = w.get("utilization")
        if u is None and (info or {}).get("rateLimitType") == "five_hour":
            u = info.get("utilization")
        return float(u) if u is not None else None
    except Exception:
        return None


def _run_claude(s, prompt, model, sid, resume, images=None):
    """One claude -p turn. Returns (text, stats) or raises _Failed(reason, limit?)."""
    ENGINE_DIR.mkdir(parents=True, exist_ok=True)
    started = _now()
    stats = {"first_token_s": None, "use": None}
    err = tempfile.TemporaryFile()
    p = None
    body = stream_message(prompt, images) if images else prompt.encode("utf-8", errors="replace")
    try:
        p = subprocess.Popen(command(model, sid, resume, stream_input=bool(images)), stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=err, cwd=str(ENGINE_DIR), env=_child_env(),
                             creationflags=_NO_WINDOW)
        lines = queue.Queue()
        done = object()

        def _write():
            try:
                p.stdin.write(body)
            except Exception:
                pass
            finally:
                try:
                    p.stdin.close()
                except Exception:
                    pass

        def _read():
            try:
                for raw in iter(p.stdout.readline, b""):
                    lines.put(raw)
            except Exception:
                pass
            finally:
                lines.put(done)

        threading.Thread(target=_write, daemon=True).start()
        threading.Thread(target=_read, daemon=True).start()

        partial, final_texts, result = [], [], None
        got_event, last_event = False, started
        tool_filter = None
        try:
            if getattr(s, "StreamingToolFilter", None) is not None and getattr(s, "console", None) is not None:
                tool_filter = s.StreamingToolFilter(s.console)  # the reply shows in the job's log, as on the remote backend
        except Exception:
            tool_filter = None
        while True:
            try:
                raw = lines.get(timeout=0.25)
            except queue.Empty:
                waited = _now() - started
                if not got_event and waited > FIRST_EVENT_TIMEOUT:
                    raise _Failed(f"no output from claude in {FIRST_EVENT_TIMEOUT}s")
                if got_event and _now() - last_event > IDLE_TIMEOUT:
                    raise _Failed(f"claude went quiet for {IDLE_TIMEOUT}s")
                if waited > TOTAL_TIMEOUT:
                    raise _Failed(f"claude took over {TOTAL_TIMEOUT}s")
                continue
            if raw is done:
                break
            if _now() - started > TOTAL_TIMEOUT:
                raise _Failed(f"claude took over {TOTAL_TIMEOUT}s")
            try:
                ev = json.loads(raw.decode("utf-8", errors="replace"))
            except Exception:
                continue
            if not isinstance(ev, dict):
                continue
            got_event, last_event = True, _now()
            kind = ev.get("type")
            if kind == "system" and ev.get("subtype") == "init":
                sid = ev.get("session_id") or sid
            elif kind == "stream_event":
                e = ev.get("event") or {}
                d = e.get("delta") or {}
                if e.get("type") == "content_block_delta" and d.get("type") == "text_delta":
                    t = d.get("text") or ""
                    if not t:
                        continue
                    partial.append(t)
                    if stats["first_token_s"] is None:
                        stats["first_token_s"] = round(_now() - started, 2)
                    if tool_filter is not None:
                        try:
                            tool_filter.feed(t)
                        except Exception:
                            tool_filter = None
                    hook = (getattr(s, "_stream_hook", None) or [None])[0]
                    watchers = list(getattr(s, "_text_watchers", None) or [])
                    if hook is not None or watchers:
                        so_far = "".join(partial)
                        for h in ([hook] if hook is not None else []) + watchers:
                            try:
                                h(so_far)
                            except Exception:
                                pass
            elif kind == "assistant":
                for block in ((ev.get("message") or {}).get("content") or []):
                    if isinstance(block, dict) and block.get("type") == "text" and block.get("text"):
                        final_texts.append(block["text"])
            elif kind == "rate_limit_event":
                info = ev.get("rate_limit_info") or {}
                use = _five_hour_use(info)
                if use is not None:
                    stats["use"] = use
                if str(info.get("status") or "").lower() == "rejected":
                    stats["rejected"] = info
            elif kind == "result":
                result = ev
        if tool_filter is not None:
            try:
                tool_filter.flush()
            except Exception:
                pass
        try:
            p.wait(timeout=15)
        except Exception:
            _kill(p)
        text = "".join(final_texts) or "".join(partial)
        try:
            err.seek(0)
            stderr = err.read().decode("utf-8", errors="replace")[-4000:]
        except Exception:
            stderr = ""
        if stderr.strip():
            try:
                with open(ENGINE_DIR / "stderr.log", "a", encoding="utf-8") as f:
                    f.write(f"--- {time.strftime('%Y-%m-%d %H:%M:%S')} {sid}\n{stderr}\n")
            except Exception:
                pass
        res_text = str((result or {}).get("result") or "")
        limited = bool(stats.get("rejected")) or bool(_LIMIT_RE.search(stderr)) or \
            (bool((result or {}).get("is_error")) and bool(_LIMIT_RE.search(res_text))) or \
            (len(text) < 300 and bool(_LIMIT_RE.search(text)))
        if limited:
            info = stats.get("rejected") or {}
            resets = info.get("resetsAt")
            rest = LIMIT_REST_SEC
            try:
                if resets and 0 < float(resets) - _now() < 6 * 3600:
                    rest = max(rest, float(resets) - _now())
            except Exception:
                pass
            _set_backoff(rest, "Claude plan limit: " + (res_text or text or stderr).strip()[:200])
            raise _Failed("Claude plan limit reached", )
        if result is not None and result.get("is_error"):
            why = (res_text or stderr).strip()[:200] or str(result.get("subtype") or "")
            if _LOGIN_RE.search(why):  # signed out: every step would try Claude first and lose ~2 s
                _set_backoff(LOGIN_REST_SEC, "Claude Code isn't signed in: " + why)
            raise _Failed(f"claude error: {why}")
        if p.returncode not in (0, None) and not text.strip():
            if _LOGIN_RE.search(stderr):
                _set_backoff(LOGIN_REST_SEC, "Claude Code isn't signed in: " + stderr.strip()[-200:])
            raise _Failed(f"claude exited {p.returncode}: {stderr.strip()[-200:]}")
        if not text.strip():
            raise _Failed("claude gave an empty reply")
        if stats["use"] is not None and stats["use"] >= HIGH_USE:
            _set_backoff(BUSY_REST_SEC, f"Claude plan {round(stats['use'] * 100)}% used this five hours")
        stats["sid"] = sid
        return text, stats
    except BaseException:
        _kill(p)
        raise
    finally:
        try:
            err.close()
        except Exception:
            pass


def _turns(sid):
    rows = []
    try:
        with open(ENGINE_DIR / f"{sid}.jsonl", encoding="utf-8") as f:
            for line in f:
                try:
                    rows.append(json.loads(line))
                except Exception:
                    pass
    except Exception:
        pass
    return rows


def _save_turn(sid, prompt, reply, first):
    try:
        ENGINE_DIR.mkdir(parents=True, exist_ok=True)
        with open(ENGINE_DIR / f"{sid}.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps({"prompt": prompt if first else prompt[-200000:], "reply": reply},
                               ensure_ascii=False) + "\n")
    except Exception:
        pass
    return len(_turns(sid))


def replay_prompt(sid, prompt):
    """The task so far, for a model that hasn't seen it (the remote backend taking over a Claude conversation)."""
    rows = _turns(sid)
    if not rows:
        return prompt
    first = str(rows[0].get("prompt") or "")
    parts = []
    for i, r in enumerate(rows):
        if i:
            parts.append(f"[Message]\n{r.get('prompt') or ''}")
        parts.append(f"[Your reply]\n{r.get('reply') or ''}")
    kept, size = [], 0
    for part in reversed(parts):  # the newest steps matter most: trim from the front
        if size + len(part) > REPLAY_CHARS:
            if not kept:
                kept.append(part[-REPLAY_CHARS:])
            break
        kept.append(part)
        size += len(part) + 2
    kept.reverse()
    return (first + "\n\n[Earlier steps of this same task, done by another model — carry on from here, "
            "don't redo them]\n" + "\n\n".join(kept) + "\n\n" + prompt)


class Engine:
    """s.call_api's stand-in inside one job process."""

    def __init__(self, s, orig, job_id="", use_claude=True, why=""):
        self.s, self._orig, self.job, self.use_claude, self.why = s, orig, job_id, use_claude, why
        self._replays = {}  # the remote backend conversation id -> the replay prompt, until the remote backend answers once
        self.used = []      # "claude" / "remote" per call, for the job's log

    def __call__(self, prompt, model, endpoint, access_token, config, conversation_id=None,
                 parent_message_id=None, attached_files=None):
        orig = self._orig
        claude_conv = str(parent_message_id or "").startswith("cc:")
        if conversation_id in self._replays and not parent_message_id:
            # the remote backend's first try at a replay failed and the loop is re-sending: it still needs the replay.
            replay = self._replays.pop(conversation_id)
            return self._to_remote(replay, model, endpoint, access_token, config)
        usable = (self.use_claude and model in MODELS and not attached_files
                  and (conversation_id is None or claude_conv) and backoff_left() <= 0
                  and not os.environ.get("PERIOD_DOT_CLAUDE", "").strip().lower() in _OFF_WORDS
                  and not OFF_FILE.exists() and not self._remote_only())
        if not usable:
            if claude_conv:  # a Claude conversation the remote backend has never seen: give it the task so far
                return self._to_remote(replay_prompt(conversation_id, prompt), model, endpoint,
                                         access_token, config)
            self.used.append("remote")
            return orig(prompt, model, endpoint, access_token, config, conversation_id, parent_message_id,
                        attached_files)
        resume = bool(conversation_id and claude_conv)
        sid = conversation_id if resume else str(uuid.uuid4())
        started = _now()
        try:
            text, stats = _run_claude(self.s, prompt, model, sid, resume)
        except KeyboardInterrupt:
            raise
        except Exception as e:
            reason = str(e) or type(e).__name__
            _log({"job": self.job, "sid": sid, "model": model, "secs": round(_now() - started, 2),
                  "ok": False, "why": reason[:300], "resume": resume})
            if not resume:
                self.used.append("remote")
                return orig(prompt, model, endpoint, access_token, config, conversation_id, parent_message_id,
                            attached_files)
            return self._to_remote(replay_prompt(sid, prompt), model, endpoint, access_token, config)
        sid = stats.get("sid") or sid
        turn = _save_turn(sid, prompt, text, first=not resume)
        _log({"job": self.job, "sid": sid, "model": model, "secs": round(_now() - started, 2),
              "first_token_s": stats.get("first_token_s"), "out_chars": len(text), "ok": True,
              "resume": resume, "turn": turn, "plan_use": stats.get("use")})
        self.used.append("claude")
        return text, sid, f"cc:{turn}"

    def _remote_only(self):
        # Checked on every call, not only at install: remote-only turned on mid-job means the very
        # next step (and its mail text) must not go to Claude. An error here counts as "on" (fail closed).
        try:
            fn = getattr(self.s, "remote_only", None)
            return bool(fn and fn())
        except Exception:
            return True

    def _to_remote(self, replay, model, endpoint, access_token, config):
        self.used.append("remote")
        got = self._orig(replay, model, endpoint, access_token, config, None, None, None)
        try:
            text, conv, parent = got
            if conv and not parent:
                self._replays[conv] = replay  # nothing answered yet: a re-send must carry the replay again
        except Exception:
            pass
        return got


def only_model(model):
    """The Claude model a claude-only install uses for what Period asked for."""
    return model if model in ONLY_MODELS else ONLY_FAST_MODEL


# Claude-only installs keep their own rest file: the remote backend-backed installs rest Claude at 90% of the plan
# (the remote backend takes over), but with no remote backend there's nothing to hand over to, so only a real refusal rests.
ONLY_BACKOFF = DOTS_DIR / "claude_only_backoff.json"
TRANSIENT_RETRIES = 1


def only_backoff_left():
    try:
        until = float(_read_json(ONLY_BACKOFF).get("until") or 0)
    except Exception:
        return 0
    return max(0, until - _now())


def call_only(s, prompt, model, conversation_id=None, parent_message_id=None, attached_files=None):
    """call_api for a claude-only install: same contract, (reply, conversation_id, parent_id).
    Errors come back as "[Error ...]" replies like the remote backend's: a hiccup as "[Error connecting to server]"
    (the agent loop retries those), the plan's limit or a signed-out Claude Code as a plain error."""
    if _under_tests():
        return "[Error claude]: test run (the real Claude plan is never called from tests)", \
            conversation_id, parent_message_id
    if not Path(cli()[0]).exists():
        return ("[Error claude]: Claude Code isn't installed. Install it from https://claude.com/claude-code "
                "and sign in once with `claude`."), conversation_id, parent_message_id
    left = only_backoff_left()
    if left > 0:
        why = _read_json(ONLY_BACKOFF).get("why") or "Claude plan limit"
        return (f"[Error claude]: {why} (try again in about {max(1, round(left / 60))} min)",
                conversation_id, parent_message_id)
    cc_model = only_model(model)
    resume = bool(conversation_id) and str(parent_message_id or "").startswith("cc:")
    sid = conversation_id if resume else str(uuid.uuid4())
    images = [f.get("_data_url") for f in (attached_files or []) if isinstance(f, dict) and f.get("_data_url")]
    started = _now()
    for attempt in range(TRANSIENT_RETRIES + 1):
        try:
            text, stats = _run_claude(s, prompt, cc_model, sid, resume, images=images)
            break
        except KeyboardInterrupt:
            raise
        except Exception as e:
            reason = str(e) or type(e).__name__
            _log({"mode": "claude_only", "sid": sid, "model": cc_model, "secs": round(_now() - started, 2),
                  "ok": False, "why": reason[:300], "resume": resume, "try": attempt + 1})
            rest = _read_json(BACKOFF)
            why = str(rest.get("why") or "")
            if backoff_left() > 0 and (why.startswith("Claude plan limit") or "isn't signed in" in why):
                # _run_claude's own verdict: copy it to the claude-only rest file and stop retrying.
                try:
                    ONLY_BACKOFF.parent.mkdir(parents=True, exist_ok=True)
                    ONLY_BACKOFF.write_text(json.dumps(rest), encoding="utf-8")
                    BACKOFF.unlink()
                except Exception:
                    pass
                hint = (" Open Terminal and run `claude` once to sign in." if "isn't signed in" in why else "")
                return f"[Error claude]: {why}.{hint}", conversation_id, parent_message_id
            if attempt >= TRANSIENT_RETRIES:
                return f"[Error connecting to server]: Claude Code: {reason}", conversation_id, parent_message_id
            time.sleep(2)
    try:  # the 90%-used rest is only for the remote backend-backed installs
        if "% used" in str(_read_json(BACKOFF).get("why") or ""):
            BACKOFF.unlink()
    except Exception:
        pass
    sid = stats.get("sid") or sid
    turn = _save_turn(sid, prompt, text, first=not resume)
    _log({"mode": "claude_only", "sid": sid, "model": cc_model, "secs": round(_now() - started, 2),
          "first_token_s": stats.get("first_token_s"), "out_chars": len(text), "ok": True, "resume": resume,
          "turn": turn, "plan_use": stats.get("use"), "images": len(images)})
    return text, sid, f"cc:{turn}"


def install(s, dot, is_lane=None, autonomous=None):
    """Swap s.call_api for the Claude engine in this job process. Returns a handle for uninstall, or None.
    Also installed (the remote backend only) when the job's conversation is a Claude one but Claude can't be used
    now, so the remote backend gets the task so far instead of an empty conversation."""
    try:
        if getattr(s, "claude_only", None) and s.claude_only():
            return None  # s.call_api already goes to Claude (call_only); there's no remote backend to fall back to
    except Exception:
        pass
    if autonomous is None:
        main = sys.modules.get("__main__")
        autonomous = getattr(main, "_autonomous", None) if main is not None else None
    ok, why = enabled(dot, s, is_lane=is_lane, autonomous=autonomous)
    claude_conv = str(getattr(dot, "parent_id", "") or "").startswith("cc:")
    if not ok and not claude_conv:
        return None
    orig = s.call_api
    eng = Engine(s, orig, job_id=str(getattr(dot, "id", "") or ""), use_claude=ok, why=why)
    s.call_api = eng
    return {"orig": orig, "engine": eng, "ok": ok, "why": why}


def describe(dot, s, handle, is_lane=None, autonomous=None):
    """The job-log line: which model engine this run uses."""
    if handle and handle.get("ok"):
        return "engine: claude"
    why = (handle or {}).get("why")
    if not why:
        if autonomous is None:
            main = sys.modules.get("__main__")
            autonomous = getattr(main, "_autonomous", None) if main is not None else None
        try:
            why = enabled(dot, s, is_lane=is_lane, autonomous=autonomous)[1]
        except Exception as e:
            why = str(e)
    return f"engine: remote ({why or 'off'})"


def uninstall(s, handle):
    if not handle:
        return
    if getattr(s, "call_api", None) is handle.get("engine"):
        s.call_api = handle["orig"]
