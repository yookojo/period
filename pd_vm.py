"""The Dot PC: Period's own computer, a WSL2 Ubuntu with a desktop.

It has its own screen (display :1, never shown on the user's), its own Chrome
and its own files. Windows drives are not mounted inside it and it cannot start
Windows programs; only C:\\Users\\<you>\\DotShare is shared (as ~/share).
The user can watch it live at http://localhost:6080/vnc.html.

Set up once with vm/provision.sh (see docs/DOTS.md). Everything here goes
through `wsl.exe`, so it works from the hidden scheduled-job process too.

On a Mac (2026-11-12, a friend's own Dot) the Dot PC is a Lima VM instead
(mac/dotpc.yaml, set up by mac/setup-dotpc.sh): Ubuntu 24.04 whose user is
`dot` (/home/dot), with only ~/DotShare mounted (as ~/share). Every command
goes through `limactl shell`; DotPC.argv() builds the host command line for
either one.
"""
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

DISTRO = os.environ.get("PERIOD_VM_DISTRO", "Ubuntu-24.04")
LIMA_INSTANCE = os.environ.get("PERIOD_VM_LIMA", "dotpc")
# limactl's own words when the VM is stopped: the command never ran, so booting it and trying again is safe.
_LIMA_STOPPED_RE = re.compile(r"is (stopped|not running)|limactl start", re.I)


def backend():
    """"lima" on a Mac, else "wsl" (checked on every call so tests can switch it)."""
    return "lima" if sys.platform == "darwin" else "wsl"


def limactl():
    """The limactl command. A launchd job's PATH has no Homebrew folders, so look there too."""
    found = shutil.which("limactl")
    if found:
        return found
    for d in ("/opt/homebrew/bin", "/usr/local/bin"):
        p = d + "/limactl"
        if os.path.exists(p):
            return p
    return "limactl"
# 11-08 owner: "turn the vm off". Any wsl.exe call boots the distro again, so while this file exists
# nothing on the Windows side calls into it (delete the file, or the owner says turn it on, to undo).
OFF_FLAG = Path.home() / ".period_dots" / "VM_OFF"


def owner_turned_off():
    return OFF_FLAG.exists()
WEB_PORT = 6080
CDP_PORT = 9222
SHARE_DIR = Path.home() / "DotShare"
LIVE_URL = f"http://localhost:{WEB_PORT}/vnc.html?autoconnect=1&resize=scale"
_NO_WINDOW = 0x08000000 if sys.platform == "win32" else 0

# Reads the page open in the VM's Chrome over the DevTools port.
_PAGE_READER = r'''
import json, sys
from playwright.sync_api import sync_playwright
mode, url, new_tab = (sys.argv[1:] + ["text", "", "0"])[:3]
a, b_ = url, new_tab  # for fill/click/select/upload: what to find, and the value


def settle(p):
    try:
        p.wait_for_load_state("domcontentloaded", timeout=8000)
        p.wait_for_load_state("networkidle", timeout=3000)
    except Exception:
        pass


def find(p, what, kinds):
    """A visible element by label, placeholder, name, button/link text, or css:..."""
    if what.startswith("css:"):
        return p.locator(what[4:]).first
    tries = []
    for k in kinds:
        if k == "label":
            tries += [p.get_by_label(what, exact=True), p.get_by_label(what)]
        elif k == "placeholder":
            tries.append(p.get_by_placeholder(what))
        elif k == "name":
            tries.append(p.locator(f'[name="{what}"], [id="{what}"], [aria-label="{what}"]'))
        elif k in ("button", "link", "checkbox", "radio", "tab", "menuitem", "option", "combobox"):
            tries += [p.get_by_role(k, name=what, exact=True), p.get_by_role(k, name=what)]
        elif k == "text":
            tries += [p.get_by_text(what, exact=True), p.get_by_text(what)]
    for loc in tries:
        try:
            for i in range(min(loc.count(), 5)):
                el = loc.nth(i)
                if el.is_visible():
                    return el
        except Exception:
            continue
    return None


try:
    with sync_playwright() as pw:
        b = pw.chromium.connect_over_cdp("http://127.0.0.1:%d")
        ctx = b.contexts[0]
        pages = [p for p in ctx.pages if not p.url.startswith("devtools")]
        if mode == "goto":
            p = ctx.new_page() if (new_tab == "1" or not pages) else pages[-1]
            p.goto(url, wait_until="domcontentloaded", timeout=30000)
            try:
                p.wait_for_load_state("networkidle", timeout=4000)
            except Exception:
                pass
            p.bring_to_front()
            print(json.dumps({"url": p.url, "title": p.title()})); sys.exit()
        if not pages:
            print(json.dumps({"error": "Chrome has no open page"})); sys.exit()
        # The tab it's working in: Chrome lists targets most recently activated
        # first (every tab claims to be visible and focused, so those don't help).
        p = pages[-1]
        try:
            import urllib.request
            front = json.load(urllib.request.urlopen("http://127.0.0.1:%d/json/list", timeout=3))
            front_id = next(t["id"] for t in front if t.get("type") == "page")
            for x in pages:
                if ctx.new_cdp_session(x).send("Target.getTargetInfo")["targetInfo"]["targetId"] == front_id:
                    p = x
                    break
        except Exception:
            pass
        out = {"url": p.url, "title": p.title()}
        if mode == "fill":
            el = find(p, a, ["label", "placeholder", "name", "combobox", "text"])
            if el is None:
                print(json.dumps({"error": f"no field called {a!r} on the page (try mode fields to list them)"})); sys.exit()
            kind = el.evaluate("e => e.tagName === 'SELECT' ? 'select' : (e.type || '').toLowerCase()")
            if kind == "select":
                el.select_option(label=b_)
            elif kind in ("checkbox", "radio"):
                # Ticking, not typing: "yes"/"true"/anything ticks it, "no"/"off"/"false" unticks.
                if b_.strip().lower() in ("no", "off", "false", "0", "uncheck", "unchecked"):
                    el.uncheck()
                else:
                    el.check()
                out["now"] = "checked" if el.is_checked() else "unchecked"
            else:
                el.fill(b_)
            if "now" not in out:
                out["now"] = el.input_value() if el.evaluate("e => 'value' in e") else ""
        elif mode == "click":
            el = find(p, a, ["button", "link", "checkbox", "radio", "tab", "menuitem", "option", "label", "text"])
            if el is None:
                print(json.dumps({"error": f"nothing called {a!r} to click (try mode links)"})); sys.exit()
            el.click(timeout=8000)
            settle(p)
            out.update(url=p.url, title=p.title())
        elif mode == "upload":
            el = find(p, a, ["label", "name", "button", "text"]) if not a.startswith("css:") else find(p, a, [])
            target = el if el is not None and el.evaluate("e => e.type") == "file" else p.locator("input[type=file]").first
            target.set_input_files(b_)
            out["now"] = "attached " + b_.split("/")[-1]
        elif mode == "fields":
            out["fields"] = p.evaluate("""[...document.querySelectorAll('input,textarea,select')]
              .filter(e => e.offsetParent !== null && !['hidden','submit','button'].includes(e.type)).slice(0, 120).map(e => {
                const id = e.id && document.querySelector(`label[for="${CSS.escape(e.id)}"]`);
                const lab = (id && id.innerText) || (e.closest('label') && e.closest('label').innerText) ||
                            e.getAttribute('aria-label') || e.placeholder || e.name || '';
                const val = e.tagName === 'SELECT' ? (e.selectedOptions[0] || {}).text || '' :
                            (['checkbox','radio'].includes(e.type) ? (e.checked ? 'checked' : 'unchecked') : e.value);
                return {label: lab.trim().slice(0, 80), type: e.type || e.tagName.toLowerCase(),
                        value: (e.type === 'password' ? (val ? '••••' : '') : String(val || '')).slice(0, 120),
                        required: e.required};})""")
        if mode == "text":
            out["text"] = p.evaluate("document.body ? document.body.innerText : ''")[:60000]
        elif mode == "links":
            # Screen coordinates (what vm_click / xdotool use): the page's own
            # coordinates plus where the page sits on screen, below Chrome's toolbar.
            out["links"] = p.evaluate("""(() => {
              const ox = window.screenX + (window.outerWidth - window.innerWidth) / 2;
              const oy = window.screenY + (window.outerHeight - window.innerHeight);
              return [...document.querySelectorAll('a,button,input,textarea,select,[role=button]')]
              .filter(e => e.offsetParent !== null).slice(0, 300).map(e => {
                const r = e.getBoundingClientRect();
                return {tag: e.tagName.toLowerCase(), text: (e.innerText || e.value || e.placeholder || e.ariaLabel || '').trim().slice(0, 80),
                        href: e.href || '', x: Math.round(ox + r.x + r.width / 2), y: Math.round(oy + r.y + r.height / 2)}; });
            })()""")
        print(json.dumps(out))
except Exception as e:
    print(json.dumps({"error": f"{type(e).__name__}: {str(e)[:300]}"}))
''' % (CDP_PORT, CDP_PORT)


def _safe_job(job):
    import re
    return re.sub(r"[^A-Za-z0-9_.-]", "_", str(job or ""))[:80].lstrip(".")


def _chrome_gone(err):
    """An error that means Chrome isn't answering on the DevTools port."""
    e = str(err)
    return any(k in e for k in ("ECONNREFUSED", "lost Chrome", "connect_over_cdp", "Target closed",
                                "Browser closed", "browser has been closed", "Connection closed"))


# Writes the page server files it's sent ({name: text} on stdin) into ~/.dotpc.
_WRITE_SERVER = ("import json, os, sys\nd = os.path.expanduser('~/.dotpc')\nos.makedirs(d + '/tabs', exist_ok=True)\n"
                 "os.chmod(d, 0o700)\nfor k, v in json.load(sys.stdin).items():\n"
                 "    open(os.path.join(d, k + '.new'), 'w').write(v)\n"
                 "    os.replace(os.path.join(d, k + '.new'), os.path.join(d, k))\n")


class DotPC:
    _lock = threading.Lock()
    _holder = None  # the hidden `dotpc run` process that keeps the VM up

    # -- plumbing ---------------------------------------------------------
    @staticmethod
    def argv(cmd, user=None):
        """The host command line that runs cmd (a list) inside the VM, as user (None = the VM's own `dot`).
        Windows: wsl.exe -d DISTRO [-u user] -- cmd. Mac: limactl shell --workdir / INSTANCE [sudo -H -u user] cmd
        (the Lima VM's login user is already dot; --workdir / so it never tries to cd into a Mac folder)."""
        cmd = [str(c) for c in cmd]
        if backend() == "lima":
            pre = [limactl(), "shell", "--workdir", "/", LIMA_INSTANCE]
            if user and user != "dot":
                pre += ["sudo", "-H", "-u", str(user)]
            return pre + cmd
        argv = ["wsl.exe", "-d", DISTRO]
        if user:
            argv += ["-u", user]
        return argv + ["--"] + cmd

    @staticmethod
    def _lima_names():
        p = subprocess.run([limactl(), "list", "--format", "{{.Name}}"], capture_output=True, timeout=30)
        return [ln.strip() for ln in p.stdout.decode("utf-8", errors="ignore").splitlines() if ln.strip()]

    @staticmethod
    def _lima_boot():
        """Start the stopped Lima VM (WSL boots itself on any call; Lima needs asking). True when it came up."""
        try:
            p = subprocess.run([limactl(), "start", "--tty=false", LIMA_INSTANCE], capture_output=True, timeout=600)
            return p.returncode == 0
        except Exception:
            return False

    @staticmethod
    def available():
        if backend() == "lima":
            try:
                return LIMA_INSTANCE in DotPC._lima_names()
            except Exception:
                return False
        if sys.platform != "win32":
            return False
        try:
            out = subprocess.run(["wsl.exe", "-l", "-q"], capture_output=True, timeout=15,
                                 creationflags=_NO_WINDOW).stdout
            return DISTRO in out.decode("utf-16-le", errors="ignore").replace("\0", "")
        except Exception:
            return False

    @staticmethod
    def script_for(command, input_bytes=None):
        """The bash script sent to the VM. wsl.exe pushes a command line through
        another shell, which eats $variables and breaks quotes, so the command
        always travels as a script on stdin instead; data for the command's
        stdin rides along base64-encoded (so it survives any bytes, CRLF or BOM)."""
        command = command.replace("\r\n", "\n").lstrip("﻿")
        if input_bytes is None:
            return (command + "\n").encode("utf-8")
        import base64
        data = base64.encodebytes(input_bytes).decode("ascii")
        # The command may span lines, so it goes in a function; the heredoc body
        # must start right after the line that opens it.
        return f"__sc_cmd() {{\n{command}\n}}\nbase64 -d <<'__SC_DATA__' | __sc_cmd\n{data}__SC_DATA__\n".encode("utf-8")

    # 2026-11-07: wsl.exe failed with "Wsl/Service/0x8007274c" (Windows couldn't reach the WSL
    # service) on and off for ~45 min. That error comes from wsl.exe itself, before bash starts,
    # so the command never ran and retrying is safe. One failure used to end the job's check and
    # park the Amazon job until the owner texted again.
    LINK_RETRY_WAITS = (5, 15, 30, 60)   # seconds between tries (~2 min in all)

    @staticmethod
    def _link_error(code, out, err):
        """wsl.exe's own "couldn't reach the WSL service" failure (UTF-16 text, exit 0xFFFFFFFF)."""
        if code not in (-1, 4294967295):
            return ""
        blob = (bytes(out[:4000]).replace(b"\x00", b"").decode("utf-8", errors="replace")
                + " " + str(err or "")[:2000].replace("\x00", ""))
        if "Wsl/" not in blob:
            return ""
        return " ".join(blob.split())[:400]

    @classmethod
    def link_up(cls, timeout=20):
        try:
            p = subprocess.run(cls.argv(["true"]), capture_output=True,
                               timeout=timeout, creationflags=_NO_WINDOW)
            return p.returncode == 0
        except Exception:
            return False

    @classmethod
    def sh(cls, command, timeout=120, user=None, input_bytes=None, link_retries=None):
        """Run bash inside the VM (multi-line scripts fine). Returns (exit_code, stdout_bytes, stderr_text).
        A link failure (the command never reached Linux) is retried with backoff; if the link
        stays down, the exit code is 75 and stderr starts with "Dot PC link down"."""
        argv = cls.argv(["bash", "-l", "-s"], user=user)
        if owner_turned_off():
            return 77, b"", ("Dot PC is off: the owner turned it off, so the command didn't run. Don't turn it "
                             "back on and don't retry; say what you'd need it for and stop.")
        waits = cls.LINK_RETRY_WAITS if link_retries is None else tuple(link_retries)
        script = cls.script_for(command, input_bytes)
        for attempt in range(len(waits) + 1):
            try:
                p = subprocess.run(argv, input=script, capture_output=True,
                                   timeout=timeout, creationflags=_NO_WINDOW)
            except subprocess.TimeoutExpired:
                return 124, b"", f"timed out after {timeout}s"
            if backend() == "lima":
                err = p.stderr.decode("utf-8", errors="replace")
                if p.returncode != 0 and not p.stdout and _LIMA_STOPPED_RE.search(err) and cls._lima_boot():
                    # The VM was stopped, so the command never ran: boot it, then run the command once more.
                    try:
                        p = subprocess.run(argv, input=script, capture_output=True, timeout=timeout)
                    except subprocess.TimeoutExpired:
                        return 124, b"", f"timed out after {timeout}s"
                    err = p.stderr.decode("utf-8", errors="replace")
                return p.returncode, p.stdout, err
            link = cls._link_error(p.returncode, p.stdout, p.stderr.decode("utf-8", errors="replace"))
            if not link:
                return p.returncode, p.stdout, p.stderr.decode("utf-8", errors="replace")
            if attempt < len(waits):
                time.sleep(waits[attempt])
        return 75, b"", (f"Dot PC link down: wsl.exe couldn't reach the Linux side after {len(waits) + 1} "
                         f"tries over ~{sum(waits)}s, so the command never ran. ({link})")

    @classmethod
    def x(cls, command, timeout=30):
        """A command on the VM's screen (DISPLAY=:1)."""
        return cls.sh("export DISPLAY=:1; unset WAYLAND_DISPLAY; " + command, timeout=timeout)

    @classmethod
    def running(cls):
        """Whether the desktop is up (the cdp line is Chrome's; ensure() handles that)."""
        code, out, _ = cls.sh("dotpc status", timeout=20)
        text = out.decode(errors="replace")
        desktop = [ln for ln in text.splitlines() if ln.strip() and not ln.lower().startswith(("cdp", "chrome"))]
        return code == 0 and bool(desktop) and not any("down" in ln for ln in desktop)

    @classmethod
    def start(cls):
        """Boot the desktop if needed. Returns a short status line."""
        with cls._lock:
            if cls._holder is not None and cls._holder.poll() is None and cls.running():
                return "already running"
            mac = backend() == "lima"
            if mac and not owner_turned_off() and not cls.link_up():
                cls._lima_boot()  # Lima doesn't boot on its own the way WSL does
            cls._holder = subprocess.Popen(
                cls.argv(["dotpc", "run"]),
                stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                creationflags=_NO_WINDOW, **({"start_new_session": True} if mac else {}))
            for _ in range(40):
                time.sleep(0.25)
                if cls.running():
                    return "started"
            return "started, but the desktop hasn't answered yet"

    @classmethod
    def stop(cls):
        cls.sh("dotpc stop; pkill -f google-chrome", timeout=30)
        with cls._lock:
            if cls._holder is not None:
                try:
                    cls._holder.terminate()
                except Exception:
                    pass
                cls._holder = None
        if backend() == "lima":
            subprocess.run([limactl(), "stop", LIMA_INSTANCE], capture_output=True, timeout=120)
            return
        subprocess.run(["wsl.exe", "--terminate", DISTRO], capture_output=True,
                       timeout=30, creationflags=_NO_WINDOW)

    @classmethod
    def live_url(cls, with_password=False):
        """The live-view link. No password by default: it ends up in tool results,
        chat logs and texts. The viewer asks for it (it's in ~/.vnc/plain in the VM);
        with_password=True is only for the signed-in local Dots page."""
        if not with_password:
            return LIVE_URL
        code, out, _ = cls.sh("cat ~/.vnc/plain 2>/dev/null", timeout=10)
        pw = out.decode(errors="ignore").strip() if code == 0 else ""
        return LIVE_URL + (f"&password={pw}" if pw else "")

    @classmethod
    def ensure(cls):
        """Desktop up, and Chrome answering on the DevTools port (`dotpc start`
        brings back just the parts that are down, never restarting the rest)."""
        if not cls.running():
            cls.start()
        if not cls._chrome_up():
            cls.sh("dotpc start >/dev/null 2>&1", timeout=40)
            for _ in range(30):
                if cls._chrome_up():
                    break
                time.sleep(0.5)

    # -- screen -------------------------------------------------------------
    @classmethod
    def screenshot_png(cls):
        cls.ensure()
        code, out, err = cls.x("import -window root png:-", timeout=30)
        if code != 0 or not out.startswith(b"\x89PNG"):
            raise RuntimeError(err.strip() or "screenshot failed")
        return out

    @classmethod
    def click(cls, x, y, button="left", double=False):
        b = {"left": 1, "middle": 2, "right": 3}.get(str(button), 1)
        rep = "--repeat 2 --delay 80 " if double else ""
        return cls.x(f"xdotool mousemove {int(x)} {int(y)} click {rep}{b}")

    @classmethod
    def type_text(cls, text):
        return cls.sh("export DISPLAY=:1; unset WAYLAND_DISPLAY; xdotool type --delay 8 --file -", timeout=120,
                      input_bytes=str(text).encode("utf-8"))

    @classmethod
    def key(cls, keys):
        # "ctrl+l", "Return", "ctrl+shift+t" -- xdotool key names
        return cls.x("xdotool key --delay 40 " + " ".join(shlex.quote(k) for k in str(keys).split()))

    @classmethod
    def scroll(cls, x, y, amount):
        button = 5 if int(amount) > 0 else 4
        return cls.x(f"xdotool mousemove {int(x)} {int(y)} click --repeat {min(abs(int(amount)), 30)} {button}")

    # -- browser ------------------------------------------------------------
    @classmethod
    def _chrome_up(cls):
        code, out, _ = cls.sh(f"curl -s -m 2 http://127.0.0.1:{CDP_PORT}/json/version", timeout=10)
        return code == 0 and out.strip().startswith(b"{")

    @classmethod
    def current_url(cls):
        """URL of this job's own tab (or the front tab when it has none yet), or ""."""
        res = cls.page("url", _fallback=False, _timeout=15)
        if res.get("url"):
            return res["url"]
        code, out, _ = cls.sh(f"curl -s -m 2 http://127.0.0.1:{CDP_PORT}/json/list", timeout=10)
        try:
            pages = [p for p in json.loads(out) if p.get("type") == "page"]
            return pages[0].get("url", "") if pages else ""
        except Exception:
            return ""

    # -- the page server (vm/pageserver.py): one tab per job -----------------
    _deployed = False
    _deploy_lock = threading.Lock()

    @staticmethod
    def job_id():
        """Which job is asking: the Dots daemon sets DOT_JOB for each job process."""
        return _safe_job(os.environ.get("DOT_JOB", "")) or "cli"

    @staticmethod
    def _server_files():
        here = Path(__file__).resolve().parent / "vm"
        return {"pageserver.py": (here / "pageserver.py").read_text(encoding="utf-8"),
                "pageclient.py": (here / "pageclient.py").read_text(encoding="utf-8")}

    @classmethod
    def _deploy(cls):
        """Ship the page server into the VM when it's missing or out of date (no
        manual install: /mnt/c isn't mounted there). A new version also stops the
        old server, so the next call starts the new one."""
        with cls._deploy_lock:
            if cls._deployed:
                return True
            import hashlib
            try:
                files = cls._server_files()
            except OSError:
                return False
            ver = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()[:16]
            code, out, _ = cls.sh("cat ~/.dotpc/page.ver 2>/dev/null; test -f ~/.dotpc/pageserver.py && echo HAVE",
                                  timeout=20)
            words = out.decode(errors="replace").split()
            if code == 0 and words[:1] == [ver] and "HAVE" in words:
                cls._deployed = True
                return True
            code, out, err = cls.sh(
                f"python3 -c {shlex.quote(_WRITE_SERVER)} && echo {ver} > ~/.dotpc/page.ver && "
                "{ pkill -u \"$(id -u)\" -f '[.]dotpc/pageserver[.]py' || true; } && echo DEPLOYED",
                timeout=30, input_bytes=json.dumps(files).encode())
            cls._deployed = code == 0 and b"DEPLOYED" in out
            return cls._deployed

    @classmethod
    def page(cls, op, _fallback=True, _timeout=90, **req):
        """One request to the page server for this job's tab. Returns a dict
        ({"error": ...} on failure). Falls back to the one-shot reader (front tab)
        when the server can't run at all."""
        req = dict(req, op=op, job=_safe_job(req.get("job")) or cls.job_id())
        res = cls._server_call(req, _timeout)
        if res.get("error") and _chrome_gone(res["error"]):
            # Chrome restarted or the port isn't up yet: bring it back, try once more.
            cls.ensure()
            res = cls._server_call(req, _timeout)
        if str(res.get("error", "")).startswith("NOSERVER") and _fallback:
            return cls._old_reader(req)
        return res

    @classmethod
    def _server_call(cls, req, timeout):
        if not cls._deploy():
            return {"error": "NOSERVER: couldn't install the page server in the VM"}
        code, out, err = cls.sh(f"python3 ~/.dotpc/pageclient.py {int(max(5, timeout - 5))}", timeout=timeout,
                                input_bytes=json.dumps(req).encode())
        try:
            return json.loads(out.decode(errors="replace").strip().splitlines()[-1])
        except Exception:
            tail = (err or out.decode(errors="replace")).strip().splitlines()[-1:] or ["no answer"]
            return {"error": "NOSERVER: " + tail[0][-300:]}

    @classmethod
    def _old_reader(cls, req):
        """The one-shot reader (a fresh Playwright per call, front tab only)."""
        op = req["op"]
        if op == "goto":
            res = cls._reader("goto", req.get("url", ""), "1" if req.get("new_tab") else "0")
        elif op == "read":
            mode = req.get("mode")
            res = cls._reader(mode if mode in ("fields", "links") else "text", "", "0")
            if res.get("fields"):
                res["fields"] = [f"- {f['label'] or '(no label)'} [{f['type']}{', required' if f.get('required') else ''}]"
                                 + (f": {f['value']!r}" if f.get("value") else "") for f in res["fields"]]
        elif op == "click":
            res = cls._reader("click", req.get("text", ""), "")
        elif op == "upload":
            res = cls._reader("upload", req.get("field", ""), req.get("path", ""))
        elif op == "fill":
            res = {"filled": []}
            files = req.get("files") or {}
            for label, value in list((req.get("fields") or {}).items()) + list(files.items()):
                r = cls._reader("upload" if label in files else "fill", str(label), str(value))
                if r.get("error"):
                    res["missed"] = {"label": label, "candidates": [], "why": r["error"]}
                    break
                res["filled"].append({"label": label, "now": r.get("now", "")})
                res.update(url=r.get("url"), title=r.get("title"))
            if req.get("then_click") and "missed" not in res:
                r = cls._reader("click", str(req["then_click"]), "")
                if r.get("error"):
                    res["missed"] = {"label": req["then_click"], "candidates": [], "why": r["error"]}
                else:
                    res.update(clicked=req["then_click"], url=r.get("url"), title=r.get("title"))
        elif op == "url":
            return {"url": ""}
        else:
            return {"error": f"the page server isn't running and {op!r} needs it"}
        res["fallback"] = True
        return res

    @classmethod
    def _reader(cls, mode, a, b):
        argv = " ".join(shlex.quote(str(x)) for x in (mode, a, b))
        code, out, err = cls.sh(f"~/.venv/bin/python - {argv}", timeout=90, input_bytes=_PAGE_READER.encode())
        try:
            return json.loads(out.decode(errors="replace").strip().splitlines()[-1])
        except Exception:
            tail = (err or out.decode(errors="replace")).strip().splitlines()[-1:] or ["couldn't reach the page"]
            return {"error": tail[0][-300:]}

    @classmethod
    def open_url(cls, url, new_tab=False):
        """Open url in this job's tab. Returns the page summary dict (url, title,
        headings, fields, text) or {"error": ...}."""
        if not cls._chrome_up():
            cls.ensure()
            if not cls._chrome_up():
                return {"error": "Chrome on the Dot PC didn't start (see /tmp/dotpc/google-chrome.log in the VM)"}
        return cls.page("goto", url=url, new_tab=bool(new_tab))

    @classmethod
    def act(cls, mode, what, value=""):
        """Drive the page by meaning instead of pixels (kept for older callers):
        fill (label -> value), click (button/link text), upload (file input -> VM
        path), fields (list every form field)."""
        if mode == "fill":
            res = cls.page("fill", fields={what: value})
            if res.get("missed"):
                m = res["missed"]
                return {"error": f"no field called {m['label']!r}" + (f" ({m['why']})" if m.get("why") else ""),
                        "candidates": m.get("candidates", [])}
            return dict(res, now=(res.get("filled") or [{}])[-1].get("now", ""))
        if mode == "click":
            return cls.page("click", text=what)
        if mode == "upload":
            return cls.page("upload", field=what, path=value)
        if mode == "fields":
            return cls.page("read", mode="fields")
        return {"error": f"unknown mode {mode!r}"}

    @classmethod
    def read_page(cls, mode="text", url="", new_tab=False, **kw):
        if mode == "goto":
            return cls.open_url(url, new_tab=new_tab)
        return cls.page("read", mode=mode, **kw)

    @classmethod
    def close_tab(cls, job=None):
        return cls.page("close", job=job or cls.job_id(), _fallback=False, _timeout=20)

    # -- jobs' own processes ----------------------------------------------
    # Every vm_run runs as its own session tagged DOT_JOB=<job> (and DOT_RUN=<run>),
    # so stopping a job can stop what it started inside the VM too.
    _PROTECTED = r"remote-debugging-port=9222|Xvfb|xfce4|x11vnc|websockify|dotpc|pageserver[.]py|novnc"

    @classmethod
    def run_job_script(cls, command, timeout=300, job=None):
        """Run a bash script for a job: written to a temp file, run as
        `bash file </dev/null` in its own session (setsid -w). Returns (code, out, err)."""
        import secrets
        job = _safe_job(job) or cls.job_id()
        run = secrets.token_hex(4)
        wrapper = "\n".join([
            'f=$(mktemp /tmp/dotrun.XXXXXX.sh) && cat > "$f" || exit 97',
            "mkdir -p ~/.dotjobs",
            f"export DOT_JOB={job} DOT_RUN={run} DISPLAY=:1",
            "unset WAYLAND_DISPLAY",
            "cd ~",
            # Its session id is kept while it runs (kill_job stops that session too),
            # and removed when it ends so a reused id can never be killed later.
            """setsid -w bash -c 'echo $$ > ~/.dotjobs/"$DOT_JOB.run-$DOT_RUN".sid; exec bash "$0" </dev/null' "$f" """,
            "code=$?",
            'rm -f "$f" ~/.dotjobs/"$DOT_JOB.run-$DOT_RUN".sid',
            "exit $code", ""])
        code, out, err = cls.sh(wrapper, timeout=timeout, input_bytes=command.replace("\r\n", "\n").encode("utf-8"))
        if code == 124 and err.startswith("timed out"):
            if not cls.link_up():
                # 11-07: a 1-line grep "timed out after 60s" while WSL itself was frozen.
                err += ("; the Dot PC link (WSL) isn't answering either, so the hang is the link, not the "
                        "command (it may not have run)")
            else:
                cls._kill_tagged("DOT_RUN", run)  # the script outlives wsl.exe in its own session
        return code, out, err

    @classmethod
    def kill_script(cls, var, value, sid_files=()):
        """The bash that kills every VM process whose environment has var=value,
        and every session listed in the sid_files globs (vm_run's <job>.sids,
        vm_claude's <job>.claude-<rid>.sid): TERM, then KILL ~2 s later. Never the
        desktop, the shared Chrome or the page server. Removes the sid files.
        Prints KILLED <n>."""
        env_loop = ('for d in /proc/[0-9]*; do pid=${d#/proc/}; [ "$pid" = "$$" ] && continue; '
                    'tr "\\0" "\\n" < "$d/environ" 2>/dev/null | grep -qxF "$want" || continue; '
                    'tr "\\0" " " < "$d/cmdline" 2>/dev/null | grep -qE "$prot" && continue; '
                    'kill -%s "$pid" 2>/dev/null && n=$((n+1)); done')
        sid_loop = ('for s in $sids; do for p in $(pgrep -s "$s"); do [ "$p" = "$$" ] && continue; '
                    'tr "\\0" " " < /proc/$p/cmdline 2>/dev/null | grep -qE "$prot" && continue; '
                    'kill -%s "$p" 2>/dev/null && n=$((n+1)); done; done')
        lines = [f"want={shlex.quote(f'{var}={value}')}; prot={shlex.quote(cls._PROTECTED)}; n=0; sids=",
                 f"files=$(ls -1 {' '.join(sid_files)} 2>/dev/null)" if sid_files else "files=",
                 # numeric session ids above 1 only (never init's session)
                 'for f in $files; do for s in $(grep -oE "^[0-9]+$" "$f"); do [ "$s" -gt 1 ] && sids="$sids $s"; done; done',
                 'sids=$(echo $sids | tr " " "\\n" | sort -un | tr "\\n" " ")',
                 env_loop % "TERM", sid_loop % "TERM",
                 '[ "$n" -gt 0 ] && sleep 2',
                 "m=$n; " + env_loop % "KILL" + "; " + sid_loop % "KILL" + "; n=$m",
                 'for f in $files; do rm -f "$f"; done',
                 'echo "KILLED $n"', ""]
        return "\n".join(lines)

    @classmethod
    def _kill_tagged(cls, var, value, sid_files=()):
        code, out, _ = cls.sh(cls.kill_script(var, value, sid_files), timeout=40)
        try:
            return int(out.decode(errors="replace").split("KILLED")[-1].split()[0])
        except Exception:
            return 0

    @classmethod
    def kill_job(cls, job_id, close_tab=False):
        """Stop everything a job started inside the VM: its vm_run scripts, its
        vm_claude runs (sessions in ~/.dotjobs/<job>*.sid) and anything else tagged
        DOT_JOB=<job>; never the desktop or the shared Chrome. Returns how many
        processes it stopped."""
        job = _safe_job(job_id)
        if not job:
            return 0
        n = cls._kill_tagged("DOT_JOB", job, sid_files=(f'"$HOME/.dotjobs/{job}".sids', f'"$HOME/.dotjobs/{job}".*sid',
                                                       f'"$HOME/.dotjobs/{job}".sid'))
        if close_tab:
            try:
                cls.close_tab(job)
            except Exception:
                pass
        return n

    # -- files --------------------------------------------------------------
    @staticmethod
    def qpath(path):
        """Shell-quote a VM path, keeping ~/ meaning the home folder."""
        path = str(path)
        if path == "~" or path.startswith("~/"):
            return '"$HOME"' + (shlex.quote(path[1:]) if len(path) > 1 else "")
        return shlex.quote(path)

    @classmethod
    def put(cls, local_path, vm_path=None):
        data = Path(local_path).read_bytes()
        dest = cls.qpath(vm_path or f"~/{Path(local_path).name}")
        code, _, err = cls.sh(f"mkdir -p \"$(dirname {dest})\" && cat > {dest} && wc -c < {dest}",
                              input_bytes=data, timeout=300)
        if code != 0:
            raise RuntimeError(err.strip() or "copy failed")
        return vm_path or f"~/{Path(local_path).name}"

    @classmethod
    def get(cls, vm_path, local_path):
        code, out, err = cls.sh(f"cat {cls.qpath(vm_path)}", timeout=300)
        if code != 0:
            raise RuntimeError(err.strip() or "copy failed")
        if not out:
            raise RuntimeError(f"{vm_path} is empty on the Dot PC")  # never hand back a silent 0-byte file
        Path(local_path).parent.mkdir(parents=True, exist_ok=True)
        Path(local_path).write_bytes(out)
        return str(local_path)
