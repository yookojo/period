"""Dot PC page server: runs INSIDE the VM as user dot (~/.venv/bin/python).

One Playwright connection to the VM's Chrome (CDP on 127.0.0.1:9222) stays
open, so each vm_open / vm_read / vm_fill / vm_click costs one small request
instead of a fresh Python + Playwright start. It listens on a unix socket
(~/.dotpc/page.sock, never forwarded to Windows) and answers one JSON line per
connection: {"op": ..., "job": ..., ...} -> {...}.

Every job gets its own tab, opened in the background with
Target.createTarget, so jobs never fight over "the tab in front". A job's tab
id is kept in memory and in ~/.dotpc/tabs/<job>; if the tab is gone, a new
one is made. The tab in front (the one the user watches) is never used.

Shipped from Windows by pd_vm.DotPC on demand (no manual install).
"""
import asyncio
import difflib

import json
import os
import re
import sys
import time
import traceback

CDP = "http://127.0.0.1:9222"
HOME = os.path.expanduser("~")
DIR = os.path.join(HOME, ".dotpc")
SOCK = os.path.join(DIR, "page.sock")
TABS = os.path.join(DIR, "tabs")
SUMMARY_TEXT = 1500
TEXT_PAGE = 10000

pw = None
browser = None
pages = {}      # job -> Page
tab_ids = {}    # Page -> targetId
job_locks = {}  # job -> asyncio.Lock (one action per tab at a time)
_connect_lock = asyncio.Lock()


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def safe_job(job):
    job = re.sub(r"[^A-Za-z0-9_.-]", "_", str(job or "cli"))[:80].lstrip(".")
    return job or "cli"


# --- connection and tabs ------------------------------------------------------

async def connect():
    global pw, browser
    async with _connect_lock:
        if browser is not None and browser.is_connected():
            return browser
        from playwright.async_api import async_playwright
        if pw is None:
            pw = await async_playwright().start()
        pages.clear()
        tab_ids.clear()
        browser = await pw.chromium.connect_over_cdp(CDP, timeout=15000)
        log("connected to Chrome")
        return browser


async def target_id(page):
    if page in tab_ids:
        return tab_ids[page]
    s = await page.context.new_cdp_session(page)
    try:
        tid = (await s.send("Target.getTargetInfo"))["targetInfo"]["targetId"]
    finally:
        try:
            await s.detach()
        except Exception:
            pass
    tab_ids[page] = tid
    return tid


async def page_by_target(tid):
    for ctx in browser.contexts:
        for p in ctx.pages:
            try:
                if await target_id(p) == tid:
                    return p
            except Exception:
                continue
    return None


async def job_page(job, create=True):
    """The job's own tab: remembered, re-found after a restart, or made new."""
    await connect()
    p = pages.get(job)
    if p is not None and not p.is_closed():
        return p
    path = os.path.join(TABS, job)
    try:
        tid = open(path).read().strip()
    except OSError:
        tid = ""
    if tid:
        p = await page_by_target(tid)
        if p is not None and not p.is_closed():
            pages[job] = p
            return p
    if not create:
        return None
    ctx = browser.contexts[0]
    s = await browser.new_browser_cdp_session()
    try:
        tid = (await s.send("Target.createTarget", {"url": "about:blank", "background": True}))["targetId"]
    finally:
        try:
            await s.detach()
        except Exception:
            pass
    p = None
    for _ in range(50):
        p = await page_by_target(tid)
        if p is not None:
            break
        await asyncio.sleep(0.1)
    if p is None:
        raise RuntimeError("Chrome made a tab but Playwright never saw it")
    os.makedirs(TABS, exist_ok=True)
    with open(path, "w") as f:
        f.write(tid)
    pages[job] = p
    log("new tab", job, tid[:8], "contexts", len(browser.contexts), "pages", len(ctx.pages))
    return p


# --- waiting ------------------------------------------------------------------

_QUIET_JS = """() => {
  if (!window.__scQuiet) {
    window.__scQuiet = Date.now();
    try { new MutationObserver(() => { window.__scQuiet = Date.now(); })
            .observe(document, {subtree: true, childList: true, attributes: true, characterData: true}); }
    catch (e) {}
  }
  return [document.readyState, Date.now() - window.__scQuiet];
}"""


async def settle(p, before_url=None, cap=3.0, quiet_ms=500):
    """Until the URL changed and the new page is parsed, or the DOM has been
    quiet for ~500 ms; at most `cap` seconds (no networkidle: many sites never
    go idle, which cost ~3 s on every click)."""
    end = time.time() + cap
    while time.time() < end:
        try:
            state, quiet = await p.evaluate(_QUIET_JS)
        except Exception:  # mid-navigation
            await asyncio.sleep(0.1)
            continue
        if state != "loading" and quiet >= quiet_ms:
            return
        if before_url is not None and p.url != before_url and state != "loading" and quiet >= 250:
            return
        await asyncio.sleep(0.1)


# --- page reading -------------------------------------------------------------

# Label for a form control, as a person sees it.
_LABEL_JS = r"""
window.__scLabel = window.__scLabel || function (e) {
  const t = s => (s || '').replace(/\s+/g, ' ').trim();
  let lab = '';
  if (e.getAttribute('aria-labelledby')) {
    lab = e.getAttribute('aria-labelledby').split(/\s+/).map(i => {
      const x = document.getElementById(i); return x ? x.innerText : ''; }).join(' ');
  }
  if (!t(lab) && e.id) {
    try { const l = document.querySelector(`label[for="${CSS.escape(e.id)}"]`); if (l) lab = l.innerText; } catch (x) {}
  }
  if (!t(lab) && e.closest('label')) lab = e.closest('label').innerText;
  if (!t(lab)) lab = e.getAttribute('aria-label') || e.placeholder || '';
  if (!t(lab)) {
    // Greenhouse/Lever style: <div><label>Name</label><div><input></div></div>
    let n = e;
    for (let i = 0; i < 4 && n && !t(lab); i++) {
      n = n.parentElement;
      if (!n) break;
      const l = n.querySelector('label, legend, .label, [class*=label]');
      if (l && !l.contains(e)) lab = l.innerText;
    }
  }
  if (!t(lab)) lab = e.name || e.id || '';
  return t(lab).slice(0, 100);
};
"""

_FIELDS_JS = "() => {" + _LABEL_JS + r"""
return (() => {
  const vis = e => !!(e.offsetParent || e.getClientRects().length);
  const out = [];
  let n = 0;
  const seenRadio = new Set();
  for (const e of document.querySelectorAll('input,textarea,select,[role=combobox],[contenteditable=true]')) {
    const type = (e.tagName === 'SELECT' ? 'select' : (e.getAttribute('role') === 'combobox' && e.tagName !== 'INPUT') ? 'combobox'
                  : e.isContentEditable && e.tagName !== 'INPUT' && e.tagName !== 'TEXTAREA' ? 'text' : (e.type || e.tagName).toLowerCase());
    if (['hidden', 'submit', 'button', 'reset', 'image'].includes(type)) continue;
    const isFile = type === 'file';
    if (!vis(e) && !isFile) continue;   // hidden file inputs still count: they take uploads
    // React-Select's invisible "required" twin of a dropdown
    if (!isFile && (e.getAttribute('aria-hidden') === 'true' ||
        (e.tabIndex === -1 && getComputedStyle(e).opacity === '0'))) continue;
    const combo = type === 'combobox' || e.getAttribute('role') === 'combobox' ||
                  (e.getAttribute('aria-autocomplete') || '') !== '' || e.getAttribute('aria-haspopup') === 'listbox';
    let label = window.__scLabel(e);
    if (isFile || /^(attach|upload|choose file|browse)$/i.test(label)) {
      // "Attach" says nothing: use the group's own label ("Resume/CV*").
      const g = e.closest('[role=group],fieldset,.file-upload,[class*=upload],[class*=field]');
      let gl = '';
      if (g) {
        const ids = g.getAttribute('aria-labelledby');
        gl = ids ? ids.split(/\s+/).map(i => (document.getElementById(i) || {}).innerText || '').join(' ')
                 : (g.getAttribute('aria-label') || ((g.querySelector('legend,.label,[class*=label]:not(label)') || {}).innerText || ''));
      }
      gl = (gl || '').replace(/\s+/g, ' ').trim();
      if (gl && gl !== label) label = (gl + (label ? ' (' + label + ')' : '')).slice(0, 100);
    }
    if (type === 'radio' || type === 'checkbox') {
      const g = e.closest('fieldset,[role=radiogroup],[role=group]');
      const gl = g ? ((g.querySelector('legend') || {}).innerText || g.getAttribute('aria-label') || '') : '';
      if (type === 'radio' && e.name) {
        if (seenRadio.has(e.name)) continue;
        seenRadio.add(e.name);
        const opts = [...document.querySelectorAll(`input[type=radio][name="${CSS.escape(e.name)}"]`)];
        const chosen = opts.find(o => o.checked);
        e.setAttribute('data-sc-f', String(n));
        out.push({i: n++, label: (gl || label).replace(/\s+/g, ' ').trim().slice(0, 100), type: 'radio',
                  options: opts.map(o => window.__scLabel(o)).slice(0, 12),
                  value: chosen ? window.__scLabel(chosen) : '', required: opts.some(o => o.required)});
        continue;
      }
      if (gl) label = (gl.replace(/\s+/g, ' ').trim() + ': ' + label).slice(0, 100);
    }
    let val;
    if (type === 'select') val = (e.selectedOptions[0] || {}).text || '';
    else if (type === 'checkbox') val = e.checked ? 'checked' : 'unchecked';
    else if (isFile) val = [...(e.files || [])].map(f => f.name).join(', ');
    else if (e.isContentEditable && !('value' in e)) val = e.innerText;
    else {
      val = e.value || '';
      if (!val && combo) {
        // React-Select shows the choice in a sibling, not in the input.
        let n = e;
        for (let k = 0; k < 4 && n && !val; k++) {
          n = n.parentElement;
          const sv = n && n.querySelector('[class*=single-value],[class*=singleValue],[class*=multi-value__label],[class*=multiValue]');
          if (sv) val = sv.innerText;
        }
      }
    }
    if (type === 'password' && val) val = '••••';
    const f = {i: n, label, type: combo && type !== 'select' ? 'combobox' : type, value: String(val || '').trim().slice(0, 120),
               required: !!(e.required || e.getAttribute('aria-required') === 'true' || /\*\s*$/.test(label))};
    if (type === 'select') f.options = [...e.options].map(o => o.text.trim()).filter(Boolean).slice(0, 15);
    if (isFile && !vis(e)) f.hidden = true;
    e.setAttribute('data-sc-f', String(n));
    n++;
    out.push(f);
    if (out.length >= 150) break;
  }
  return out;
})();
}
"""

_CLICKABLE_JS = r"""
(() => {
  const vis = e => !!(e.offsetParent || e.getClientRects().length);
  const out = [];
  for (const e of document.querySelectorAll('a,button,[role=button],[role=link],[role=tab],[role=menuitem],input[type=submit],input[type=button],summary')) {
    if (!vis(e)) continue;
    const text = (e.innerText || e.value || e.getAttribute('aria-label') || e.title || '').replace(/\s+/g, ' ').trim().slice(0, 80);
    if (!text) continue;
    out.push({tag: e.tagName.toLowerCase(), text, href: (e.href && !String(e.href).startsWith('javascript')) ? String(e.href).slice(0, 160) : ''});
    if (out.length >= 300) break;
  }
  return out;
})()
"""

# The page's own words, minus menus, headers, footers and cookie banners.
_TEXT_JS = r"""
(sel) => {
  let root = sel ? document.querySelector(sel) : null;
  if (sel && !root) return null;
  if (!root) root = document.querySelector('main,[role=main],article') || document.body;
  if (!root) return '';
  if (sel) return root.innerText || '';
  const drop = root.querySelectorAll('nav,footer,header,aside,[role=navigation],[role=banner],[role=contentinfo],script,style,noscript,[aria-hidden=true],[id*=cookie],[class*=cookie]');
  const saved = [];
  for (const d of drop) { if (d === root || d.contains(root)) continue; saved.push([d, d.style.display]); d.style.display = 'none'; }
  const text = root.innerText || '';
  for (const [d, v] of saved) d.style.display = v;
  return text;
}
"""


def squeeze(text):
    lines, last = [], None
    for ln in (text or "").splitlines():
        ln = re.sub(r"[ \t ]+", " ", ln).strip()
        if not ln:
            if last != "":
                lines.append("")
            last = ""
            continue
        if ln == last:
            continue
        lines.append(ln)
        last = ln
    return "\n".join(lines).strip()


def frames_of(p):
    """Main frame first, then embedded ones (Greenhouse/Lever forms live in iframes)."""
    out = [p.main_frame]
    for f in p.frames:
        if f is p.main_frame:
            continue
        u = f.url or ""
        if not u or u == "about:blank" or re.search(r"recaptcha|hcaptcha|doubleclick|googletagmanager|facebook\.com/tr|analytics", u):
            continue
        out.append(f)
    return out


async def all_fields(p):
    res = []
    for fi, f in enumerate(frames_of(p)):
        try:
            got = await f.evaluate(_FIELDS_JS)
        except Exception:
            continue
        for x in got:
            x["frame"] = fi
            res.append(x)
    return res


async def all_clickables(p):
    res = []
    for fi, f in enumerate(frames_of(p)):
        try:
            got = await f.evaluate(_CLICKABLE_JS)
        except Exception:
            continue
        for x in got:
            x["frame"] = fi
            res.append(x)
    return res


async def page_text(p, selector=""):
    parts = []
    for fi, f in enumerate(frames_of(p)):
        try:
            t = await f.evaluate(_TEXT_JS, selector or "")
        except Exception:
            continue
        if t is None:
            continue
        t = squeeze(t)
        if not t:
            continue
        parts.append(t if fi == 0 else f"[embedded frame {f.url[:100]}]\n{t}")
    if selector and not parts:
        return None
    return "\n\n".join(parts)


async def headings(p):
    try:
        return await p.evaluate("""[...document.querySelectorAll('h1,h2,h3')].filter(e => e.offsetParent)
            .map(e => e.innerText.replace(/\\s+/g, ' ').trim()).filter(Boolean).slice(0, 12)""")
    except Exception:
        return []


def empty_required(fields):
    return [f["label"] for f in fields if f.get("required") and f.get("value") in ("", None, "unchecked")]


def field_line(f):
    bits = [f["type"]]
    if f.get("required"):
        bits.append("required")
    if f.get("hidden"):
        bits.append("hidden file input")
    line = f"- {f['label'] or '(no label)'} [{', '.join(bits)}]"
    if f.get("value"):
        line += f": {f['value']!r}"
    if f.get("options"):
        line += " options: " + " | ".join(f["options"][:10])
    return line


async def summary(p):
    """What a person would see at a glance: title, headings, the form, and the start of the text."""
    out = {"url": p.url}
    try:
        out["title"] = await p.title()
    except Exception:
        out["title"] = ""
    out["headings"] = await headings(p)
    fields = await all_fields(p)
    out["field_count"] = len(fields)
    out["fields"] = [field_line(f) for f in fields[:30]]
    out["empty_required"] = empty_required(fields)[:20]
    text = await page_text(p) or ""
    out["text"] = text[:SUMMARY_TEXT]
    out["text_len"] = len(text)
    out["frames"] = [f.url[:120] for f in frames_of(p)[1:]][:5]
    return out


# --- finding things -----------------------------------------------------------

def norm(s):
    return re.sub(r"[\s*:() ]+", " ", str(s or "")).strip().casefold()


def candidates(what, labels, n=8):
    labels = [l for l in dict.fromkeys(l for l in labels if l)]
    w = norm(what)
    scored = []
    for l in labels:
        nl = norm(l)
        s = difflib.SequenceMatcher(None, w, nl).ratio()
        if w and (w in nl or nl in w):
            s += 0.5
        if set(w.split()) & set(nl.split()):
            s += 0.2
        scored.append((s, l))
    scored.sort(key=lambda x: -x[0])
    return [l for _, l in scored[:n]]


async def first_visible(loc, allow_hidden=False):
    try:
        n = min(await loc.count(), 6)
    except Exception:
        return None
    for i in range(n):
        el = loc.nth(i)
        try:
            if allow_hidden or await el.is_visible():
                return el
        except Exception:
            continue
    return None


async def find_field(p, what):
    """A form control by its label: Playwright's own label matching in every
    frame first, then our label guess (same as the field list shows)."""
    if what.startswith("css:"):
        for f in frames_of(p):
            el = await first_visible(f.locator(what[4:]), allow_hidden=True)
            if el is not None:
                return el, None
        return None, None
    frs = frames_of(p)
    for exact in (True, False):
        for f in frs:
            for loc in (f.get_by_label(what, exact=exact), f.get_by_placeholder(what, exact=exact),
                        f.get_by_role("combobox", name=what, exact=exact)):
                el = await first_visible(loc)
                if el is not None:
                    return el, None
    fields = await all_fields(p)
    w = norm(what)
    best = [x for x in fields if norm(x["label"]) == w] or [x for x in fields if w and w in norm(x["label"])]
    if best:
        x = best[0]
        return frs[x["frame"]].locator(f'[data-sc-f="{x["i"]}"]').first, x
    for f in frs:  # name / id attributes
        el = await first_visible(f.locator(f'[name="{what}"], [id="{what}"]'), allow_hidden=True)
        if el is not None:
            return el, None
    return None, fields


async def find_clickable(p, what):
    if what.startswith("css:"):
        for f in frames_of(p):
            el = await first_visible(f.locator(what[4:]))
            if el is not None:
                return el
        return None
    kinds = ["button", "link", "checkbox", "radio", "tab", "menuitem", "option"]
    frs = frames_of(p)
    for exact in (True, False):
        for f in frs:
            for k in kinds:
                el = await first_visible(f.get_by_role(k, name=what, exact=exact))
                if el is not None:
                    return el
            for loc in (f.get_by_label(what, exact=exact), f.get_by_text(what, exact=exact)):
                el = await first_visible(loc)
                if el is not None:
                    return el
    return None


_TAP_JS = """e => {
  e.scrollIntoView({block: 'center'});
  const r = e.getBoundingClientRect(), o = {bubbles: true, cancelable: true, view: window,
    clientX: r.x + r.width / 2, clientY: r.y + r.height / 2, button: 0};
  e.dispatchEvent(new PointerEvent('pointerdown', o)); e.dispatchEvent(new MouseEvent('mousedown', o));
  if (e.focus) e.focus();
  e.dispatchEvent(new PointerEvent('pointerup', o)); e.dispatchEvent(new MouseEvent('mouseup', o));
  e.click();
}"""


async def tap(el):
    """A DOM click with the pointer/mouse events around it: ~10 ms, where a
    Playwright click in a background tab takes ~1 s (it waits for the element
    to be painted still). For checkboxes, radios and dropdown options."""
    await el.evaluate(_TAP_JS)


async def click_el(el):
    """A real click for buttons and links (popups and file choosers need one)."""
    try:
        await el.click(timeout=5000)
    except Exception as e:
        if "Timeout" not in type(e).__name__ and "timeout" not in str(e).lower():
            raise
        await tap(el)


# --- filling ------------------------------------------------------------------

def _no(v):
    return str(v).strip().lower() in ("no", "off", "false", "0", "uncheck", "unchecked")


_COMBO_VALUE_JS = """e => {
  if (e.value) return e.value;
  let n = e;
  for (let k = 0; k < 4 && n; k++) {
    n = n.parentElement;
    const sv = n && n.querySelector('[class*=single-value],[class*=singleValue],[class*=multi-value__label],[class*=multiValue]');
    if (sv) return sv.innerText;
  }
  return '';
}"""


async def visible_options(p):
    out = []
    for f in frames_of(p):
        loc = f.get_by_role("option")
        try:
            n = min(await loc.count(), 40)
        except Exception:
            continue
        for i in range(n):
            o = loc.nth(i)
            try:
                if await o.is_visible():
                    out.append((((await o.inner_text()) or "").strip(), o))
            except Exception:
                continue
    return out


async def pick_option(p, el, value):
    """Comboboxes (React-Select, Greenhouse/Ashby dropdowns): open, type, pick the
    option that matches. Returns (ok, what it shows now)."""
    value = str(value)
    await tap(el)
    try:
        await el.fill(value, timeout=3000)
    except Exception:
        try:
            await el.press_sequentially(value, delay=10, timeout=5000)
        except Exception:
            await p.keyboard.type(value, delay=10)
    want = norm(value)
    end = time.time() + 3.0
    choice = None
    while time.time() < end and choice is None:  # options often load from the network
        await asyncio.sleep(0.15)
        opts = await visible_options(p)
        if not opts:
            continue
        exact = [o for t, o in opts if norm(t) == want]
        starts = [o for t, o in opts if norm(t).startswith(want)]
        contains = [o for t, o in opts if want and want in norm(t)]
        if exact or starts or contains:
            choice = (exact or starts or contains)[0]
        elif len(opts) == 1 or time.time() > end - 1.5:
            texts = [t for t, _ in opts]
            best = candidates(value, texts, 1)
            if len(opts) == 1 or (best and difflib.SequenceMatcher(None, want, norm(best[0])).ratio() > 0.6):
                choice = opts[texts.index(best[0])][1] if best else opts[0][1]
    if choice is None:
        try:
            await el.press("Escape")
        except Exception:
            pass
        return False, ""
    await tap(choice)
    await asyncio.sleep(0.1)
    try:
        now = await el.evaluate(_COMBO_VALUE_JS)
    except Exception:
        now = ""
    return True, (now or "").strip()


async def read_value(el):
    try:
        return await el.evaluate("""e => e.tagName === 'SELECT' ? ((e.selectedOptions[0] || {}).text || '') :
            (['checkbox', 'radio'].includes(e.type) ? (e.checked ? 'checked' : 'unchecked') :
             (e.type === 'file' ? [...(e.files || [])].map(f => f.name).join(', ') :
              ('value' in e ? e.value : e.innerText)))""")
    except Exception:
        return ""


async def fill_one(p, label, value):
    """Returns (now, None) or (None, error_with_candidates)."""
    el, info = await find_field(p, label)
    if el is None:
        # A radio group by its question: pick the answer inside it.
        for f in frames_of(p):
            for grp in (f.get_by_role("radiogroup", name=label), f.get_by_role("group", name=label),
                        f.locator("fieldset").filter(has=f.locator("legend", has_text=label))):
                g = await first_visible(grp)
                if g is None:
                    continue
                for loc in (g.get_by_label(str(value), exact=True), g.get_by_label(str(value)),
                            g.get_by_role("radio", name=str(value)), g.get_by_text(str(value), exact=True)):
                    opt = await first_visible(loc)
                    if opt is not None:
                        await tap(opt)
                        return str(value), None
        fields = info if isinstance(info, list) else await all_fields(p)
        return None, {"label": label, "candidates": candidates(label, [x["label"] for x in fields])}
    kind = await el.evaluate("""e => e.tagName === 'SELECT' ? 'select' :
        ((e.getAttribute('role') === 'combobox' || (e.getAttribute('aria-autocomplete') || '') !== '' ||
          e.getAttribute('aria-haspopup') === 'listbox') ? 'combobox' : (e.type || e.tagName).toLowerCase())""")
    if info and info.get("type") == "radio":
        # Pick the answer inside THIS question's group (every group has a "Yes").
        frame = frames_of(p)[info["frame"]]
        picked = await frame.evaluate("([i, want]) => {" + _LABEL_JS + r"""
return (() => {
          const first = document.querySelector(`[data-sc-f="${i}"]`);
          if (!first) return null;
          const opts = first.name ? [...document.querySelectorAll(`input[type=radio][name="${CSS.escape(first.name)}"]`)] : [first];
          const n = s => s.replace(/[\s*]+/g, ' ').trim().toLowerCase();
          const w = n(want);
          const o = opts.find(o => n(window.__scLabel(o)) === w) || opts.find(o => n(window.__scLabel(o)).startsWith(w))
                    || opts.find(o => w && n(window.__scLabel(o)).includes(w));
          if (!o) return null;
          o.setAttribute('data-sc-pick', '1');
          return window.__scLabel(o);
        })();
        }""", [info["i"], str(value)])
        if not picked:
            return None, {"label": label, "candidates": info.get("options") or [], "why": f"no answer {value!r}"}
        target = frame.locator('[data-sc-pick="1"]').first
        await tap(target)
        if not await target.evaluate("e => e.checked"):
            await click_el(target)
        try:
            await frame.evaluate("document.querySelectorAll('[data-sc-pick]').forEach(e => e.removeAttribute('data-sc-pick'))")
        except Exception:
            pass
        return picked, None
    if kind == "select":
        opts = await el.evaluate("e => [...e.options].map(o => o.text.trim())")
        w = norm(value)
        pick = ([o for o in opts if norm(o) == w] or [o for o in opts if norm(o).startswith(w)]
                or [o for o in opts if w and w in norm(o)] or [o for o in candidates(value, opts, 1)
                if difflib.SequenceMatcher(None, w, norm(o)).ratio() > 0.6])
        if not pick:
            return None, {"label": label, "candidates": opts[:15], "why": f"no option {value!r}"}
        await el.select_option(label=pick[0], timeout=4000)
    elif kind in ("checkbox", "radio"):
        want_on = not _no(value)
        if await el.evaluate("e => e.checked") != want_on:
            await tap(el)
        if await el.evaluate("e => e.checked") != want_on:  # a custom box that hides the input
            await click_el(el)
    elif kind == "file":
        return None, {"label": label, "candidates": [], "why": "that's a file field: put it under \"files\""}
    elif kind == "combobox":
        ok, now = await pick_option(p, el, value)
        if not ok:
            opts = [t for t, _ in await visible_options(p)][:12]
            return None, {"label": label, "candidates": opts, "why": f"no choice like {value!r} in that dropdown"}
        return now or str(value), None
    else:
        try:
            await el.fill(str(value), timeout=4000)
        except Exception:
            await click_el(el)
            await el.press_sequentially(str(value), delay=5)
    return await read_value(el), None


async def upload_one(p, label, path):
    if not os.path.exists(os.path.expanduser(path)):
        return None, {"label": label, "candidates": [], "why": f"no file {path} on the Dot PC"}
    path = os.path.expanduser(path)
    el, info = await find_field(p, label)
    ok = False
    if el is not None:
        try:
            ok = await el.evaluate("e => e.type === 'file'")
        except Exception:
            ok = False
        if not ok:  # a label/button next to the hidden input
            try:
                inner = el.locator("xpath=ancestor-or-self::*[.//input[@type='file']][1]//input[@type='file']").first
                if await inner.count():
                    el, ok = inner, True
            except Exception:
                pass
    if not ok:
        fields = info if isinstance(info, list) else await all_fields(p)
        files = [x for x in fields if x["type"] == "file"]
        w = norm(label)
        pick = [x for x in files if w and (w in norm(x["label"]) or norm(x["label"]) in w)] or (files if len(files) == 1 else [])
        if not pick:
            return None, {"label": label, "candidates": [x["label"] for x in files] or ["(no file inputs on the page)"]}
        el = frames_of(p)[pick[0]["frame"]].locator(f'[data-sc-f="{pick[0]["i"]}"]').first
    await el.set_input_files(path, timeout=8000)
    return "attached " + os.path.basename(path), None


# --- ops ----------------------------------------------------------------------

async def op_goto(p, req):
    before = p.url
    await p.goto(req["url"], wait_until="domcontentloaded", timeout=30000)
    await settle(p, before)
    return await summary(p)


async def op_read(p, req):
    mode = req.get("mode") or "text"
    find = str(req.get("find") or "")
    start = max(0, int(req.get("start") or 0))
    out = {"url": p.url, "title": await p.title()}
    if mode == "summary":
        return await summary(p)
    if mode == "fields":
        fields = await all_fields(p)
        if find:
            fields = [x for x in fields if norm(find) in norm(x["label"])] or fields
        out["total"] = len(fields)
        out["fields"] = [field_line(f) for f in fields[start:start + 120]]
        out["empty_required"] = empty_required(fields)
        out["frames"] = [f.url[:120] for f in frames_of(p)[1:]][:5]
        return out
    if mode == "links":
        items = await all_clickables(p)
        if find:
            items = [x for x in items if norm(find) in norm(x["text"]) or norm(find) in x["href"].casefold()] or items
        out["total"] = len(items)
        out["links"] = items[start:start + 200]
        return out
    text = await page_text(p, req.get("selector") or "")
    if text is None:
        out["error"] = f"nothing matches the selector {req.get('selector')!r}"
        return out
    out["total"] = len(text)
    if find:
        hits, i = [], 0
        low, f = text.casefold(), find.casefold()
        while len(hits) < 8:
            j = low.find(f, i)
            if j < 0:
                break
            hits.append(f"[at {j}] …{text[max(0, j - 400):j + len(find) + 600]}…")
            i = j + len(find) + 600
        out["text"] = "\n\n".join(hits) if hits else ""
        out["found"] = len(hits)
        return out
    limit = max(500, min(int(req.get("limit") or TEXT_PAGE), 20000))
    out["start"] = start
    out["text"] = text[start:start + limit]
    if start + limit < len(text):
        out["next"] = start + limit
    return out


async def op_fill(p, req):
    fields = req.get("fields") or {}
    files = req.get("files") or {}
    out = {"filled": []}
    for label, value in fields.items():
        now, miss = await fill_one(p, str(label), "" if value is None else value)
        if miss:
            out["missed"] = miss
            break
        out["filled"].append({"label": label, "now": str(now)[:120]})
    if "missed" not in out:
        for label, path in files.items():
            now, miss = await upload_one(p, str(label), str(path))
            if miss:
                out["missed"] = miss
                break
            out["filled"].append({"label": label, "now": now})
    if "missed" not in out and req.get("then_click"):
        el = await find_clickable(p, str(req["then_click"]))
        if el is None:
            out["missed"] = {"label": req["then_click"], "candidates": candidates(
                req["then_click"], [x["text"] for x in await all_clickables(p)]), "why": "nothing to click"}
        else:
            before = p.url
            await click_el(el)
            await settle(p, before)
            out["clicked"] = req["then_click"]
    await asyncio.sleep(0.15)  # let validation messages render
    fields_now = await all_fields(p)
    out["empty_required"] = empty_required(fields_now)[:25]
    invalid = []
    for f in frames_of(p):
        try:
            invalid += await f.evaluate("() => {" + _LABEL_JS + r"""
              return [...document.querySelectorAll(':invalid')].filter(e => e.matches('input,select,textarea'))
                .map(e => window.__scLabel(e) || window.__scLabel(e.parentElement.querySelector('input:not([aria-hidden=true])') || e))
                .filter(Boolean).slice(0, 15); }""")
        except Exception:
            pass
    if invalid:
        out["invalid"] = list(dict.fromkeys(invalid))[:15]
    if out.get("clicked"):
        out["page"] = await summary(p)
    out["url"] = p.url
    out["title"] = await p.title()
    return out


async def op_click(p, req):
    what = str(req.get("text") or "")
    el = await find_clickable(p, what)
    if el is None:
        return {"error": f"nothing called {what!r} to click", "candidates": candidates(
            what, [x["text"] for x in await all_clickables(p)] + [x["label"] for x in await all_fields(p)])}
    before = p.url
    await click_el(el)
    await settle(p, before)
    return await summary(p)


async def op_upload(p, req):
    now, miss = await upload_one(p, str(req.get("field") or ""), str(req.get("path") or ""))
    if miss:
        return {"error": f"no file field {miss['label']!r}" + (f" ({miss['why']})" if miss.get("why") else ""),
                "candidates": miss.get("candidates", [])}
    return {"now": now, "url": p.url}


async def handle(req):
    op = req.get("op")
    if op == "ping":
        return {"ok": True, "pid": os.getpid(), "jobs": sorted(pages)}
    job = safe_job(req.get("job"))
    if op == "close":
        p = await job_page(job, create=False)
        pages.pop(job, None)
        try:
            os.remove(os.path.join(TABS, job))
        except OSError:
            pass
        if p is None:
            return {"ok": True, "closed": False}
        if sum(len(c.pages) for c in browser.contexts) <= 1:
            await p.goto("about:blank")  # never close the last tab: Chrome would quit
        else:
            await p.close()
        return {"ok": True, "closed": True}
    lock = job_locks.setdefault(job, asyncio.Lock())
    async with lock:
        p = await job_page(job, create=(op != "url"))
        if op == "url":
            return {"url": p.url if p else ""}
        fn = {"goto": op_goto, "read": op_read, "fill": op_fill, "click": op_click, "upload": op_upload}.get(op)
        if fn is None:
            return {"error": f"unknown op {op!r}"}
        return await fn(p, req)


async def serve_conn(reader, writer):
    try:
        line = await reader.readline()
        req = json.loads(line or b"{}")
        t = time.time()
        try:
            res = await handle(req)
        except Exception as e:
            msg = str(e).splitlines()[0][:300] if str(e) else ""
            if browser is not None and not browser.is_connected():
                msg += " (lost Chrome; reconnecting on the next call)"
            res = {"error": f"{type(e).__name__}: {msg}"}
            log("error", req.get("op"), traceback.format_exc()[-800:])
        log(req.get("op"), req.get("job"), f"{time.time() - t:.2f}s", "ERR" if res.get("error") else "")
        writer.write(json.dumps(res, ensure_ascii=False).encode() + b"\n")
        await writer.drain()
    except Exception:
        log("conn", traceback.format_exc()[-400:])
    finally:
        try:
            writer.close()
        except Exception:
            pass


async def main():
    import fcntl
    os.makedirs(TABS, exist_ok=True)
    os.chmod(DIR, 0o700)
    lockf = open(os.path.join(DIR, "page.lock"), "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log("another page server is running")
        return
    if os.path.exists(SOCK):
        os.remove(SOCK)
    server = await asyncio.start_unix_server(serve_conn, path=SOCK, limit=8 * 1024 * 1024)
    os.chmod(SOCK, 0o600)
    log("listening on", SOCK, "pid", os.getpid())
    try:
        await connect()
    except Exception as e:
        log("Chrome not reachable yet:", e)
    async with server:
        await server.serve_forever()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        sys.exit(0)
