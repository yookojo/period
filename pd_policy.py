import os
"""Full auto: what still needs the user's OK.

In full auto Period works without asking, with two exceptions the user
named ("only verification with money and things that are crazy"):

- money: paying, buying, subscribing, transferring, typing a card number;
- crazy: things that are hard or impossible to undo and hit the whole PC or an
  account: formatting a drive, wiping the user folder or C:\\, deleting backups,
  editing boot or security settings, turning off antivirus, changing a password
  or 2FA, deleting an account, posting publicly as the user.

needs_human() returns a short plain reason when one applies, else None.
Pure functions only, so it is easy to test (test_policy.py, test_dots.py).

The money check looks for money *actions* (a pay/buy button, a card number, a
checkout page), not money words: job forms are full of "desired pay", "pay
transparency" and "expected salary", and scripts are full of `git checkout`.
"""
import json
import re
import unicodedata
from urllib.parse import urlparse

# Buttons and phrases that spend money when clicked or typed. Bare "pay",
# "payment", "billing", "checkout" and "security code" are left out on purpose:
# they show up on every job application and in code.
MONEY_WORDS = re.compile(
    r"\b(place (your |my |the )?order|complete (your |my |the )?(order|purchase)|confirm (your |my |the )?purchase|"
    r"buy now|buy it now|buy (this|it)\b|add to (cart|basket|bag)|purchase (now|it|this)|make (a |the )?purchase|"
    r"(proceed|continue|go) to (checkout|payment)|check ?out now|secure checkout|"
    r"pay now|pay \$\s?\d+|pay with (card|paypal|venmo|apple pay|google pay|my card)|confirm (and )?pay|"
    r"submit payment|make (a |the )?payment|send payment|complete payment|"
    r"card number|credit card|debit card|cvv|cvc|card expir\w*|name on card|"
    r"subscribe( now)?|start (my |your |a )?(free )?(trial|subscription)|upgrade (plan|to \w+)|free trial|"
    r"venmo|zelle|cash ?app|paypal|wire transfer|bank transfer|send money|request money|"
    r"donate|make a donation|send (bitcoin|btc|eth|crypto)|wallet address|gift card)\b", re.I)

# Pay words that are about a job, never about spending money.
_SAFE_PAY = re.compile(
    r"\b(pay (transparency|range|band|scale|rate|grade|equity)|(desired|expected|target|base|hourly) "
    r"(pay|salary|compensation|wage)|salary (expectations?|range)|compensation (range|expectations?))\b", re.I)

# Payment hosts and store paths. "checkout" only counts as its own path segment
# (shop.com/checkout) or as a checkout subdomain (checkout.stripe.com), so
# checkout.com (a company) and jobs.lever.co/checkout (its job board) don't.
MONEY_URL = re.compile(
    r"(/cart\b|/basket\b|/payments?\b|/pay\b|/billing\b|/subscribe\b|/purchase\b|/order/review|"
    r"/gp/buy|/spc/|place.?order|/buy/|"
    r"paypal\.com|venmo\.com|stripe\.com/pay|pay\.google|//buy\.|/donate\b)", re.I)
_JOB_HOSTS = re.compile(r"(^|\.)(lever\.co|greenhouse\.io|ashbyhq\.com|myworkdayjobs\.com|workable\.com|"
                        r"smartrecruiters\.com|linkedin\.com|indeed\.com|wellfound\.com|handshake\.com|"
                        r"joinhandshake\.com|bamboohr\.com|icims\.com|jobvite\.com)$", re.I)
_URL_IN = re.compile(r"https?://[^\s'\"<>()\[\]{}]+", re.I)

# Card-shaped digit groups: 4-4-4-4(-1..3), 4-6-5/4-6-4 (Amex/Diners), or 13-19
# digits in a row starting with 2-6 (every big card network does; ms
# timestamps start with 1). Separators: space, NBSP, thin spaces, dot, dash.
_SEP = r"[ \u00a0\u2007\u2009\u202f.\-]"
CARD_NUMBER = re.compile(
    r"(?<![\d.\-])(?:\d{4}(" + _SEP + r")\d{4}\1\d{4}\1\d{4}(?:\1\d{1,3})?"
    r"|\d{4}(" + _SEP + r")\d{6}\2\d{4,5}"
    r"|[2-6]\d{12,18})(?!\d|[.\-]\d)")

# Labels of fields that only exist to take payment details.
CARD_FIELD = re.compile(r"\b(card ?number|credit card|debit card|cvv2?|cvc2?|cvn|card verification|"
                        r"card security|name on (the )?card|card ?holder|card expir\w*)\b", re.I)
# Labels that are payment details only when the page is a checkout page.
CHECKOUT_FIELD = re.compile(r"\b(expir\w*|exp\.? ?date|mm ?/ ?yy|billing|security code|zip|postal)\b", re.I)

# Scripts that drive a browser (and so act on whatever page is open).
DRIVES_BROWSER = re.compile(r"playwright|puppeteer|selenium|connect_over_cdp|:9222|9222/|xdotool|"
                            r"chrome-remote-interface|\bpage\.(click|fill|type|press)\b", re.I)

# What a delegated task is asking for: an intent to spend, not a money word.
_INTENT = re.compile(
    r"\b(buy|purchase|pay for|pay (the |my |his |her |their |a |an |our )?([\w-]+ )?(bill|invoice|balance|rent|fee|tuition|tab)s?|"
    r"pay \$\s?\d+|pay (him|her|them|me|someone)|"
    r"order (me |us )?(a |an |some |another |more |\d+ )?(?!(by|of|to|in|and|or|for|from|is|was|status|history|"
    r"number|confirmation|id|details|page|form|the (list|results|rows|items|columns|files|jobs|lines|entries|output))\b)"
    r"(?=[a-z0-9])\w+|place (an |the |my |your )?order|"
    r"check ?out (my |the |our )?(cart|basket|bag|order)|complete (my |the )?(checkout|order|purchase)|"
    r"subscribe (me )?to|sign (me )?up for (a )?paid|donate|make a donation|"
    r"send (money|cash|payment|\$\s?\d+)|transfer (money|funds|\$\s?\d+)|wire (money|funds|\$\s?\d+)|"
    r"(venmo|zelle|cash ?app) (me|him|her|them|someone|\w+ \$\s?\d+|\$\s?\d+))\b", re.I)
_NOT_ORDER = re.compile(r"\b(in|the|a|an|my|your|his|her|their|our|its|each|every|sort|reverse|chronological|"
                        r"alphabetical|same|random|word|tab|pecking|"
                        r"that|this|which|what|any|right|correct|original)\s+$", re.I)
_NEGATED = re.compile(r"\b(don'?t|do not|never|no|without|nor|not|avoid|stop before|before you)\b[^.;\n]{0,25}$", re.I)

SECURITY_WORDS = re.compile(
    r"\b(change|reset|update|new|remove|disable|turn off)\s+(my |your |the )?"
    r"(password|passcode|pin|2fa|two[- ]factor|mfa|authenticator|recovery (email|phone|codes?)|"
    r"security (questions?|settings))\b|\b(delete|close|deactivate)\s+(my |your |the |this )?account\b", re.I)

SECURITY_OFF_WORDS = re.compile(
    r"\b(remove|disable|turn(ing)? off|deactivate|unenroll)\s+(my |your |the )?"
    r"(2fa|two[- ]factor|two[- ]step|mfa|multi[- ]factor|authenticator|recovery (email|phone|codes?))\b"
    r"|\b(delete|close|deactivate)\s+(my |your |the |this )?account\b", re.I)

PUBLIC_POST_TOOLS = {"discord_send"}
PUBLIC_POST_WORDS = re.compile(
    r"\b(tweet|post (it |this )?(publicly|to (twitter|x|instagram|facebook|reddit|tiktok|linkedin)))\b", re.I)

# Commands that can wreck the PC itself. Normal deletes inside a project are
# fine in full auto; these are not.
_HOME_OR_ROOT = (r"(['\"]?(c:\\?|c:/|~|\$home|\$env:userprofile|%userprofile%|/|/home/\w+|c:\\users\\\w+)"
                 r"[\\/]?\*?(\.\*)?['\"]?)")
CRAZY_COMMANDS = [
    (re.compile(r"\bformat(-volume)?\s+[a-z]:|\bformat-volume\b|mkfs\.|\bdiskpart\b|\bclear-disk\b|\binitialize-disk\b", re.I),
     "formats a drive"),
    (re.compile(r"\brm\s+(-[a-z]*\s+)*" + _HOME_OR_ROOT + r"(\s|$)", re.I), "deletes your whole home folder or drive"),
    (re.compile(r"\bremove-item\b[^|;]*\s" + _HOME_OR_ROOT + r"(\s|$)[^|;]*-recurse|\bremove-item\b[^|;]*-recurse[^|;]*\s"
                + _HOME_OR_ROOT + r"(\s|$)", re.I), "deletes your whole home folder or drive"),
    (re.compile(r"\b(rd|rmdir)\s+/s\s+(/q\s+)?" + _HOME_OR_ROOT + r"(\s|$)", re.I), "deletes your whole home folder or drive"),
    (re.compile(r"\bvssadmin\b.*\bdelete\b|\bwbadmin\b.*\bdelete\b|\bcipher\s+/w", re.I), "deletes backups or wipes free space"),
    (re.compile(r"\bbcdedit\b|\bbootrec\b|\breagentc\b", re.I), "changes how Windows boots"),
    (re.compile(r"\breg(\.exe)?\s+delete\s+hk(lm|ey_local_machine)|remove-item\s+['\"]?hklm:", re.I),
     "deletes system registry keys"),
    (re.compile(r"set-mppreference\b.*-disable|\bdisable-windowsoptionalfeature\b.*defender|"
                r"netsh\s+advfirewall\s+set\s+\w+\s+state\s+off|\bsc(\.exe)?\s+(stop|delete|config)\s+windefend", re.I),
     "turns off antivirus or the firewall"),
    (re.compile(r"\btakeown\b.*\bc:\\windows|\bicacls\s+c:\\windows", re.I), "changes ownership of Windows system files"),
    (re.compile(r"\bnet\s+user\b.*\s(/delete|/add)|\bremove-localuser\b|\bset-localuser\b.*-password", re.I),
     "changes Windows user accounts"),
    (re.compile(r":\(\)\s*{\s*:\s*\|\s*:\s*&\s*}\s*;\s*:"), "fork bomb"),
    (re.compile(r"\bdrop\s+database\b", re.I), "drops a whole database"),
]


# ~/jobs/AUDIT_PASS on the Dot PC is the application lanes' audit sign-off: overnight_run.sh / lanes_run.sh only start
# when it is newer than every ~/tools/*.py. RULES.md: only the owner or the main Claude Code session writes it. Dot must
# not sign off its own code (11-04 17:09 it "Refreshed AUDIT_PASS (Dot's call ...)"; 11-05 12:18 and 17:18 it was
# rewritten with no logged writer). Reading it (ls, stat, test -e, [ -nt ], cat) is fine.
_AUDIT_RE = re.compile(r"AUDIT_PASS", re.I)
_AUDIT_READ_CMDS = {"ls", "stat", "test", "[", "[[", "cat", "head", "tail", "wc", "file", "readlink", "realpath",
                    "find", "date", "echo", "printf", "grep", "egrep", "fgrep", "rg", "sed", "awk", "less", "diff",
                    "md5sum", "sha1sum", "sha256sum", "basename", "dirname"}
# A script or file that writes it: touch/cp/mv/rm/ln/a redirect to it, or Python's touch()/write_text()/utime/open(...,"w").
_AUDIT_WRITE_IN_TEXT = re.compile(
    r"\b(touch|cp|mv|rm|ln|install|truncate|tee)\b[^\n;|&]{0,120}AUDIT_PASS|>>?\s*['\"]?[^\s'\"]*AUDIT_PASS|"
    r"AUDIT_PASS[^\n]{0,60}(\.touch\(|\.write_(text|bytes)\(|\.unlink\(|\.rename\(|\.replace\()|"
    r"(utime|os\.remove|os\.rename|os\.replace|shutil\.\w+)\([^\n)]{0,120}AUDIT_PASS|"
    r"open\([^\n)]{0,120}AUDIT_PASS[^\n)]{0,20},\s*['\"][wax+]", re.I)
_SHELL_WORDS = re.compile(r"^(?:(?:do|then|else|elif|if|while|until|!|\{|\(|time)\s+)+")


def _audit_segment_reads(seg):
    seg = _SHELL_WORDS.sub("", seg.strip())
    seg = re.sub(r"^(?:[A-Za-z_]\w*=\S*\s+)+(?=\S)", "", seg)  # LC_ALL=C ls ... (a bare P=.../AUDIT_PASS stays)
    words = seg.split()
    if not words:
        return True
    first = words[0].rsplit("/", 1)[-1]
    if first not in _AUDIT_READ_CMDS or re.search(r">|\btee\b|-exec|-execdir|-delete|-ok\b", seg):
        return False  # touch, cp, mv, rm, ln, python, a redirect into it, find -exec/-delete ...
    if first == "sed" and re.search(r"\s(-i\S*|--in-place)", seg):
        return False
    if first == "awk" and re.search(r"\bsystem\s*\(|\|\s*\"", seg):
        return False
    if first == "date":
        return bool(re.search(r"\s(-r|--reference)\b", seg))  # date -r FILE reads; date -s sets the clock
    return True  # (echo "--- AUDIT_PASS" only prints the name: its redirects were ruled out above)


def audit_pass_write(tool, args):
    """Why this call would write, touch, move or delete ~/jobs/AUDIT_PASS (the lanes' audit sign-off), or None.
    Commands that only read it (ls, stat, test -e, [ "$f" -nt AUDIT_PASS ], cat) are fine."""
    if not isinstance(args, dict):
        return None
    why = ("don't write ~/jobs/AUDIT_PASS by hand. To sign off your own ~/tools changes (owner 11-06: full reign), "
           "run: bash ~/tools/self_audit.sh. It runs the checks and writes AUDIT_PASS only if they all pass")
    if tool in ("run_command", "vm_run"):
        cmd = _norm(args.get("command") or "")
        if not _AUDIT_RE.search(cmd):
            return None
        segs = re.split(r"\|\||&&|\$\(|`|[;|&\n()]", cmd)
        return why if any(_AUDIT_RE.search(s) and not _audit_segment_reads(s) for s in segs) else None
    if tool in ("write_file", "edit_file", "vm_files", "vm_claude", "claude"):
        if tool == "vm_files" and str(args.get("action") or "").lower() in ("list", "ls", "get", "download", "read"):
            return None
        paths = " ".join(str(args.get(k) or "") for k in ("path", "file_path", "dest", "to", "target", "remote"))
        if (tool in ("write_file", "edit_file", "vm_files") and _AUDIT_RE.search(paths)) or \
                _writes_audit_pass(_blob(args)):
            return why  # the file itself, or a script / task that would write it
    return None


def _writes_audit_pass(text):
    """Text (a file's content, a delegated task) that writes AUDIT_PASS. "Never touch ~/jobs/AUDIT_PASS" doesn't."""
    for m in _AUDIT_WRITE_IN_TEXT.finditer(text or ""):
        before = text[max(0, m.start() - 40):m.start()]
        if re.search(r"\b(never|don'?t|do not|not|no|must not|mustn'?t|without)\b[^.;\n]{0,30}$", before, re.I):
            continue
        return True
    return False


def forbidden(tool, args):
    """A hard no for Dot's jobs (refused outright, not asked about), or None."""
    return audit_pass_write(tool, args)


def crazy_command(command, in_vm=False):
    if in_vm:
        return None  # the Dot PC is disposable: anything goes in there
    for pattern, reason in CRAZY_COMMANDS:
        if pattern.search(command or ""):
            return reason
    return None


def _norm(text):
    return unicodedata.normalize("NFKC", str(text or ""))


def is_money_url(url):
    """A checkout or payment page (not a store's home page, not a job board)."""
    url = _norm(url).strip()
    if not url:
        return False
    try:
        u = urlparse(url if "//" in url else "//" + url)
        host = (u.hostname or "").lower()
    except ValueError:
        return bool(MONEY_URL.search(url))
    path = u.path or ""
    if _JOB_HOSTS.search(host):
        return False  # jobs.lever.co/checkout is Checkout.com's job board
    if MONEY_URL.search(url):
        return True
    if re.search(r"(^|/)checkouts?(/|$|\.|-)", path, re.I):
        return True
    labels = host.split(".")
    # checkout.stripe.com, checkout.shopify.com - but not checkout.com itself
    return len(labels) > 2 and labels[0] == "checkout" and ".".join(labels[-2:]) != "checkout.com"


def card_numbers(text):
    """Card numbers in the text (card-shaped digit groups that pass the Luhn check)."""
    return [m.group(0) for m in CARD_NUMBER.finditer(_norm(text)) if _luhn_ok(m.group(0))]


def money_reason(text="", url=""):
    if url and is_money_url(url):
        return "this page is a checkout or payment page"
    text = _norm(text)
    if text and card_numbers(text):
        return "it types a card number"
    m = MONEY_WORDS.search(_SAFE_PAY.sub(" ", text))
    if m:
        return f"it involves money ({m.group(0).strip()})"
    return None


def _luhn_ok(raw):
    digits = [int(c) for c in raw if c.isdigit()]
    if not 13 <= len(digits) <= 19:
        return False
    total = 0
    for i, d in enumerate(reversed(digits)):
        if i % 2:
            d *= 2
            if d > 9:
                d -= 9
        total += d
    return total % 10 == 0


def spend_intent(text):
    """The task asks to spend money ("buy", "order a ...", "pay for", "donate"), or None.
    "Don't buy anything" and "in order to" don't count."""
    text = _norm(text)
    for m in _INTENT.finditer(text):
        before = text[max(0, m.start() - 40):m.start()]
        word = m.group(0).strip().lower()
        if word.startswith("order") and _NOT_ORDER.search(before):
            continue
        if _NEGATED.search(before):
            continue
        return f"it asks to spend money ({m.group(0).strip()})"
    return None


def _fill_money(args, page_url):
    """vm_fill: judged on the field labels and the page, not on what's typed
    (a cover letter can say "pay" all it likes)."""
    on_checkout = is_money_url(page_url)
    if on_checkout:
        return "this page is a checkout or payment page"
    labels, values = [], []
    for key in ("field", "label"):
        if args.get(key):
            labels.append(str(args[key]))
    if args.get("text") is not None:
        values.append(str(args["text"]))
    for key in ("fields", "files"):
        group = args.get(key)
        if isinstance(group, dict):
            labels += [str(k) for k in group]
            values += [str(v) for v in group.values() if isinstance(v, (str, int, float))]
        elif isinstance(group, list):  # [{"field": ..., "text": ...}, ...]
            for item in group:
                if isinstance(item, dict):
                    labels.append(str(item.get("field") or item.get("label") or ""))
                    values.append(str(item.get("text") or item.get("value") or ""))
    for label in labels:
        if CARD_FIELD.search(_norm(label)):
            return f"it fills in a payment field ({label.strip()[:40]})"
    if any(card_numbers(v) for v in values):
        return "it types a card number"
    click = str(args.get("then_click") or "")
    if click and MONEY_WORDS.search(_SAFE_PAY.sub(" ", _norm(click))):
        return f"it clicks a buy or pay button ({click.strip()[:40]})"
    return None


def _run_money(command, page_url=""):
    """vm_run: a card number in the script, a payment URL it goes to, or a
    browser-driving script while the open page is a checkout page."""
    if card_numbers(command):
        return "it types a card number"
    for url in _URL_IN.findall(_norm(command)):
        if is_money_url(url):
            return "it goes to a checkout or payment page"
    if page_url and is_money_url(page_url) and DRIVES_BROWSER.search(command):
        return "it drives the browser while it's on a checkout page"
    return None


# Tools whose arguments can spend money or touch account security.
ACTING_TOOLS = {
    "vm_click", "vm_type", "vm_key", "vm_open", "vm_fill",
    "tab_click", "tab_type", "tab_navigate", "tab_execute_js",
    "browser_click", "browser_type", "browser_navigate",
    "computer_click", "computer_type", "computer_key",
    "app_do", "mail_send", "email_send", "imessage_send", "discord_send", "claude", "vm_claude",
}
DELEGATE_TOOLS = {"claude", "vm_claude"}


def _blob(args):
    parts = []
    for v in args.values():
        if isinstance(v, (str, int, float)) and not isinstance(v, bool):
            parts.append(str(v))
        elif isinstance(v, list):
            parts += [str(x) for x in v if isinstance(x, (str, int, float)) and not isinstance(x, bool)]
    return _norm(" ".join(parts))


def needs_human(tool, args, page_url="", in_vm=False):
    """Why this tool call needs the user's OK in full auto, or None."""
    if not isinstance(args, dict):
        return None
    hard = forbidden(tool, args)
    if hard:
        return hard
    if str(tool).startswith("mac_"):  # 2026-11-11: the owner's Mac (pd_mac.py): same bar as his PC
        try:
            import pd_mac
            return pd_mac.policy(tool, args)
        except ImportError:
            return "the Mac tools aren't installed"
    if tool in ("run_command", "vm_run"):
        cmd = str(args.get("command") or "")
        crazy = crazy_command(cmd, in_vm=(tool == "vm_run" or in_vm))
        if crazy:
            return crazy
        return _run_money(cmd, page_url) if tool == "vm_run" else None
    if tool not in ACTING_TOOLS:
        return None
    # desc counts: a click is often only coordinates plus "Clicking Place your order".
    blob = _blob(args)
    if tool in ("vm_open", "tab_navigate", "browser_navigate"):
        url = str(args.get("url") or "")
        return money_reason(url=url)  # just opening a store is fine; only payment pages
    if tool in DELEGATE_TOOLS:
        reason = ("it types a card number" if card_numbers(blob) else None) or spend_intent(blob)
    elif tool == "vm_fill":
        reason = _fill_money(args, page_url)
    else:
        reason = money_reason(blob, page_url)
    if reason and tool in ("mail_send", "email_send", "imessage_send") and not card_numbers(blob):
        # Talking about money in a message is fine; sending card numbers is not.
        if not re.search(r"\b(send|pay|transfer|venmo|zelle)\b.{0,20}\$\s?\d", blob, re.I):
            reason = None
    if reason:
        return reason
    if SECURITY_WORDS.search(blob):
        # Owner 2026-10-29 ("not just for bot for anything this needs to be fully automated"): Dot's application
        # lane job resets job-site passwords and sets up two-step login itself. Turning 2FA off, removing recovery
        # options and closing accounts still need the owner.
        if not (os.environ.get("DOT_JOB_LABEL", "").startswith("Dot lane:") and not SECURITY_OFF_WORDS.search(blob)):
            return "it changes a password, 2FA or an account"
    if tool in PUBLIC_POST_TOOLS or PUBLIC_POST_WORDS.search(blob):
        return "it posts publicly as you"
    return None


def describe(tool, args):
    try:
        shown = {k: v for k, v in args.items() if k != "desc"}
        return f"{tool} {json.dumps(shown)[:300]}"
    except Exception:
        return tool
