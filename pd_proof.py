"""Proof before "done": what the records and the inbox say about a claim, checked by
code, not by a model.

When Dot is about to tell the owner it applied somewhere or sent something, this
looks up:
  - the application scripts' own results on Dot's PC (~/jobs/*_results.jsonl),
  - the confirmation logs (confirmed_log.txt, *_confirmed.jsonl),
  - the owner's Gmail over IMAP: "thank you for applying" mail and the Sent folder.

facts_for(text) -> Proof(lines, problems)
  lines:    facts for the second-opinion checker (authoritative, newest first)
  problems: claims the records flatly contradict, stated plainly; these are
            shown to the owner even when the checker can't be reached."""
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

JOBS = Path(os.environ.get("PERIOD_DOT_JOBS", r"\\wsl$\Ubuntu-24.04\home\dot\jobs"))
MAIL_CACHE_SEC = 120
# No double quotes: the IMAP search passes the query inside quotes of its own.
CONFIRM_QUERY = ("newer_than:3d {subject:(thank you for applying) subject:(thanks for applying) "
                 "subject:(application received) subject:(received your application) "
                 "subject:(thank you for your application) subject:(thank you for your interest) "
                 "subject:(thanks for your interest) subject:(application confirmation) subject:(your application)} "
                 "-subject:(security code)")
SUBMITTED = {"submitted", "unconfirmed", "check_email", "email_code"}

APPLIED_RE = re.compile(r"\b(applied|submitted|application (is |went )?(in|through|sent)|went (in|through)|"
                        r"sent (in )?(my |the |an |your )?applications?)\b", re.I)
SENT_RE = re.compile(r"\b(sent|emailed|went out|going out|on (its|their) way)\b", re.I)
NEGATED_RE = re.compile(r"\b(not|n['’]t|never|couldn['’]?t|didn['’]?t|wasn['’]?t|don['’]?t|doesn['’]?t|"
                        r"won['’]?t|isn['’]?t|can['’]?t|failed|blocked|stuck|captcha|skipp?ed|"
                        r"ineligible|will|going to|about to|next|try(ing)?|queued?|waiting|pending|need)\b", re.I)
NOISE_RE = re.compile(r"\b(inc|llc|ltd|corp(oration)?|co|company|the|technologies|group|holdings|labs?)\b\.?", re.I)


@dataclass
class Proof:
    lines: list = field(default_factory=list)
    problems: list = field(default_factory=list)


def _jsonl(path):
    out = []
    try:
        with open(path, encoding="utf-8") as f:
            for line in f:
                try:
                    out.append(json.loads(line))
                except ValueError:
                    pass
    except OSError:
        pass
    return out


def _names(company):
    c = re.sub(r"[^\w&' -]+", " ", company or "").strip()
    out = {c.lower()}
    short = re.sub(r"\s+", " ", NOISE_RE.sub("", c)).strip()
    if len(short) >= 3:
        out.add(short.lower())
    return [n for n in out if len(n) >= 3]


def mentions(text, company):
    t = " " + re.sub(r"\s+", " ", (text or "").lower()) + " "
    return any(re.search(r"(?<![\w-])" + re.escape(n) + r"(?![\w-])", t) for n in _names(company))


def applications(jobs=None):
    """company -> {"confirmed": [roles], "latest": {role: (status, ts, note)}} from the scripts' own records."""
    jobs = Path(jobs or JOBS)
    apps = {}

    def entry(company):
        return apps.setdefault(company, {"confirmed": [], "latest": {}})

    for p in sorted(jobs.glob("*_results.jsonl")):
        for j in _jsonl(p):
            if j.get("mode") == "dry" or not j.get("company"):
                continue
            ts = j.get("ts") or j.get("date") or ""
            role = j.get("role") or "?"
            prev = entry(j["company"])["latest"].get(role)
            if not prev or ts >= prev[1]:
                note = j.get("note") or j.get("blockers") or ", ".join(j.get("missing_required") or [])
                entry(j["company"])["latest"][role] = (str(j.get("status") or "").lower(), ts, str(note)[:120])
    for p in sorted(jobs.glob("*_confirmed.jsonl")):
        for j in _jsonl(p):
            if j.get("company"):
                entry(j["company"])["confirmed"].append(j.get("role") or "?")
    try:
        for line in (jobs / "confirmed_log.txt").read_text(encoding="utf-8").splitlines():
            parts = [x.strip() for x in line.split("|")]
            if len(parts) >= 3 and parts[0] == "CONFIRMED":
                entry(parts[1])["confirmed"].append(parts[2])
    except OSError:
        pass
    return apps


_mail_cache = {}


def _imap_search(query, count=60):
    """From/Subject of the newest matching mail across connected Gmail accounts, read-only, one FETCH per account."""
    import email as email_lib
    import pd_dots
    s = pd_dots.sc()
    out = []
    for address in s.email_accounts():
        conn = s._imap(address)
        try:
            conn.select('"[Gmail]/All Mail"', readonly=True)
            _typ, data = conn.uid("SEARCH", "X-GM-RAW", '"' + query.replace('"', "'") + '"')
            uids = (data[0] or b"").split()[-count:][::-1]
            if not uids:
                continue
            _typ, msgs = conn.uid("FETCH", b",".join(uids), "(BODY.PEEK[HEADER.FIELDS (FROM SUBJECT)])")
            for m in msgs or []:
                if isinstance(m, tuple):
                    h = email_lib.message_from_bytes(m[1])
                    out.append({"from": s._decode_header(h.get("From")), "subject": s._decode_header(h.get("Subject"))})
        finally:
            try:
                conn.logout()
            except Exception:
                pass
    return out


def _mail(query, count=60, search=None):
    """(from, subject) of recent matching mail in the owner's Gmail, or None if the inbox can't be read."""
    hit = _mail_cache.get(query)
    if hit and time.time() - hit[0] < MAIL_CACHE_SEC:
        return hit[1]
    try:
        rows = [(r.get("from", ""), r.get("subject", "")) for r in (search or _imap_search)(query, count=count)]
    except Exception as e:
        print(f"[proof] inbox: {e}", file=sys.stderr)
        return None
    _mail_cache[query] = (time.time(), rows)
    return rows


def _claim_sentences(text, pattern):
    return [s for s in re.split(r"(?<=[.!?;])\s+|\n+", text or "")
            if pattern.search(s) and not NEGATED_RE.search(s)]


def facts_for(text, jobs=None, search=None):
    proof = Proof()
    applied = _claim_sentences(text, APPLIED_RE)
    if applied:
        apps = applications(jobs)
        mail = _mail(CONFIRM_QUERY, count=100, search=search)
        claim_text = " ".join(applied)
        named = sorted({c for c in apps if mentions(claim_text, c)}, key=len, reverse=True)
        named = [c for c in named if not any(c != o and mentions(o, c) and mentions(claim_text, o) for o in named)]
        for company in named[:15]:
            info = apps[company]
            emails = [f"{f} | {s}" for f, s in (mail or []) if mentions(f"{f} {s}", company)]
            submitted = {r: v for r, v in info["latest"].items() if v[0] in SUBMITTED}
            if info["confirmed"] or emails:
                how = f"confirmation email: {emails[0][:120]}" if emails else "logged as confirmed"
                proof.lines.append(f"{company}: APPLIED, confirmed ({how})")
            elif submitted:
                role, (status, ts, _n) = next(iter(submitted.items()))
                proof.lines.append(f"{company}: script recorded '{status}' for {role} at {ts[:16]}, "
                                   f"no confirmation email yet")
            elif info["latest"]:
                role, (status, ts, note) = max(info["latest"].items(), key=lambda kv: kv[1][1])
                proof.lines.append(f"{company}: NOT applied. latest result for {role}: {status}"
                                   + (f" ({note})" if note else ""))
                proof.problems.append(f"{company} didn't go through ({status.replace('_', ' ')})")
            else:
                proof.lines.append(f"{company}: Dot's scripts have no application on record (the owner may have applied himself)")
                proof.problems.append(f"Dot's records show no application to {company}")
        if mail is None:
            proof.lines.append("(couldn't read the inbox, so confirmation emails weren't checked)")
        today = time.strftime("%Y-%m-%d")
        sub_today = sum(1 for a in apps.values() for v in a["latest"].values() if v[0] in SUBMITTED and v[1][:10] == today)
        proof.lines.append(f"today the application scripts recorded {sub_today} submitted")
    if _claim_sentences(text, SENT_RE) and re.search(r"\b(e-?mails?|emailed|messages?|repl(y|ied)|wrote)\b", text, re.I):
        sent = _mail("in:sent newer_than:1d", count=15, search=search)
        if sent is None:
            proof.lines.append("(couldn't read the Sent folder)")
        elif not sent:
            proof.lines.append("Sent folder: nothing sent in the last day")
            proof.problems.append("nothing is in your Sent folder from the last day")
        else:
            proof.lines.append("Sent folder, last day (newest first): " + "; ".join(s[:70] for _f, s in sent[:10]))
    return proof
