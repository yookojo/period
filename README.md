# Period

Period is a personal AI assistant you text. You message it on Discord ("find me cheap flights to Chicago for
Thanksgiving", "what's due this week?") and it does the work on your Mac, or on its own little Linux computer
that runs inside your Mac, then texts you back. Inside, it's called Dot.

It thinks with **your own Claude plan** through [Claude Code](https://claude.com/claude-code). There's no other
account, server or API key involved.

## What it can do

- Real work on your computer: files, apps, the web, your logged-in browser, mail and calendar (once connected)
- Its own computer (optional): a Linux VM with its own screen and Chrome, so browsing and downloads stay off yours
- Jobs that keep running: schedules, reminders, "tell me when this price drops", a morning brief
- Asks first for anything involving money or anything drastic (checkouts, card numbers, wiping files,
  password changes, posting publicly). Ordinary work runs on its own.

## Install on a Mac (about 10 minutes)

Needs macOS 13 or newer, a Claude Pro or Max plan, and a Discord account.

    # download this repo to ~/Period (Code > Download ZIP, or git clone it), then:
    cd ~/Period && bash mac/install-dot.sh

The installer sets up Python and Claude Code, walks you through making a Discord bot, offers to give Period its
own computer, and makes it start when you log in. Check on it any time:

    cd ~/Period && .venv/bin/python pd_dots.py doctor

More detail, including what macOS asks permission for: [docs/MAC.md](docs/MAC.md).

## Good to know

- It only works while your Mac is awake.
- When your Claude plan hits its limit, Period says so and waits for the plan to reset.
- Everything it remembers (memory, rules, chats) stays on your Mac in `~/.period_dots/`.
