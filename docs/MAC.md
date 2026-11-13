# Period on a Mac

Period (the assistant inside calls itself Dot) has three parts on a Mac:

| | On your Mac |
|---|---|
| Thinks with | **Only your own Claude plan**, through Claude Code (`claude -p`) |
| Its own computer | Ubuntu in a **Lima** VM (optional) |
| Starts at login | **launchd** (`~/Library/LaunchAgents/com.period.dot.plist`) |

## What you need

- A Mac with macOS 13 (Ventura) or newer. Apple Silicon (M1 and later) or Intel.
- A **Claude Pro or Max** plan. Dot runs many model calls per job. Max lasts much longer before you hit
  the plan's limits. On Pro, a few long jobs can use up the five-hour allowance.
- A **Discord** account and a server you own (a private one just for you is fine). This is where you text Dot.
- About 2 GB of disk for Dot, plus about 10 GB if Dot gets its own computer.

## Install

```
cd ~/Dot && bash mac/install-dot.sh
```

The installer:

1. installs Homebrew, Python 3.12 and Dot's Python packages into `~/Dot/.venv`
2. installs Claude Code and has you sign in with your own Claude account
3. offers to set up Dot's own computer (`mac/setup-dotpc.sh`: Lima, Ubuntu, a hidden desktop, Chrome, a live view)
4. switches Dot to Claude-only mode, walks you through making the Discord bot, and makes Dot start at login
5. runs `pd_dots.py doctor`, which checks everything and tells you what to fix in plain words

## Making the Discord bot (the installer walks you through it)

1. Go to https://discord.com/developers/applications and click **New Application**. Any name works.
2. Under **Bot**, click **Reset Token** and copy the token. Paste it when the installer asks.
   On the same page, turn on **Message Content Intent**.
3. Under **OAuth2 > URL Generator**, tick `bot`, then tick *Send Messages* and *Read Message History*.
   Open the link it makes and add the bot to your server.
4. In any channel the bot can see, send `hi dot`. Dot finds you and DMs you. Only you can give it jobs.

## Permissions macOS asks for

The first time Dot takes a screenshot or clicks on your Mac, macOS asks you to allow it. Turn on **Python** under
System Settings > Privacy & Security > **Screen Recording** and **Accessibility**. If you never allow it,
Dot still works, but it can't see or click your screen, only run commands and use its own computer.

## Good to know

- **Sleep:** Dot only works while the Mac is awake. The installer can keep the Mac from idle-sleeping, but closing
  the lid still puts it to sleep (unless it's plugged in with an external display).
- **Plan limits:** when your Claude plan hits its limit, Dot says so and waits until the plan resets.
  Nothing falls back to another account.
- **Safety:** money (checkouts, card numbers, sending money) and drastic actions (wiping files, password or account
  changes, posting publicly) always wait for your OK by text. On its own computer, anything goes except money.
- **Dot's own computer:** on Apple Silicon it runs ARM Linux. If Google doesn't offer Chrome for that, the
  setup installs Chromium instead. Chromium works the same for almost every site.
- **Using Claude Code inside Dot's computer** (the `vm_claude` tool) is optional. It needs its own sign-in once:
  `limactl shell dotpc` then `claude`.

## Commands

```
.venv/bin/python pd_dots.py doctor       check everything
.venv/bin/python pd_dots.py restart      restart Dot after changing settings
.venv/bin/python pd_dots.py uninstall    stop Dot starting at login
bash mac/setup-dotpc.sh                  add or repair Dot's own computer
limactl stop dotpc                       turn Dot's computer off (limactl start dotpc to turn it back on)
```

Logs are in `~/.period_dots/` (`launchd.err.log` if Dot won't start). Dot's memory, rules and chats live
there too. Delete that folder to start fresh.
