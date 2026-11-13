#!/usr/bin/env bash
# Installs Dot on a Mac. Dot thinks with YOUR Claude plan (Claude Code), you text it on Discord,
# and it starts by itself when you log in. Safe to run again.
#
#   cd ~/Dot && bash mac/install-dot.sh
#
# Needs: macOS 13 or newer, a Claude Pro or Max plan, internet. Takes about 10 minutes.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
VENV="$ROOT/.venv"
say() { printf '\n==> %s\n' "$*"; }
fail() { printf '\nSorry, setup stopped: %s\n' "$*" >&2; exit 1; }

[ "$(uname -s)" = "Darwin" ] || fail "this installer is for a Mac."
major="$(sw_vers -productVersion | cut -d. -f1)"
[ "$major" -ge 13 ] || fail "Dot needs macOS 13 (Ventura) or newer. This Mac has $(sw_vers -productVersion)."
[ -f "$ROOT/pd_dots.py" ] && [ -f "$ROOT/period.py" ] || fail "run this from inside the Dot folder (it needs pd_dots.py next to mac/)."
case "$ROOT" in *" "*) fail "move the Dot folder somewhere without spaces in its path (for example ~/Dot), then run this again.";; esac

# 1. Homebrew: installs Python and (optionally) the VM for Dot's own computer.
for b in /opt/homebrew/bin/brew /usr/local/bin/brew; do
  [ -x "$b" ] && eval "$("$b" shellenv)" && break
done
if ! command -v brew >/dev/null; then
  say "Installing Homebrew (Mac's app installer for developer tools). It will ask for your Mac password."
  /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
  for b in /opt/homebrew/bin/brew /usr/local/bin/brew; do
    [ -x "$b" ] && eval "$("$b" shellenv)" && break
  done
  command -v brew >/dev/null || fail "Homebrew didn't install. Install it from https://brew.sh, then run this again."
fi

# 2. Python 3.12 in its own folder (.venv), so nothing else on the Mac changes.
PY="$(brew --prefix)/bin/python3.12"
if [ ! -x "$PY" ]; then
  say "Installing Python 3.12"
  brew install python@3.12
fi
if [ ! -x "$VENV/bin/python" ]; then
  say "Making Dot's own Python folder"
  "$PY" -m venv "$VENV"
fi
say "Installing what Dot needs (a few minutes the first time)"
"$VENV/bin/python" -m pip install -q --upgrade pip
"$VENV/bin/python" -m pip install -q -r "$ROOT/requirements.txt" psutil
"$VENV/bin/python" -m playwright install chromium >/dev/null 2>&1 || \
  echo "   (couldn't download Dot's web browser yet; web tasks will try again later)"
command -v cliclick >/dev/null || brew install cliclick >/dev/null 2>&1 || true

# 3. Claude Code: the brain. Dot only ever uses this Mac's own Claude sign-in.
CLAUDE=""
for c in "$HOME/.local/bin/claude" "$(command -v claude || true)" /opt/homebrew/bin/claude /usr/local/bin/claude; do
  [ -n "$c" ] && [ -x "$c" ] && CLAUDE="$c" && break
done
if [ -z "$CLAUDE" ]; then
  say "Installing Claude Code"
  curl -fsSL https://claude.ai/install.sh | bash
  CLAUDE="$HOME/.local/bin/claude"
  [ -x "$CLAUDE" ] || fail "Claude Code didn't install. See https://claude.com/claude-code, then run this again."
fi
if ! "$CLAUDE" -p "Reply with exactly: ok" --model claude-haiku-5-5 </dev/null 2>/dev/null | grep -qi ok; then
  say "Sign in to Claude Code with YOUR Claude account (Pro or Max)."
  echo "   Claude Code opens now. Follow its sign-in steps, then type /exit to come back here."
  "$CLAUDE" || true
  "$CLAUDE" -p "Reply with exactly: ok" --model claude-haiku-5-5 </dev/null 2>/dev/null | grep -qi ok || \
    fail "Claude Code still isn't signed in. Run \`claude\`, sign in, then run this installer again."
fi
echo "   Claude Code is signed in."

# 4. Dot's own computer (optional): a Linux VM with its own screen and Chrome.
if [ ! -f "$HOME/.period_dots/no_vm" ]; then
  if limactl list --format '{{.Name}}' 2>/dev/null | grep -qx "${PERIOD_VM_LIMA:-dotpc}"; then
    echo "   Dot's own computer is already set up."
  else
    printf '\nGive Dot its own computer (a Linux VM, about 10 GB)? It browses and downloads there instead\n'
    printf 'of on your Mac. You can add it later with: bash mac/setup-dotpc.sh\n'
    read -r -p "Set it up now? [Y/n] " ans || ans=""
    case "${ans:-y}" in
      [Yy]*) bash "$HERE/setup-dotpc.sh" || echo "   Dot's computer didn't finish setting up; Dot still works on your Mac. Try again later with: bash mac/setup-dotpc.sh";;
      *) mkdir -p "$HOME/.period_dots" && touch "$HOME/.period_dots/no_vm"
         echo "   Skipped. Dot will work on your Mac and ask before anything risky.";;
    esac
  fi
fi

# 5. Claude-only mode, Discord, start at login, and a final check.
say "Connecting Dot"
export PERIOD_BACKEND=claude PERIOD_DOT_CLAUDE_CLI="$CLAUDE"
cd "$ROOT"
"$VENV/bin/python" pd_dots.py setup-mac || true

cat <<EOF

Done. Text Dot on Discord to give it a job, like "find me cheap flights to Chicago for Thanksgiving".

  Check on it any time:   cd "$ROOT" && .venv/bin/python pd_dots.py doctor
  Its page:               http://localhost:8767
  Stop it starting:       cd "$ROOT" && .venv/bin/python pd_dots.py uninstall

The first time Dot takes a screenshot or clicks on your Mac, macOS asks to allow it under
System Settings > Privacy & Security (Screen Recording, Accessibility). Allow Python there.
EOF
