#!/usr/bin/env bash
# Sets up the Dot PC on a Mac: Dot's own Linux computer (a Lima VM) with its own screen,
# Chrome and a live view. Same job as WSL on Windows. Safe to run again.
#
#   bash mac/setup-dotpc.sh
#
# Needs: macOS 13 or newer, Homebrew (https://brew.sh), about 10 GB free, and internet.
set -euo pipefail

NAME="${PERIOD_VM_LIMA:-dotpc}"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
say() { printf '\n==> %s\n' "$*"; }
fail() { printf '\nSorry, setup stopped: %s\n' "$*" >&2; exit 1; }

[ "$(uname -s)" = "Darwin" ] || fail "this script is for a Mac."
major="$(sw_vers -productVersion | cut -d. -f1)"
[ "$major" -ge 13 ] || fail "Dot's computer needs macOS 13 (Ventura) or newer. This Mac has $(sw_vers -productVersion)."
for f in "$HERE/dotpc.yaml" "$ROOT/vm/provision.sh" "$ROOT/vm/dotpc.sh"; do
  [ -f "$f" ] || fail "a setup file is missing: $f"
done

# Homebrew (a launchd job or a fresh Terminal may not have it on PATH yet).
for b in /opt/homebrew/bin/brew /usr/local/bin/brew; do
  [ -x "$b" ] && eval "$("$b" shellenv)" && break
done
command -v brew >/dev/null || fail "Homebrew isn't installed. Install it from https://brew.sh, then run this again."

if ! command -v limactl >/dev/null; then
  say "Installing Lima (the program that runs Dot's computer)"
  brew install lima
fi
ver="$(limactl --version | grep -oE '[0-9]+\.[0-9]+' | head -1)"
if [ "${ver%%.*}" -lt 1 ]; then
  say "Updating Lima (version $ver is too old)"
  brew upgrade lima
fi

mkdir -p "$HOME/DotShare"

status() { limactl list --format '{{.Status}}' "$NAME" 2>/dev/null || true; }
if [ -z "$(status)" ]; then
  say "Creating Dot's computer (this downloads Ubuntu, about 600 MB)"
  limactl create --tty=false --name "$NAME" "$HERE/dotpc.yaml"
fi
if [ "$(status)" != "Running" ]; then
  say "Starting Dot's computer"
  limactl start --tty=false "$NAME"
fi

in_vm() { limactl shell --workdir / "$NAME" "$@"; }

say "Installing the desktop, Chrome and tools inside it (5 to 15 minutes the first time)"
limactl copy "$ROOT/vm/provision.sh" "$ROOT/vm/dotpc.sh" "$NAME:/tmp/"
in_vm sudo bash /tmp/provision.sh

say "Starting its screen and Chrome"
in_vm dotpc start

pw="$(in_vm cat /home/dot/.vnc/plain 2>/dev/null || true)"
cat <<DONE

Dot's computer is ready.

  Watch it live:  http://localhost:6080/vnc.html?autoconnect=1&resize=scale
  Password:       ${pw:-"(run this script again if it's blank)"}

It can't see your Mac's files. The one shared folder is ~/DotShare
(inside Dot's computer it's called ~/share).

Optional: let Dot hand big jobs to Claude Code inside its computer
(it uses your own Claude account). Run these two lines once:

  limactl shell --workdir / $NAME bash -lc 'curl -fsSL https://claude.ai/install.sh | bash'
  limactl shell --workdir / $NAME /home/dot/.local/bin/claude

The second one opens Claude Code: sign in with your Claude account, then type /exit.

To turn Dot's computer off:  limactl stop $NAME
DONE
