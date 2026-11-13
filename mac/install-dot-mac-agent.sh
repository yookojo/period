#!/bin/bash
# Install Dot's Mac helper (dot_mac_agent.py) so it starts at login and restarts if it stops.
# Run on the Mac:   bash install-dot-mac-agent.sh
# Then pair it with the Dot that should control this Mac (the command it prints at the end).
set -euo pipefail
DIR="$HOME/.dot_mac"
PLIST="$HOME/Library/LaunchAgents/com.dot.macagent.plist"
SRC="$(cd "$(dirname "$0")" && pwd)/dot_mac_agent.py"
PY="$(command -v python3 || true)"
[ -n "$PY" ] || { echo "python3 is missing: install it (brew install python, or xcode-select --install)"; exit 1; }
command -v tailscale >/dev/null 2>&1 || [ -x /Applications/Tailscale.app/Contents/MacOS/Tailscale ] || \
  echo "note: Tailscale isn't installed; the helper will only listen on 127.0.0.1 (a Dot on this Mac can still use it)"
mkdir -p "$DIR" "$HOME/Library/LaunchAgents"
cp "$SRC" "$DIR/dot_mac_agent.py"
command -v cliclick >/dev/null 2>&1 || { command -v brew >/dev/null 2>&1 && brew install cliclick >/dev/null 2>&1 || \
  echo "note: install cliclick (brew install cliclick) so Dot can click"; }
cat > "$PLIST" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
  <key>Label</key><string>com.dot.macagent</string>
  <key>ProgramArguments</key><array><string>$PY</string><string>$DIR/dot_mac_agent.py</string><string>serve</string></array>
  <key>RunAtLoad</key><true/>
  <key>KeepAlive</key><true/>
  <key>StandardOutPath</key><string>$DIR/stdout.log</string>
  <key>StandardErrorPath</key><string>$DIR/stderr.log</string>
</dict></plist>
EOF
launchctl unload "$PLIST" 2>/dev/null || true
launchctl load "$PLIST"
sleep 2
INFO="$("$PY" "$DIR/dot_mac_agent.py" info)"
HOST="$(echo "$INFO" | "$PY" -c 'import json,sys; print(json.load(sys.stdin)["host"])')"
TOK="$(echo "$INFO" | "$PY" -c 'import json,sys; print(json.load(sys.stdin)["token"])')"
echo
echo "Dot's Mac helper is running on $HOST:8790 and starts at login."
echo "macOS will ask once for Screen Recording and Accessibility for python3: allow both (System Settings > Privacy)."
echo
echo "To let Dot on your PC control this Mac, run this on the PC (in Claude Code: ! ...):"
echo "  python C:/Users/you/.gemini/antigravity/scratch/period/pd_mac.py pair $HOST $TOK"
