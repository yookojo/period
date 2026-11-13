#!/usr/bin/env bash
# Builds the Dot Mac app: an iMessage-style chat with Dot, with voice typing (Dot answers in text only)
# and a window to watch Dot's own computer. It talks to the Dot that's already running on this Mac.
#
#   bash mac/build-dot-app.sh                 icon: phone/icon.png
#   bash mac/build-dot-app.sh ~/me.jpg        use your own picture as the app icon and Dot's chat picture
#   ADD_TO_DOCK=1 bash mac/build-dot-app.sh   also pin it to the Dock
#
# Needs the Xcode command line tools (xcode-select --install). Installs to ~/Applications/Dot.app.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
OUT="${OUT:-$HOME/Applications}"
PIC="${1:-$ROOT/phone/icon.png}"
[ -f "$PIC" ] || { echo "No picture at $PIC"; exit 1; }
command -v swiftc >/dev/null || { echo "Install the Xcode command line tools first: xcode-select --install"; exit 1; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
APP="$TMP/Dot.app/Contents"
mkdir -p "$APP/MacOS" "$APP/Resources"
echo "==> Building the app"
swiftc -O -o "$APP/MacOS/Dot" "$HERE/DotChatApp.swift"
cat > "$APP/Info.plist" <<PLIST
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
  <key>CFBundleName</key><string>Dot</string>
  <key>CFBundleDisplayName</key><string>Dot</string>
  <key>CFBundleIdentifier</key><string>local.dot.chat</string>
  <key>CFBundleExecutable</key><string>Dot</string>
  <key>CFBundleIconFile</key><string>AppIcon</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>CFBundleShortVersionString</key><string>1.0</string>
  <key>LSMinimumSystemVersion</key><string>13.0</string>
  <key>NSHighResolutionCapable</key><true/>
  <key>NSAppTransportSecurity</key><dict><key>NSAllowsLocalNetworking</key><true/></dict>
  <key>NSMicrophoneUsageDescription</key><string>So you can talk to Dot instead of typing.</string>
  <key>NSSpeechRecognitionUsageDescription</key><string>Turns what you say into text for Dot.</string>
</dict></plist>
PLIST

echo "==> Making the icon"
# Square crop from the middle, rounded corners like other Mac apps.
"${PY:-$ROOT/.venv/bin/python}" -I - "$PIC" "$TMP/icon.png" "$TMP/avatar.jpg" <<'PY'
import sys
from PIL import Image, ImageDraw, ImageOps
src, icon, avatar = sys.argv[1:4]
im = ImageOps.exif_transpose(Image.open(src)).convert("RGB")
w, h = im.size; side = min(w, h)
sq = im.crop(((w - side) // 2, 0 if h > w else (h - side) // 2, (w + side) // 2, (0 if h > w else (h - side) // 2) + side))
sq = sq.resize((1024, 1024), Image.LANCZOS)
sq.save(avatar, quality=90)
out = Image.new("RGBA", (1024, 1024), (0, 0, 0, 0))
mask = Image.new("L", (824, 824), 0)
ImageDraw.Draw(mask).rounded_rectangle((0, 0, 823, 823), radius=185, fill=255)
out.paste(sq.resize((824, 824), Image.LANCZOS), (100, 100), mask)
out.save(icon)
PY
SET="$TMP/AppIcon.iconset"; mkdir -p "$SET"
for s in 16 32 128 256 512; do
  sips -z $s $s "$TMP/icon.png" --out "$SET/icon_${s}x${s}.png" >/dev/null
  sips -z $((s*2)) $((s*2)) "$TMP/icon.png" --out "$SET/icon_${s}x${s}@2x.png" >/dev/null
done
iconutil -c icns "$SET" -o "$APP/Resources/AppIcon.icns"
[ "$PIC" != "$ROOT/phone/icon.png" ] && cp "$TMP/avatar.jpg" "$ROOT/phone/avatar.jpg"
codesign --force --deep -s - "$TMP/Dot.app" >/dev/null 2>&1

mkdir -p "$OUT"
pkill -f "$OUT/Dot.app/Contents/MacOS/Dot" 2>/dev/null || true
rm -rf "$OUT/Dot.app" && ditto "$TMP/Dot.app" "$OUT/Dot.app"
/System/Library/Frameworks/CoreServices.framework/Frameworks/LaunchServices.framework/Support/lsregister -f "$OUT/Dot.app" || true
if [ "${ADD_TO_DOCK:-0}" = 1 ] && ! defaults read com.apple.dock persistent-apps 2>/dev/null | grep -q "$OUT/Dot.app"; then
  defaults write com.apple.dock persistent-apps -array-add \
    "<dict><key>tile-data</key><dict><key>file-data</key><dict><key>_CFURLString</key><string>file://$OUT/Dot.app/</string><key>_CFURLStringType</key><integer>15</integer></dict></dict></dict>"
  killall Dock
fi
echo
echo "Done. Open Dot from Spotlight (Cmd+Space, type Dot) or from $OUT."
