#!/usr/bin/env bash
# Sets up the Dot PC: a WSL2 Ubuntu with its own desktop, Chrome and a live view.
# Run as root inside the distro:  wsl -d Ubuntu-24.04 -u root -- bash provision.sh
# Also sets up the Mac version (a Lima Ubuntu 24.04 VM, arm64 or x86_64), run by
# mac/setup-dotpc.sh as:  limactl shell dotpc sudo bash /tmp/provision.sh
# Safe to run again.
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive

IS_WSL=0
if [ -e /proc/sys/fs/binfmt_misc/WSLInterop ] || grep -qi microsoft /proc/version 2>/dev/null; then
  IS_WSL=1
fi
ARCH="$(dpkg --print-architecture)"

apt-get update -qq
apt-get install -y -qq --no-install-recommends \
  xvfb xfce4 xfce4-terminal dbus-x11 x11-utils x11-xserver-utils \
  x11vnc novnc python3-websockify xdotool scrot imagemagick wmctrl xclip \
  python3 python3-pip python3-venv curl wget ca-certificates unzip git \
  fonts-dejavu fonts-liberation fonts-noto-color-emoji fonts-noto-cjk locales sudo >/dev/null
locale-gen en_US.UTF-8 >/dev/null

# On the Mac the Lima VM already made the dot user (mac/dotpc.yaml: user name dot, home /home/dot).
id dot >/dev/null 2>&1 || useradd -m -s /bin/bash dot
echo "dot ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/dot

if [ "$IS_WSL" = 1 ]; then
  # Isolation: no Windows drives, no running Windows programs. Only the shared
  # folder (C:\Users\<you>\DotShare -> /home/dot/share) crosses over.
  WINUSER="${1:-you}"
  cat > /etc/wsl.conf <<CONF
[boot]
systemd=false
[automount]
enabled=false
mountFsTab=true
[interop]
enabled=false
appendWindowsPath=false
[user]
default=dot
CONF
  mkdir -p /home/dot/share
  grep -q 'DotShare' /etc/fstab 2>/dev/null || \
    echo "C:\\Users\\${WINUSER}\\DotShare /home/dot/share drvfs defaults,uid=1000,gid=1000 0 0" >> /etc/fstab
fi
# (Lima: the only Mac folder it can see is ~/DotShare, mounted at /home/dot/share by mac/dotpc.yaml.)

# Python tools the agent uses inside the VM.
sudo -u dot bash -c 'python3 -m venv ~/.venv && ~/.venv/bin/pip -q install --upgrade pip playwright requests beautifulsoup4 >/dev/null'

if ! command -v google-chrome >/dev/null; then
  if wget -q -O /tmp/chrome.deb "https://dl.google.com/linux/direct/google-chrome-stable_current_${ARCH}.deb" \
      && apt-get install -y -qq /tmp/chrome.deb >/dev/null; then
    :
  elif [ "$ARCH" = "arm64" ]; then
    # No Google Chrome for this ARM Linux: use Playwright's Chromium under the usual name, so
    # dotpc.sh and everything else stay the same.
    echo "Google Chrome isn't available for ARM Linux here; installing Chromium instead"
    /home/dot/.venv/bin/playwright install-deps chromium >/dev/null
    sudo -u dot /home/dot/.venv/bin/playwright install chromium >/dev/null
    cat > /usr/local/bin/google-chrome <<'WRAP'
#!/usr/bin/env bash
# Dot PC: Playwright's Chromium standing in for Google Chrome (ARM Linux).
bin="$(ls -d /home/dot/.cache/ms-playwright/chromium-*/chrome-linux*/chrome 2>/dev/null | sort -V | tail -1)"
[ -n "$bin" ] || { echo "Chromium isn't installed (run vm/provision.sh again)" >&2; exit 1; }
exec "$bin" "$@"
WRAP
    chmod 755 /usr/local/bin/google-chrome
    # Ubuntu 24.04 blocks the user namespaces Chromium's sandbox needs unless an AppArmor profile allows
    # it (Google's deb ships one; Playwright's Chromium doesn't): "No usable sandbox!" without this.
    if command -v apparmor_parser >/dev/null && [ -d /etc/apparmor.d ]; then
      cat > /etc/apparmor.d/dotpc-chromium <<'AA'
abi <abi/4.0>,
include <tunables/global>
profile dotpc-chromium /home/dot/.cache/ms-playwright/chromium-*/chrome-linux*/chrome flags=(unconfined) {
  userns,
  include if exists <local/dotpc-chromium>
}
AA
      apparmor_parser -r /etc/apparmor.d/dotpc-chromium || true
    fi
  else
    echo "Couldn't install Google Chrome" >&2
    exit 1
  fi
  rm -f /tmp/chrome.deb
fi

install -m 755 "$(dirname "$0")/dotpc.sh" /usr/local/bin/dotpc
if [ "$IS_WSL" = 1 ]; then
  chown -R dot:dot /home/dot
else
  # Lima: the share is the Mac's own folder (already the dot user's): leave its ownership alone.
  find /home/dot -xdev -path /home/dot/share -prune -o -exec chown dot:dot {} +
fi
echo "PROVISIONED"
