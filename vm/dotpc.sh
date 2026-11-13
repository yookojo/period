#!/usr/bin/env bash
# dotpc run|start|stop|status  -- the Dot PC's desktop (display :1), VNC and live view.
#   run    start everything and stay in the foreground (keeps the WSL distro alive;
#          Period holds this open in a hidden process)
#   start  start whatever is down in the background and return (never restarts
#          what is already up)
DISP=:1; GEOM=${DOTPC_GEOM:-1440x900x24}; VNC=5901; WEB=${DOTPC_WEB_PORT:-6080}; CDP=9222
export DISPLAY=$DISP
# WSLg's Wayland display would otherwise win: x11vnc refuses to run and XFCE
# draws onto the Windows desktop instead of this hidden screen.
unset WAYLAND_DISPLAY
# A job's tags must not leak into the desktop or Chrome (stopping the job kills
# everything tagged with it).
unset DOT_JOB DOT_RUN
export XDG_RUNTIME_DIR=/tmp/dotpc-run XDG_SESSION_TYPE=x11
mkdir -p $XDG_RUNTIME_DIR && chmod 700 $XDG_RUNTIME_DIR
LOG=/tmp/dotpc; mkdir -p $LOG
# up NAME [PORT]: a process with exactly that name (pgrep -x, so "Xvfb" in some
# script's command line doesn't count), and when a port is given, someone listening on it.
up() {
  pgrep -x "$1" >/dev/null || return 1
  [ -z "$2" ] || port_up "$2"
}
port_up() { ss -ltnH "sport = :$1" 2>/dev/null | grep -q .; }
# Our screen itself answering. Not `up Xvfb`: jobs run their own Xvfb on other
# displays (xvfb-run), and a crashed :1 leaves /tmp/.X1-lock behind, which makes
# startxfce4 think it's still running.
DNUM=${DISP#:}
x_up() { timeout 5 xdpyinfo -display "$DISP" >/dev/null 2>&1; }
clear_stale_x() {
  local pid
  pid=$(tr -dc 0-9 < "/tmp/.X$DNUM-lock" 2>/dev/null)
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null && tr "\0" " " < "/proc/$pid/cmdline" 2>/dev/null | grep -q "^Xvfb $DISP "; then
    return 0
  fi
  rm -f "/tmp/.X$DNUM-lock" "/tmp/.X11-unix/X$DNUM"
}
cdp_up() { curl -s -m 2 "http://127.0.0.1:$CDP/json/version" 2>/dev/null | grep -q '"Browser"'; }
bg() { setsid nohup "$@" >>"$LOG/$(basename "$1").log" 2>&1 < /dev/null & }
CHROME_FLAGS=(--no-first-run --no-default-browser-check --remote-debugging-port=$CDP --start-maximized
  --user-data-dir=$HOME/.dot-chrome
  # Each job works in its own background tab; don't let Chrome slow those down.
  --disable-background-timer-throttling --disable-backgrounding-occluded-windows --disable-renderer-backgrounding)
# Chrome in a loop: if it crashes or is closed, it comes back in a few seconds.
# It never starts a second Chrome while one is already answering.
chrome_loop() {
  echo $$ > "$LOG/chrome-loop.pid"
  while true; do
    # No screen, no Chrome: it would only exit at once and flood the log.
    if x_up && ! cdp_up && ! pgrep -f -- "--remote-debugging-port=$CDP" >/dev/null; then
      echo "$(date '+%F %T') starting Chrome" >>"$LOG/google-chrome.log"
      google-chrome "${CHROME_FLAGS[@]}" about:blank >>"$LOG/google-chrome.log" 2>&1 </dev/null
    fi
    sleep 3
  done
}
loop_up() { [ -s "$LOG/chrome-loop.pid" ] && kill -0 "$(cat "$LOG/chrome-loop.pid")" 2>/dev/null; }
start_all() {
  x_up || { clear_stale_x; bg Xvfb $DISP -screen 0 $GEOM -nolisten tcp; }
  for i in $(seq 1 40); do x_up && break; sleep 0.25; done
  up xfce4-session || bg dbus-launch --exit-with-session startxfce4
  # The live view needs a password (any web page could otherwise drive this PC
  # through ws://localhost) and only listens on this computer.
  if [ ! -s "$HOME/.vnc/passwd" ]; then
    mkdir -p "$HOME/.vnc" && chmod 700 "$HOME/.vnc"
    tr -dc 'A-Za-z0-9' </dev/urandom | head -c 8 > "$HOME/.vnc/plain"
    x11vnc -storepasswd "$(cat "$HOME/.vnc/plain")" "$HOME/.vnc/passwd" >/dev/null 2>&1
  fi
  up x11vnc $VNC || bg x11vnc -display $DISP -rfbport $VNC -localhost -forever -shared -rfbauth "$HOME/.vnc/passwd" -quiet
  port_up $WEB || bg websockify --web /usr/share/novnc 127.0.0.1:$WEB localhost:$VNC
  loop_up || setsid nohup "$0" chrome-loop >>"$LOG/chrome-loop.log" 2>&1 </dev/null &
  for i in $(seq 1 20); do cdp_up && break; sleep 0.5; done
  echo "READY display=$DISP live=http://localhost:$WEB/vnc.html"
}
case "${1:-status}" in
  # Every Period restart opens another `run`; only the one holding the
  # lock does the upkeep, the rest just keep the distro alive until it's free.
  run) exec 9>"$LOG/run.lock"; trap 'exit 0' TERM INT
       while true; do flock -n 9 && start_all >/dev/null; sleep 30; done;;
  start) start_all;;
  chrome-loop) chrome_loop;;
  stop) [ -s "$LOG/chrome-loop.pid" ] && kill "$(cat "$LOG/chrome-loop.pid")" 2>/dev/null; rm -f "$LOG/chrome-loop.pid"
        pkill -f google-chrome; pkill -f -- "--remote-debugging-port=$CDP"; pkill -f websockify; pkill -x x11vnc; pkill -x xfce4-session; pkill -f "^Xvfb $DISP "; echo STOPPED;;
  status)
    x_up && echo "Xvfb $DISP: up" || echo "Xvfb $DISP: down"
    up xfce4-session && echo "xfce4-session: up" || echo "xfce4-session: down"
    up x11vnc $VNC && echo "x11vnc: up" || echo "x11vnc: down"
    port_up $WEB && echo "websockify: up" || echo "websockify: down"
    cdp_up && echo "cdp $CDP: up" || echo "cdp $CDP: down";;
esac
