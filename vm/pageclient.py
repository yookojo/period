"""One request to the Dot PC page server (runs inside the VM, plain python3).

Reads one JSON request on stdin, prints the server's one-line JSON reply.
Starts the server (detached, its own session) when the socket is dead.
Exit 3 with {"error": "NOSERVER: ..."} when it can't be reached at all, so the
caller can fall back to the one-shot page reader.
"""
import json
import os
import socket
import subprocess
import sys
import time

DIR = os.path.expanduser("~/.dotpc")
SOCK = os.path.join(DIR, "page.sock")
SERVER = os.path.join(DIR, "pageserver.py")
PY = os.path.expanduser("~/.venv/bin/python")
LOG = "/tmp/dotpc/pageserver.log"


def call(data, timeout):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    s.connect(SOCK)
    s.sendall(data.rstrip(b"\n") + b"\n")
    buf = b""
    while not buf.endswith(b"\n"):
        chunk = s.recv(1 << 16)
        if not chunk:
            break
        buf += chunk
    s.close()
    return buf


def start_server():
    os.makedirs("/tmp/dotpc", exist_ok=True)
    env = {k: v for k, v in os.environ.items() if k not in ("DOT_JOB", "DOT_RUN")}
    subprocess.Popen([PY, SERVER], stdin=subprocess.DEVNULL, stdout=open(LOG, "ab"),
                     stderr=subprocess.STDOUT, start_new_session=True, env=env, cwd=os.path.expanduser("~"))


def main():
    timeout = float(sys.argv[1]) if len(sys.argv) > 1 else 85.0
    data = sys.stdin.buffer.read()
    try:
        out = call(data, timeout)
    except (FileNotFoundError, ConnectionRefusedError):
        if not os.path.exists(SERVER):
            print(json.dumps({"error": "NOSERVER: page server not installed"}))
            sys.exit(3)
        start_server()
        out = None
        end = time.time() + 20
        while time.time() < end:
            time.sleep(0.25)
            try:
                out = call(data, timeout)
                break
            except (FileNotFoundError, ConnectionRefusedError):
                continue
        if out is None:
            print(json.dumps({"error": "NOSERVER: page server didn't start (see /tmp/dotpc/pageserver.log)"}))
            sys.exit(3)
    except socket.timeout:
        print(json.dumps({"error": f"the page took longer than {timeout:.0f}s to answer"}))
        sys.exit(2)
    if not out.strip():
        print(json.dumps({"error": "NOSERVER: page server closed the connection without answering"}))
        sys.exit(3)
    sys.stdout.buffer.write(out)


if __name__ == "__main__":
    main()
