#!/usr/bin/env python3
"""
Dedicated Isa-REPL server for the MathBench import-reconciliation pipeline.

Runs on a private port (default 7777) with base session MathBench_ProverBase,
isolated from the default 6666 that other tasks use. The pipeline can start and
restart this itself — restart is the inner-loop step after editing
MathBench_Prover.thy (the REPL caches loaded theories, so edits are only picked
up on a fresh server).

  python tools/mathbench_repl.py start     # start if not already up, wait until ready
  python tools/mathbench_repl.py restart   # stop + start (after editing MathBench_Prover.thy)
  python tools/mathbench_repl.py stop
  python tools/mathbench_repl.py status

Only ever touches port 7777 — never the 6666 server other tasks may use.
"""
import argparse
import asyncio
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'contrib', 'Isa-REPL'))

PORT = 7777
ADDR = f'127.0.0.1:{PORT}'
SESSION = 'MathBench_ProverBase'
OUTDIR = '/tmp/mathbench_repl_outputs'
LOG = '/tmp/mathbench_repl.log'
REPL_SH = os.path.join(ROOT, 'contrib', 'Isa-REPL', 'repl_server.sh')


def listener_pid(port=PORT):
    """PID of the process LISTENING on `port`, or None.

    Matches the local-address column exactly (field 4 of `ss -ltnpH`,
    `State Recv-Q Send-Q Local:Port Peer:Port Process`) so we never match a
    peer address or a superstring port like :17777 — and never kill the wrong
    process (e.g. the 6666 server)."""
    try:
        out = subprocess.check_output(['ss', '-ltnpH'], text=True)
    except Exception:
        return None
    for line in out.splitlines():
        cols = line.split()
        if len(cols) >= 4 and cols[3].endswith(f':{port}'):
            m = re.search(r'pid=(\d+)', line)
            if m:
                return int(m.group(1))
    return None


async def wait_ready(timeout=600):
    """Poll until the REPL accepts a trivial eval (heap loaded), or time out.
    The MathBench_ProverBase heap can take several minutes to load on a cold start."""
    from IsaREPL import Client
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            async with Client(ADDR, 'HOL', timeout=60) as c:
                await c.eval('theory MB_Ping imports Main begin end', timeout=60000)
            return True
        except Exception:
            await asyncio.sleep(3)
    return False


def stop():
    pid = listener_pid()
    if not pid:
        print(f"no server on {PORT}")
        return
    print(f"stopping REPL on {PORT} (pid {pid})")
    subprocess.run(['kill', str(pid)])
    for _ in range(30):
        if listener_pid() is None:
            return
        time.sleep(1)
    pid2 = listener_pid()          # re-resolve in case the pid was reused
    if pid2:
        subprocess.run(['kill', '-9', str(pid2)])


def start():
    if listener_pid():
        print(f"server already listening on {PORT}; verifying readiness")
    else:
        os.makedirs(OUTDIR, exist_ok=True)
        logf = open(LOG, 'w')
        subprocess.Popen([REPL_SH, ADDR, SESSION, OUTDIR],
                         stdout=logf, stderr=subprocess.STDOUT,
                         start_new_session=True, cwd=ROOT)
        print(f"launching REPL on {ADDR} (base session {SESSION}); waiting for ready...")
    if asyncio.run(wait_ready()):
        print(f"REPL ready on {ADDR}")
    else:
        print(f"REPL did NOT become ready within timeout (see {LOG})", file=sys.stderr)
        sys.exit(1)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('cmd', choices=['start', 'stop', 'restart', 'status'])
    cmd = ap.parse_args().cmd
    if cmd == 'stop':
        stop()
    elif cmd == 'restart':
        stop()
        start()
    elif cmd == 'start':
        start()
    else:
        pid = listener_pid()
        print(f"listening on {PORT} (pid {pid})" if pid else f"not running on {PORT}")


if __name__ == '__main__':
    main()
