#!/bin/bash
# Clean teardown of the PURE-EVAL fleet started by run_fleet_eval.sh.
#
# ORDER MATTERS (missing-lemma SKILL.md:59-78): kill the RESURRECTOR first, then
# scancel, then poll. slurm.run_server is a non-daemon while-True thread living
# IN the orchestrator process that re-issues `srun` ~every 10s; if we scancel
# before killing the orchestrator, squeue refills within ~10s and the job never
# dies. So:
#   1. kill the orchestrator PROCESS GROUP (recorded pgid) -> stops revivers +
#      their srun children (Popen shell=True, no start_new_session -> same pgrp).
#   2. scancel --name=<job> (exact name, like watcher.py:2115 — NOT free_servers'
#      grep substring) then POLL squeue until the job is gone (a lingering CG job
#      re-trips the job-name-blind check_node).
#   3. kill the central RPC host by recorded pid / exact RPC port LISTEN.
#
# Targets are resolved ONLY by recorded pid/pgid/port — never `pkill -f`
# (shared login node; CLAUDE.md).
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
STATE_DIR="$ROOT/tools/aoa_putnam_eval/state_fleet"
ts() { date -Is; }
log() { echo "[$(ts)] $*"; }

JOB="${JOB:-$(cat "$STATE_DIR/job_name" 2>/dev/null || true)}"
EVAL_PGID="$(cat "$STATE_DIR/eval.pgid" 2>/dev/null || true)"
RPC_PID="$(cat "$STATE_DIR/rpc_host.pid" 2>/dev/null || true)"
RPC_PORT="$(cat "$STATE_DIR/rpc_port" 2>/dev/null || echo 27185)"

# ---- 1. kill the orchestrator group FIRST (stop the resurrector) -----------
if [ -n "$EVAL_PGID" ]; then
  if kill -0 "$EVAL_PGID" 2>/dev/null; then
    kill -- -"$EVAL_PGID" 2>/dev/null && log "SIGTERM orchestrator process group $EVAL_PGID"
    sleep 3
    kill -0 "$EVAL_PGID" 2>/dev/null && kill -9 -- -"$EVAL_PGID" 2>/dev/null && log "SIGKILL orchestrator group $EVAL_PGID"
  else
    log "orchestrator group $EVAL_PGID already gone"
  fi
else
  log "WARN: no recorded eval.pgid — cannot group-kill the orchestrator (revivers may persist)"
fi

# ---- 2. scancel by EXACT job name, then poll squeue until empty ------------
if [ -n "$JOB" ]; then
  scancel --name="$JOB" 2>/dev/null && log "scancel --name=$JOB issued"
  deadline=$((SECONDS + 120))
  while :; do
    left="$(squeue --me -h --name="$JOB" -o '%i' 2>/dev/null | wc -l)"
    [ "$left" -eq 0 ] && { log "all srun tasks for $JOB cleared"; break; }
    if [ $SECONDS -gt $deadline ]; then
      log "WARN: $left task(s) for $JOB still in squeue after 120s — re-issuing scancel"
      scancel --name="$JOB" 2>/dev/null || true
      deadline=$((SECONDS + 60))
    fi
    sleep 5
  done
else
  log "WARN: no recorded job_name — skipping scancel (check squeue manually)"
fi

# ---- 3. kill the central RPC host (recorded pid + exact port) --------------
if [ -n "$RPC_PID" ] && kill -0 "$RPC_PID" 2>/dev/null; then
  kill "$RPC_PID" 2>/dev/null && log "SIGTERM central RPC host pid $RPC_PID"
fi
# belt-and-suspenders: exact port LISTEN only (never pkill -f)
if command -v lsof >/dev/null 2>&1; then
  lsof -ti tcp:"$RPC_PORT" -s TCP:LISTEN 2>/dev/null | xargs -r kill 2>/dev/null \
    && log "killed any remaining LISTENer on $RPC_PORT"
fi

log "teardown complete (job=$JOB rpc_port=$RPC_PORT). Verify: squeue --me ; ss -ltn | grep $RPC_PORT"
