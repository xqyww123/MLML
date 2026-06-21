#!/bin/bash
# Thin PURE-EVAL fleet launcher for AoA x PutnamBench on the mbzuai-fm SLURM
# cluster (4 nodes x 6 independent REPLs = 24-way). NO missing-lemma loop.
#
# It mirrors tools/aoa_putnam_eval/start_servers.sh (RPC host start) + the
# detach pattern of run_pipeline.sh, but:
#   * binds the central RPC host on 0.0.0.0:$RPC_PORT (compute REPLs connect back)
#   * execs evaluation/evaluator_top.py agent-putnam (CLUSTER=slurmx), whose
#     launch_servers()->slurm.run_servers() srun's the per-node REPLs and whose
#     evaluate_and_save() work-steals 24 ways from config/evaluation_servers.csv
#   * does NOT inject the missing-lemma survey env
#
# All AoA Python (DeepSeek calls + semantic retrieval) runs in the ONE central
# RPC host on THIS login node; compute nodes only run Isabelle ML.
#
# Hard constraints enforced/encoded here (see plan scalable-spinning-wren.md §4):
#   (2) must NOT share a login node with a missing-lemma loop watcher (its
#       `pkill -f fork_and_launch__` would SIGKILL our RPC host) -> pre-checked.
#   (3) CSV node set must be DISJOINT from any of OUR OTHER squeue jobs
#       (check_node in slurm.py is job-name-blind) -> pre-checked.
#   (1) post-launch completeness gate (TCP-connect every host:port + squeue
#       RUNNING==N, PENDING==0); degraded => abort+scancel (else evaluator.py
#       still reports success on a silently <24 run).
#
# Usage (env-configured):
#   NODES=cn-01,cn-04,cn-05,cn-06 [LOGIN_IB0=...] [RPC_PORT=27185] \
#   [PORTS_PER_NODE=6] [BASE_PORT=6666] [NUMPROCS=8] [WALLTIME=48:00:00] \
#   [CASE_CATEGORY=test] [DRIVER=DeepSeekV4.pro] [JOB=aoaputnam-<uuid>] \
#   [RESULT_DB=...] [LOG_DIR=...] \
#   tools/aoa_putnam_eval/run_fleet_eval.sh [-- extra args to evaluator_top]
#
# Re-run as a periodic health probe only (no setup/launch):
#   JOB=<job> NODES=... tools/aoa_putnam_eval/run_fleet_eval.sh --check
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
HERE="$ROOT/tools/aoa_putnam_eval"
STATE_DIR="$HERE/state_fleet"
mkdir -p "$STATE_DIR"

ts() { date -Is; }
log() { echo "[$(ts)] $*"; }
die() { log "FATAL: $*"; exit 1; }

# ---- configuration ---------------------------------------------------------
RPC_PORT="${RPC_PORT:-27185}"          # distinct from 27180(build)/27182(loop)/27183(collect)/27184(single-AoA)
PORTS_PER_NODE="${PORTS_PER_NODE:-6}"
BASE_PORT="${BASE_PORT:-6666}"
NUMPROCS="${NUMPROCS:-8}"              # Isabelle threads per REPL JVM
WALLTIME="${WALLTIME:-48:00:00}"       # exported as SLURM_EVAL_WALLTIME (slurm.py reads it)
CASE_CATEGORY="${CASE_CATEGORY:-test}"
DRIVER="${DRIVER:-DeepSeekV4.pro}"
RESULT_DB="${RESULT_DB:-$STATE_DIR/putnam_fleet_${DRIVER}.db}"
LOG_DIR="${LOG_DIR:-$STATE_DIR/logs}"
GATE_DEADLINE="${GATE_DEADLINE:-1800}"  # seconds to wait for all 24 REPLs to LISTEN (heap load ~90s+ each)

# login ib0 name the compute REPLs dial back on. Auto-derive from this host
# unless overridden; the launcher MUST run on the login node it advertises.
if [ -z "${LOGIN_IB0:-}" ]; then
  _hs="$(hostname -s 2>/dev/null || hostname)"
  LOGIN_IB0="${_hs}.ib0.cscc-new.mbzuai.ac.ae"
fi

[ -n "${NODES:-}" ] || die "NODES is required (comma-separated SLURM node names, e.g. cn-01,cn-04,cn-05,cn-06)"
IFS=',' read -r -a NODE_ARR <<< "$NODES"
NUM_NODES="${#NODE_ARR[@]}"
EXPECT_REPLS=$(( NUM_NODES * PORTS_PER_NODE ))

# forwarded extra args (drop a leading `--`)
FWD=("$@")
if [ "${FWD[0]:-}" = "--" ]; then FWD=("${FWD[@]:1}"); fi
CHECK_ONLY=0
if [ "${FWD[0]:-}" = "--check" ]; then CHECK_ONLY=1; FWD=("${FWD[@]:1}"); fi

port_listening() { lsof -ti tcp:"$1" -s TCP:LISTEN >/dev/null 2>&1; }
tcp_ok() { timeout 3 bash -c "exec 3<>/dev/tcp/$1/$2" 2>/dev/null; }

# ---- the M4 completeness gate (also reused by --check) ---------------------
# Returns 0 iff: squeue shows exactly NUM_NODES distinct RUNNING nodes for $JOB
# and zero PENDING, AND every host:port accepts a TCP connection.
fleet_ready() {
  local job="$1" quiet="${2:-0}"
  local line state node running_nodes pending
  running_nodes=""
  pending=0
  while IFS='|' read -r state node; do
    [ -z "$state" ] && continue
    case "$state" in
      RUNNING) running_nodes="$running_nodes $node" ;;
      PENDING|CONFIGURING) pending=$((pending+1)) ;;
    esac
  done < <(squeue --me -h --name="$job" -o '%T|%N' 2>/dev/null)
  local ndistinct
  ndistinct=$(echo $running_nodes | tr ' ' '\n' | sed '/^$/d' | sort -u | wc -l)
  if [ "$pending" -ne 0 ]; then
    [ "$quiet" = 1 ] || log "gate: $pending srun task(s) still PENDING/CONFIGURING"
    return 1
  fi
  if [ "$ndistinct" -ne "$NUM_NODES" ]; then
    [ "$quiet" = 1 ] || log "gate: $ndistinct/$NUM_NODES distinct RUNNING nodes for job $job"
    return 1
  fi
  local n p missing=0
  for n in "${NODE_ARR[@]}"; do
    for ((p=BASE_PORT; p<BASE_PORT+PORTS_PER_NODE; p++)); do
      if ! tcp_ok "$n" "$p"; then missing=$((missing+1)); fi
    done
  done
  if [ "$missing" -ne 0 ]; then
    [ "$quiet" = 1 ] || log "gate: $missing/$EXPECT_REPLS REPL ports not yet accepting TCP"
    return 1
  fi
  return 0
}

# ---- --check mode: one-shot health probe, no setup ------------------------
if [ "$CHECK_ONLY" = 1 ]; then
  [ -n "${JOB:-}" ] || JOB="$(cat "$STATE_DIR/job_name" 2>/dev/null || true)"
  [ -n "${JOB:-}" ] || die "--check needs JOB (or a recorded state_fleet/job_name)"
  if fleet_ready "$JOB" 0; then
    log "OK: job $JOB holds $NUM_NODES nodes, all $EXPECT_REPLS REPLs reachable"; exit 0
  else
    log "DEGRADED: job $JOB is not at full $EXPECT_REPLS-way capacity"; exit 1
  fi
fi

JOB="${JOB:-aoaputnam-$(cat /proc/sys/kernel/random/uuid 2>/dev/null | cut -c1-8 || echo $$)}"

# ---- credentials + environment --------------------------------------------
set +u
source ./envir.sh
[ -f ./secret.sh ] && source ./secret.sh
set -u
[ -n "${DEEPSEEK_API_KEY:-}" ] || die "DEEPSEEK_API_KEY not set after secret.sh (DeepSeek driver runs in the RPC host)"
export DEEPSEEK_API_KEY
log "config: NODES=$NODES ports=$BASE_PORT..$((BASE_PORT+PORTS_PER_NODE-1)) numprocs=$NUMPROCS"
log "config: RPC_PORT=$RPC_PORT LOGIN_IB0=$LOGIN_IB0 JOB=$JOB WALLTIME=$WALLTIME -> ${EXPECT_REPLS}-way"

# ---- blocker (2): no missing-lemma loop on THIS login node -----------------
# Its watcher does port-agnostic `pkill -9 -f fork_and_launch__`, which would
# SIGKILL our central RPC host; with AUTO_START_RPC_SERVER=0 the compute REPLs
# would never respawn -> silent dead eval.
if pgrep -f "missing_lemma_loop/watcher.py" >/dev/null 2>&1; then
  die "a missing-lemma watcher.py is running on this login node — refusing (its pkill -f fork_and_launch__ would kill our RPC host). Use a different login node or stop the loop."
fi
if port_listening 27182; then
  die "something is LISTENing on 27182 (missing-lemma loop RPC host?) on this login — refusing to co-reside."
fi

# ---- blocker (3): node set disjoint from OUR OTHER squeue jobs -------------
# check_node (slurm.py:17) is job-name-blind: run_server would skip-and-adopt a
# foreign REPL on any node that already carries one of OUR jobs.
for n in "${NODE_ARR[@]}"; do
  others="$(squeue --me -h -w "$n" -o '%i %j' 2>/dev/null | grep -v " $JOB$" || true)"
  if [ -n "$others" ]; then
    die "node $n already runs another of YOUR jobs (check_node is job-name-blind and would adopt its REPL):
$others
Pick nodes with no other jobs of yours, or stop them."
  fi
done

# ---- generate config/evaluation_servers.csv (back up any existing) ---------
CSV="$ROOT/config/evaluation_servers.csv"
if [ -f "$CSV" ]; then
  bak="$CSV.bak.$(date +%Y%m%d-%H%M%S)"
  cp -p "$CSV" "$bak"
  log "backed up existing CSV -> $bak"
fi
{
  echo "server, numprocs, num-translator, num-evaluator"
  for n in "${NODE_ARR[@]}"; do
    for ((p=BASE_PORT; p<BASE_PORT+PORTS_PER_NODE; p++)); do
      echo "$n:$p, $NUMPROCS, 1, 1"
    done
  done
} > "$CSV"
log "wrote $CSV ($EXPECT_REPLS rows)"

# ---- pre-create result DB (short-circuit clean_mash's mv) ------------------
# evaluator_top.clean_mash mv's ./cache/repl_tmps only when --result DB is
# ABSENT; pre-create via SqliteDict (NOT bare touch, else resume chokes).
if [ ! -f "$RESULT_DB" ]; then
  mkdir -p "$(dirname "$RESULT_DB")"
  python3 -c "from sqlitedict import SqliteDict; d=SqliteDict('$RESULT_DB'); d.commit(); d.close()" \
    || die "could not pre-create result DB $RESULT_DB"
  log "pre-created result DB $RESULT_DB (clean_mash mv short-circuited)"
else
  log "result DB exists -> resume mode: $RESULT_DB"
fi
mkdir -p "$LOG_DIR"

# ---- central RPC host on 0.0.0.0:$RPC_PORT --------------------------------
if port_listening "$RPC_PORT"; then
  die "$RPC_PORT already LISTENing on this login — refusing to clobber. Pick a free RPC_PORT or clean it up."
fi
log "launching central Isabelle_RPC_Host on 0.0.0.0:$RPC_PORT (log: $STATE_DIR/rpc_host.log)"
python3 -c "import Isabelle_RPC_Host; Isabelle_RPC_Host.fork_and_launch__()" \
        "0.0.0.0:$RPC_PORT" "$STATE_DIR/rpc_host.log"
deadline=$((SECONDS + 60))
until port_listening "$RPC_PORT"; do
  [ $SECONDS -gt $deadline ] && die "central RPC host did not come up on 0.0.0.0:$RPC_PORT in 60s (see $STATE_DIR/rpc_host.log)"
  sleep 1
done
RPC_PID="$(lsof -ti tcp:"$RPC_PORT" -s TCP:LISTEN | head -1)"
echo "$RPC_PID" > "$STATE_DIR/rpc_host.pid"
log "central RPC host up (pid $RPC_PID) on 0.0.0.0:$RPC_PORT"

# ---- launch the orchestrator (setsid -> own pgrp/session leader) -----------
# The slurm.run_server while-True reviver threads AND atexit live in THIS
# process; detaching it as a session leader lets stop kill the WHOLE group and
# survives SSH SIGHUP. PGID == the setsid child's PID.
echo "$JOB"      > "$STATE_DIR/job_name"
echo "$NODES"    > "$STATE_DIR/nodes"
echo "$RPC_PORT" > "$STATE_DIR/rpc_port"
EVAL_LOG="$STATE_DIR/fleet_eval.log"
log "launching slurmx fleet eval (driver=$DRIVER, job=$JOB, category=$CASE_CATEGORY); log: $EVAL_LOG"
setsid bash -c "
  cd '$ROOT'
  source ./envir.sh
  [ -f ./secret.sh ] && source ./secret.sh
  export CLUSTER=slurmx SESSION=MathBench_Prover
  export SBATCH_JOB_NAME='$JOB'
  export SLURM_EVAL_WALLTIME='$WALLTIME'
  export RPC_Host='$LOGIN_IB0:$RPC_PORT' AUTO_START_RPC_SERVER=0
  exec python3 evaluation/evaluator_top.py agent-putnam '$DRIVER' \
       --case-category '$CASE_CATEGORY' --result '$RESULT_DB' \
       --log-dir '$LOG_DIR' --timeout-seconds 14400 ${FWD[*]}
" >> "$EVAL_LOG" 2>&1 &
EVAL_PGID=$!
echo "$EVAL_PGID" > "$STATE_DIR/eval.pgid"
log "orchestrator running (pgid $EVAL_PGID)"

# ---- blocker (1): post-launch completeness gate ---------------------------
log "waiting up to ${GATE_DEADLINE}s for all $EXPECT_REPLS REPLs across $NUM_NODES nodes..."
gate_deadline=$((SECONDS + GATE_DEADLINE))
until fleet_ready "$JOB" 0; do
  if ! kill -0 "$EVAL_PGID" 2>/dev/null; then
    log "ERROR: orchestrator (pgid $EVAL_PGID) exited during bring-up — see $EVAL_LOG"
    break
  fi
  if [ $SECONDS -gt $gate_deadline ]; then
    log "ERROR: fleet did not reach full $EXPECT_REPLS-way capacity in ${GATE_DEADLINE}s — ABORTING to avoid a silently-degraded run"
    log "aborting: killing orchestrator group, scancel $JOB, killing RPC host"
    kill -- -"$EVAL_PGID" 2>/dev/null || true
    scancel --name="$JOB" 2>/dev/null || true
    [ -n "${RPC_PID:-}" ] && kill "$RPC_PID" 2>/dev/null || true
    die "degraded fleet aborted; inspect $EVAL_LOG and compute logs under cache/repl_tmps/"
  fi
  sleep 15
done

if fleet_ready "$JOB" 1; then
  log "READY: job $JOB holds $NUM_NODES nodes, all $EXPECT_REPLS REPLs reachable; eval running."
  log "  result db : $RESULT_DB"
  log "  agent logs: $LOG_DIR"
  log "  eval log  : $EVAL_LOG"
  log "  periodic  : JOB=$JOB tools/aoa_putnam_eval/run_fleet_eval.sh --check"
  log "  stop      : tools/aoa_putnam_eval/stop_fleet_eval.sh"
else
  log "NOTE: orchestrator exited before full capacity; check $EVAL_LOG (may have finished a tiny smoke set)."
fi
