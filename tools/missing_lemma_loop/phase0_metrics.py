#!/usr/bin/env python3
"""Phase 0 (non-invasive) telemetry for the missing-lemma loop.

Reconstructs claim-production rate, adjudication latency/drain, backlog over
time, and verdict precision purely from artifacts the running watcher ALREADY
produces — `ledger.json`, `verdicts/verdict_*.json` (filename embeds the
adjudication start unix-stamp; file mtime is the finish), and `events.jsonl`.
It does NOT import or modify the watcher and needs NO restart: it is the
cheapest decisive measurement for the parallelism decision — is discovery
*prover-bound* (the single adjudicator keeps up, backlog ~0) or
*adjudication-bound* (claims queue behind the lone max_workers=1 slot)?

Usage:
    python tools/missing_lemma_loop/phase0_metrics.py            # all-time
    python tools/missing_lemma_loop/phase0_metrics.py --since 2026-06-16T15:45
    python tools/missing_lemma_loop/phase0_metrics.py --json     # machine-readable
"""
import argparse
import glob
import json
import os
import re
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_STATE = ROOT / "missing_lemma_loop_state"

TERMINAL = {"missing_import", "not_found", "already_in_heap", "duplicate",
            "import_failed", "provided_but_unfindable", "imported"}
# Verdicts that mean "the loop found a genuinely-absent lemma it could act on".
VALUABLE = {"missing_import", "imported"}


def parse_iso(s):
    try:
        return datetime.fromisoformat(s)
    except Exception:
        return None


def load_ledger(state):
    d = json.load(open(state / "ledger.json"))
    if isinstance(d, list):
        return d
    return d.get("entries") or d.get("claims") or list(d.values())


def index_verdicts(state):
    """claim_id -> latest (finish_dt, start_dt, batch_file); plus per-batch rows."""
    idx, batches = {}, []
    for f in sorted(glob.glob(str(state / "verdicts" / "verdict_*.json"))):
        try:
            obj = json.load(open(f))
        except Exception:
            continue
        base = os.path.basename(f)
        m = re.search(r"_(\d{10})\.json$", base)
        start = datetime.fromtimestamp(int(m.group(1))) if m else None
        finish = datetime.fromtimestamp(os.path.getmtime(f))
        search = {v["claim_id"]: v.get("verdict") for v in obj.get("verdicts", [])}
        dedup = {v["claim_id"]: v.get("verdict") for v in obj.get("dedup", [])}
        ids = set(search) | set(dedup)
        batches.append(dict(file=base, start=start, finish=finish, n=len(ids),
                            search=search, dedup=dedup))
        for cid in ids:
            prev = idx.get(cid)
            if prev is None or finish > prev[0]:
                idx[cid] = (finish, start, base)
    return idx, batches


def fmt_dt(dt):
    return dt.strftime("%m-%d %H:%M:%S") if dt else "?"


def fmt_dur(secs):
    if secs is None:
        return "?"
    m, s = divmod(int(secs), 60)
    return f"{m}m{s:02d}s" if m else f"{s}s"


def analyze(state, since):
    ledger = load_ledger(state)
    vidx, batches = index_verdicts(state)

    # Window: claims whose first_seen >= since (None = all-time).
    claims = []
    for e in ledger:
        fs = parse_iso(e.get("first_seen", ""))
        if fs is None:
            continue
        if since and fs < since:
            continue
        claims.append((fs, e))
    claims.sort(key=lambda x: x[0])

    if not claims:
        return dict(empty=True, n_batches=len(batches))

    # --- production / drain / backlog timeline ---
    events = []  # (dt, +1|-1, claim_id)
    drained = 0
    latencies = []
    for fs, e in claims:
        cid = e["id"]
        events.append((fs, +1, cid))
        v = vidx.get(cid)
        if v:
            finish, start, _ = v
            events.append((finish, -1, cid))
            drained += 1
            if start:
                latencies.append((finish - start).total_seconds())
    events.sort(key=lambda x: (x[0], x[1]))

    backlog = 0
    max_backlog = 0
    last_t = events[0][0]
    busy_secs = 0.0          # time-integral of backlog (claim-seconds waiting)
    span_secs = 0.0
    pos_secs = 0.0           # wall time with backlog > 0
    for t, delta, _ in events:
        dt = (t - last_t).total_seconds()
        span_secs += dt
        busy_secs += backlog * dt
        if backlog > 0:
            pos_secs += dt
        backlog += delta
        max_backlog = max(max_backlog, backlog)
        last_t = t

    first_t = claims[0][0]
    last_seen = claims[-1][0]
    window_hr = max((last_seen - first_t).total_seconds() / 3600.0, 1e-9)
    n = len(claims)

    # --- precision (final ledger status over the window) ---
    status_hist = {}
    for _, e in claims:
        status_hist[e["status"]] = status_hist.get(e["status"], 0) + 1
    adjudicated = sum(v for k, v in status_hist.items() if k in TERMINAL)
    valuable = sum(v for k, v in status_hist.items() if k in VALUABLE)

    # --- bottleneck verdict ---
    avg_backlog = busy_secs / span_secs if span_secs else 0.0
    frac_backlogged = pos_secs / span_secs if span_secs else 0.0
    lat_mean = sum(latencies) / len(latencies) if latencies else None
    lat_max = max(latencies) if latencies else None
    # Adjudication occupies one serial slot; if the queue is rarely non-empty
    # and backlog rarely exceeds the in-flight batch, the prover is the limiter.
    if max_backlog <= 2 and frac_backlogged < 0.25:
        verdict = "PROVER-BOUND (single adjudicator keeps up; raising adjudication concurrency buys little — the production lever, C, dominates)"
    elif avg_backlog >= 2 or frac_backlogged >= 0.5:
        verdict = "ADJUDICATION-BOUND (claims queue behind the lone max_workers=1 slot; widen _AGENT_POOL first — A is the lever)"
    else:
        verdict = "MIXED / INCONCLUSIVE (accumulate more cases before gating; judge wants >=30-50)"

    return dict(
        empty=False, n_claims=n, window_first=first_t, window_last=last_seen,
        window_hr=window_hr, prod_per_hr=n / window_hr,
        drained=drained, undrained=n - drained,
        lat_mean=lat_mean, lat_max=lat_max, n_latencies=len(latencies),
        max_backlog=max_backlog, avg_backlog=avg_backlog,
        frac_backlogged=frac_backlogged,
        status_hist=status_hist, adjudicated=adjudicated, valuable=valuable,
        n_batches=len(batches), verdict=verdict,
        cases=len({e["case"] for _, e in claims}),
    )


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--state-dir", default=str(DEFAULT_STATE))
    p.add_argument("--since", help="ISO timestamp; only claims first_seen >= this")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    args = p.parse_args()

    state = Path(args.state_dir)
    since = parse_iso(args.since) if args.since else None
    r = analyze(state, since)

    if args.json:
        out = dict(r)
        for k in ("window_first", "window_last"):
            if out.get(k):
                out[k] = out[k].isoformat()
        print(json.dumps(out, ensure_ascii=False, indent=2, default=str))
        return

    print("=" * 64)
    print("  Missing-lemma loop — Phase 0 telemetry (non-invasive)")
    print("=" * 64)
    if r.get("empty"):
        print(f"  No claims in window (verdict files on disk: {r['n_batches']}).")
        print("  The (re)started run has not surfaced claims yet — re-run later.")
        return
    print(f"  Window      : {fmt_dt(r['window_first'])} → {fmt_dt(r['window_last'])} "
          f"({r['window_hr']:.2f} h, {r['cases']} cases)")
    print(f"  Claims       : {r['n_claims']}  "
          f"({r['drained']} adjudicated, {r['undrained']} still in flight)")
    print(f"  Production   : {r['prod_per_hr']:.1f} claims/hr")
    print(f"  Adjudication : mean {fmt_dur(r['lat_mean'])}, max {fmt_dur(r['lat_max'])} "
          f"(n={r['n_latencies']} batches timed)")
    print(f"  Backlog      : max {r['max_backlog']}, avg {r['avg_backlog']:.2f}, "
          f"{r['frac_backlogged']*100:.0f}% of wall-time non-empty")
    print(f"  Precision    : {r['valuable']} valuable (missing_import/imported) "
          f"of {r['adjudicated']} adjudicated")
    print(f"  Status hist  : " +
          ", ".join(f"{k}={v}" for k, v in sorted(r["status_hist"].items())))
    print("-" * 64)
    print(f"  VERDICT: {r['verdict']}")
    print("=" * 64)


if __name__ == "__main__":
    main()
