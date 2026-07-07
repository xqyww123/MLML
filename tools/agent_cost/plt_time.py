#!/usr/bin/env python3
"""Plot per-case time limit vs pass rate from evaluation result DBs.

Each point (X, Y) means: if each case is given a time limit of X seconds,
the pass rate is Y%.  A case counts as passed when it succeeded AND
its wall-clock time was <= X.

Usage:
    python -m tools.agent_cost.plt_time db1.sqlite [db2.sqlite ...]
    python -m tools.agent_cost.plt_time db1.sqlite:label1 db2.sqlite:label2
    python -m tools.agent_cost.plt_time db1.sqlite -o output.png
"""

import argparse
import sys
from sqlitedict import SqliteDict
import matplotlib.pyplot as plt

from evaluation.evaluator import Status


def load_case_filter(path: str) -> set[str]:
    """Read a benchmark case list (one case name per line) into a set.

    Blank lines and leading/trailing whitespace are ignored.
    """
    with open(path) as fh:
        return {line.strip() for line in fh if line.strip()}


def load_entries(db_path: str,
                 keep: set[str] | None = None) -> list[tuple[float, float, bool]]:
    """Load a result DB and return [(elapsed_seconds, model_time_seconds, is_success), ...].

    When ``keep`` is given, only cases whose key is in that set are considered.
    CASE_NOT_AVAILABLE entries are excluded.
    elapsed_time is stored as milliseconds in Result; converted to seconds here.
    model_time comes from cost data (already in seconds).
    """
    entries = []
    with SqliteDict(db_path, flag='r') as db:
        for key, result in db.items():
            if keep is not None and key not in keep:
                continue
            if result.status == Status.CASE_NOT_AVAILABLE:
                continue
            elapsed_s = sum(result.elapsed_time) / 1000.0 if result.elapsed_time else 0.0
            model_time = 0.0
            if result.data and "costs" in result.data:
                model_time = sum(c.get("model_time", 0.0) for c in result.data["costs"])
            entries.append((elapsed_s, model_time, result.status == Status.SUCCESS))
    return entries


def budget_curve(values: list[float], total: int) -> tuple[list[float], list[float]]:
    """Return (thresholds, pass_rates) for a per-case budget plot.

    ``values`` contains the metric (time / model_time) for successful cases only.
    ``total`` is the total number of cases (including failures).
    """
    if not values:
        return [0.0], [0.0]

    values = sorted(values)
    values = [v / 60.0 for v in values]
    thresholds = []
    rates = []
    for i, v in enumerate(values):
        rate = 100.0 * (i + 1) / total
        if thresholds and thresholds[-1] == v:
            rates[-1] = rate
        else:
            thresholds.append(v)
            rates.append(rate)

    return thresholds, rates


def parse_db_arg(arg: str) -> tuple[str, str | None]:
    """Parse 'path' or 'path:label' into (path, label)."""
    if ':' in arg:
        idx = arg.rindex(':')
        candidate_path = arg[:idx]
        candidate_label = arg[idx + 1:]
        if candidate_label and '/' not in candidate_label and '\\' not in candidate_label:
            return candidate_path, candidate_label
    return arg, None


def main():
    parser = argparse.ArgumentParser(description="Plot per-case time limit vs pass rate.")
    parser.add_argument("dbs", nargs="+", metavar="DB[:LABEL]",
                        help="Path to result SQLite DB, optionally with :label suffix")
    parser.add_argument("-o", "--output", default=None,
                        help="Save figure to file instead of showing interactively")
    parser.add_argument("-f", "--filter-file", default=None, metavar="FILE",
                        help="Only consider benchmark cases listed in FILE "
                             "(one case name per line)")
    parser.add_argument("--title", default=None, help="Figure title")
    parser.add_argument("--dpi", type=int, default=150, help="Output DPI (default 150)")
    parser.add_argument("--model-time", action="store_true",
                        help="Also plot model thinking time as a dashed line")
    parser.add_argument("--log", action="store_true", help="Use logarithmic X-axis")
    args = parser.parse_args()

    keep = load_case_filter(args.filter_file) if args.filter_file else None
    if keep is not None:
        print(f"Filtering to {len(keep)} cases listed in {args.filter_file}")

    fig, ax = plt.subplots(figsize=(8, 5))
    show_legend = len(args.dbs) > 1 or args.model_time

    for db_arg in args.dbs:
        path, label = parse_db_arg(db_arg)
        entries = load_entries(path, keep)
        if not entries:
            print(f"Warning: no plottable entries in {path}", file=sys.stderr)
            continue

        total = len(entries)
        successes = sum(1 for *_, s in entries if s)
        total_time = sum(t for t, _mt, _s in entries)
        success_time = sum(t for t, _mt, s in entries if s)
        display = label or path
        avg_success = f"{success_time/successes:.1f}s" if successes else "N/A"
        print(f"{display}: {total} cases, {successes} passed ({100*successes/total:.1f}%), "
              f"total {total_time:.0f}s, avg {avg_success}/pass")

        success_elapsed = [t for t, _mt, s in entries if s]
        thresholds, rates = budget_curve(success_elapsed, total)
        line, = ax.plot(thresholds, rates, label=label)

        if args.model_time:
            success_mt = [mt for _t, mt, s in entries if s]
            mt_thresh, mt_rates = budget_curve(success_mt, total)
            mt_label = f"{label} (model)" if label else "model time"
            ax.plot(mt_thresh, mt_rates, linestyle="--", color=line.get_color(),
                    label=mt_label)

    ax.set_xlabel("Per-Case Time Limit (min)")
    ax.set_ylabel("Pass Rate (%)")
    ax.set_title(args.title or "Per-Case Time Limit vs Pass Rate")
    ax.set_ylim(bottom=0)
    if args.log:
        ax.set_xscale("log")
    else:
        ax.set_xlim(left=0)
    if show_legend:
        ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    if args.output:
        fig.savefig(args.output, dpi=args.dpi)
        print(f"Saved to {args.output}")
    else:
        plt.show()


if __name__ == "__main__":
    main()
