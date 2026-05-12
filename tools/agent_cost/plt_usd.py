#!/usr/bin/env python3
"""Plot cumulative USD budget vs pass rate from evaluation result DBs.

Each point (X, Y) means: with a total budget of X USD, the pass rate is Y.
Cases are sorted by per-case cost ascending (cheapest first), so the curve
shows the best achievable pass rate for each budget level.

Usage:
    python -m tools.agent_cost.plt_usd db1.sqlite [db2.sqlite ...]
    python -m tools.agent_cost.plt_usd db1.sqlite:label1 db2.sqlite:label2
    python -m tools.agent_cost.plt_usd db1.sqlite -o output.png
"""

import argparse
import sys
from sqlitedict import SqliteDict
import matplotlib.pyplot as plt

from evaluation.evaluator import Status


def load_entries(db_path: str) -> list[tuple[float, bool]]:
    """Load a result DB and return [(cost, is_success), ...].

    CASE_NOT_AVAILABLE entries are excluded.
    Cases without cost data are treated as zero-cost.
    """
    entries = []
    with SqliteDict(db_path, flag='r') as db:
        for _key, result in db.items():
            if result.status == Status.CASE_NOT_AVAILABLE:
                continue
            cost = 0.0
            if result.data and "costs" in result.data:
                cost = sum(c.get("cost_usd", 0.0) for c in result.data["costs"])
            entries.append((cost, result.status == Status.SUCCESS))
    return entries


def cumulative_curve(entries: list[tuple[float, bool]]) -> tuple[list[float], list[float]]:
    """Sort entries by cost ascending and return (cumulative_usd, cumulative_pass_rate)."""
    if not entries:
        return [], []

    entries = sorted(entries, key=lambda e: e[0])
    total = len(entries)
    cum_usd = []
    cum_rate = []
    running_cost = 0.0
    running_success = 0
    for cost, is_success in entries:
        running_cost += cost
        if is_success:
            running_success += 1
        cum_usd.append(running_cost)
        cum_rate.append(100.0 * running_success / total)

    return cum_usd, cum_rate


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
    parser = argparse.ArgumentParser(description="Plot cumulative USD budget vs pass rate.")
    parser.add_argument("dbs", nargs="+", metavar="DB[:LABEL]",
                        help="Path to result SQLite DB, optionally with :label suffix")
    parser.add_argument("-o", "--output", default=None,
                        help="Save figure to file instead of showing interactively")
    parser.add_argument("--title", default=None, help="Figure title")
    parser.add_argument("--dpi", type=int, default=150, help="Output DPI (default 150)")
    args = parser.parse_args()

    fig, ax = plt.subplots(figsize=(8, 5))
    show_legend = len(args.dbs) > 1

    for db_arg in args.dbs:
        path, label = parse_db_arg(db_arg)
        entries = load_entries(path)
        if not entries:
            print(f"Warning: no plottable entries in {path}", file=sys.stderr)
            continue

        total = len(entries)
        successes = sum(1 for _, s in entries if s)
        total_cost = sum(c for c, _ in entries)
        success_cost = sum(c for c, s in entries if s)
        display = label or path
        avg_success = f"${success_cost/successes:.4f}" if successes else "N/A"
        print(f"{display}: {total} cases, {successes} passed ({100*successes/total:.1f}%), "
              f"total ${total_cost:.2f}, avg {avg_success}/pass")

        cum_usd, cum_rate = cumulative_curve(entries)
        ax.plot(cum_usd, cum_rate, label=label)

    ax.set_xlabel("Cumulative USD Cost")
    ax.set_ylabel("Pass Rate (%)")
    ax.set_title(args.title or "Budget vs Pass Rate")
    ax.set_ylim(bottom=0)
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
