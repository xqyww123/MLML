#!/usr/bin/env python3
"""Plot per-case tool-call limit vs pass rate from evaluation result DBs.

Each point (X, Y) means: if each case is given a budget of X tool calls,
the pass rate is Y%.  A case counts as passed when it succeeded AND
its tool-call count was <= X.

Usage:
    python -m tools.agent_cost.plt_toolcall_num db1.sqlite [db2.sqlite ...]
    python -m tools.agent_cost.plt_toolcall_num db1.sqlite:label1 db2.sqlite:label2
    python -m tools.agent_cost.plt_toolcall_num db1.sqlite -o output.png
"""

import argparse
import sys
from sqlitedict import SqliteDict
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, LogLocator, NullFormatter

from evaluation.evaluator import Status


def load_entries(db_path: str) -> list[tuple[int, bool]]:
    """Load a result DB and return [(tool_call_count, is_success), ...].

    CASE_NOT_AVAILABLE entries are excluded.
    Cases without cost data are treated as zero tool calls.
    """
    entries = []
    with SqliteDict(db_path, flag='r') as db:
        for _key, result in db.items():
            if result.status == Status.CASE_NOT_AVAILABLE:
                continue
            tc = 0
            if result.data and "costs" in result.data:
                tc = sum(c.get("tool_calls", 0) for c in result.data["costs"])
            entries.append((tc, result.status == Status.SUCCESS))
    return entries


def budget_curve(entries: list[tuple[int, bool]]) -> tuple[list[int], list[float]]:
    """Return (tool_call_thresholds, pass_rates) for per-case budget plot."""
    if not entries:
        return [], []

    total = len(entries)
    success_counts = sorted(tc for tc, s in entries if s)
    if not success_counts:
        return [0], [0.0]

    thresholds: list[int] = []
    rates: list[float] = []
    for i, tc in enumerate(success_counts):
        rate = 100.0 * (i + 1) / total
        if thresholds and thresholds[-1] == tc:
            rates[-1] = rate
        else:
            thresholds.append(tc)
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
    parser = argparse.ArgumentParser(description="Plot per-case tool-call limit vs pass rate.")
    parser.add_argument("dbs", nargs="+", metavar="DB[:LABEL]",
                        help="Path to result SQLite DB, optionally with :label suffix")
    parser.add_argument("-o", "--output", default=None,
                        help="Save figure to file instead of showing interactively")
    parser.add_argument("--title", default=None, help="Figure title")
    parser.add_argument("--dpi", type=int, default=150, help="Output DPI (default 150)")
    parser.add_argument("--log", action="store_true", help="Use logarithmic X-axis")
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
        total_tc = sum(tc for tc, _ in entries)
        success_tc = sum(tc for tc, s in entries if s)
        display = label or path
        avg_success = f"{success_tc/successes:.1f}" if successes else "N/A"
        print(f"{display}: {total} cases, {successes} passed ({100*successes/total:.1f}%), "
              f"total {total_tc} tool calls, avg {avg_success}/pass")

        thresholds, rates = budget_curve(entries)
        ax.plot(thresholds, rates, label=label)

    ax.set_xlabel("Per-Case Tool Call Limit")
    ax.set_ylabel("Pass Rate (%)")
    ax.set_title(args.title or "Per-Case Tool Call Limit vs Pass Rate")
    ax.set_ylim(bottom=0)
    if args.log:
        ax.set_xscale("log")
        ax.xaxis.set_major_locator(LogLocator(base=10, subs=(1, 2, 5), numticks=20))
        ax.xaxis.set_major_formatter(FuncFormatter(
            lambda x, _: f"{x:g}" if x == int(x) else f"{x:.2f}"))
        ax.xaxis.set_minor_locator(LogLocator(base=10, subs="auto", numticks=20))
        ax.xaxis.set_minor_formatter(NullFormatter())
    else:
        ax.set_xlim(left=0)
    if show_legend:
        ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    if args.log:
        fig.canvas.draw()
        seen: set[str] = set()
        for lbl in ax.xaxis.get_ticklabels():
            t = lbl.get_text()
            if t in seen:
                lbl.set_visible(False)
            else:
                seen.add(t)

    if args.output:
        fig.savefig(args.output, dpi=args.dpi)
        print(f"Saved to {args.output}")
    else:
        plt.show()


if __name__ == "__main__":
    main()
