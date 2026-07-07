#!/usr/bin/env python3
"""Plot per-case USD budget cap vs pass rate from evaluation result DBs.

Each point (X, Y) means: if each case is given a budget of X USD,
the pass rate is Y%.  A case counts as passed when it succeeded AND
its cost was <= X.

Usage:
    python -m tools.agent_cost.plt_usd db1.sqlite [db2.sqlite ...]
    python -m tools.agent_cost.plt_usd db1.sqlite:label1 db2.sqlite:label2
    python -m tools.agent_cost.plt_usd db1.sqlite -o output.png
"""

import argparse
import io
import pickle
import sys
from enum import Enum

from sqlitedict import SqliteDict
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, LogLocator, NullFormatter


# Result DBs are SqliteDict stores of pickled ``evaluation.evaluator.Result``
# objects whose ``status`` is an ``evaluation.evaluator.Status`` enum.  To read
# them standalone -- without importing the (heavy) MLML evaluation stack -- we
# unpickle through a custom Unpickler that maps just those two classes to the
# local stand-ins below.  Nothing else from MLML is ever imported.

class Status(Enum):
    SUCCESS = "SUCCESS"
    FAIL = "FAIL"
    CASE_NOT_AVAILABLE = "CASE_NOT_AVAILABLE"


class Result:
    """Plain stand-in for evaluation.evaluator.Result (the fields we read)."""
    status = None
    data = None


class _ResultUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if module == "evaluation.evaluator":
            if name == "Status":
                return Status
            if name == "Result":
                return Result
        return super().find_class(module, name)


def _decode(raw) -> object:
    """SqliteDict value decoder: unpickle MLML Result objects standalone."""
    return _ResultUnpickler(io.BytesIO(bytes(raw))).load()


def load_case_filter(path: str) -> set[str]:
    """Read a benchmark case list (one case name per line) into a set.

    Blank lines and leading/trailing whitespace are ignored.
    """
    with open(path) as fh:
        return {line.strip() for line in fh if line.strip()}


def load_entries(db_path: str,
                 keep: set[str] | None = None) -> list[tuple[float, float, bool]]:
    """Load a result DB and return [(cost, quota_wait_time, is_success), ...].

    When ``keep`` is given, only cases whose key is in that set are considered.
    CASE_NOT_AVAILABLE entries are excluded.
    Cases without cost data are treated as zero-cost.
    """
    entries = []
    with SqliteDict(db_path, flag='r', decode=_decode) as db:
        for key, result in db.items():
            if keep is not None and key not in keep:
                continue
            if result.status == Status.CASE_NOT_AVAILABLE:
                continue
            cost = 0.0
            quota_wait = 0.0
            if result.data and "costs" in result.data:
                cost = sum(c.get("cost_usd", 0.0) for c in result.data["costs"])
                quota_wait = sum(c.get("quota_wait_time", 0.0) for c in result.data["costs"])
            entries.append((cost, quota_wait, result.status == Status.SUCCESS))
    return entries


def budget_curve(entries: list[tuple[float, float, bool]]) -> tuple[list[float], list[float]]:
    """Return (budget_thresholds, pass_rates) for per-case budget cap plot.

    For each unique cost value X among successful cases, compute
    pass_rate = (cases that succeeded with cost <= X) / total_cases.
    """
    if not entries:
        return [], []

    total = len(entries)
    success_costs = sorted(c for c, _qw, s in entries if s)
    if not success_costs:
        return [0.0], [0.0]

    budgets = []
    rates = []
    for i, cost in enumerate(success_costs):
        rate = 100.0 * (i + 1) / total
        if budgets and budgets[-1] == cost:
            rates[-1] = rate
        else:
            budgets.append(cost)
            rates.append(rate)

    return budgets, rates


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
    parser.add_argument("-f", "--filter-file", default=None, metavar="FILE",
                        help="Only consider benchmark cases listed in FILE "
                             "(one case name per line)")
    parser.add_argument("--title", default=None, help="Figure title")
    parser.add_argument("--dpi", type=int, default=150, help="Output DPI (default 150)")
    parser.add_argument("--log", action="store_true", help="Use logarithmic X-axis")
    args = parser.parse_args()

    keep = load_case_filter(args.filter_file) if args.filter_file else None
    if keep is not None:
        print(f"Filtering to {len(keep)} cases listed in {args.filter_file}")

    fig, ax = plt.subplots(figsize=(8, 5))
    show_legend = len(args.dbs) > 1

    for db_arg in args.dbs:
        path, label = parse_db_arg(db_arg)
        entries = load_entries(path, keep)
        if not entries:
            print(f"Warning: no plottable entries in {path}", file=sys.stderr)
            continue

        total = len(entries)
        successes = sum(1 for *_, s in entries if s)
        total_cost = sum(c for c, _qw, _s in entries)
        success_cost = sum(c for c, _qw, s in entries if s)
        total_quota_wait = sum(qw for _c, qw, _s in entries)
        display = label or path
        avg_success = f"${success_cost/successes:.4f}" if successes else "N/A"
        quota_str = f", quota_wait {total_quota_wait:.0f}s" if total_quota_wait > 0 else ""
        print(f"{display}: {total} cases, {successes} passed ({100*successes/total:.1f}%), "
              f"total ${total_cost:.2f}, avg {avg_success}/pass{quota_str}")

        budgets, rates = budget_curve(entries)
        ax.plot(budgets, rates, label=label)

    ax.set_xlabel("Per-Case Budget (USD)")
    ax.set_ylabel("Pass Rate (%)")
    ax.set_title(args.title or "Per-Case Budget vs Pass Rate")
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
