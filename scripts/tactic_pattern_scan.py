#!/usr/bin/env python3
"""Detect repeated tactic-block patterns across the Lean corpus.

Purpose
-------
Supports the tactic self-improvement loop (docs/tactic_development.md):
find tactic-line sequences that recur across ``TNLean/``, so they can be
recorded in the pattern ledger (docs/tactic_patterns.md) and eventually
promoted to a custom tactic, macro, or simp set.

Method
------
* Walk ``TNLean/**/*.lean`` (excluding ``Archive/`` and ``Scratch/``).
* Keep only lines that look like tactic invocations (leading keyword from
  ``TACTIC_HEADS``, or a focus-dot line).  Comments and string literals are
  not parsed; this is a heuristic scanner, not a Lean parser.
* Normalize each line (strip indentation, collapse whitespace).
* Slide windows of ``--min-window`` .. ``--max-window`` consecutive tactic
  lines over each file and count identical windows across the corpus.
* Report windows seen at least ``--min-count`` times, largest
  ``lines x occurrences`` savings first.  Sub-windows of a reported window
  are suppressed so each pattern is reported once, maximally.

Usage
-----
    python3 scripts/tactic_pattern_scan.py                # default scan
    python3 scripts/tactic_pattern_scan.py --min-count 5  # stricter
    python3 scripts/tactic_pattern_scan.py --top 10 --show-locations 5

Exit code is always 0; this is a reporting tool, not a lint gate.
"""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path

# Keywords that begin a tactic invocation line.  Deliberately conservative:
# missing a tactic keyword only means some duplication goes unreported.
TACTIC_HEADS = (
    "simp",
    "simpa",
    "rw",
    "rewrite",
    "exact",
    "apply",
    "refine",
    "intro",
    "intros",
    "rintro",
    "obtain",
    "rcases",
    "cases",
    "constructor",
    "ext",
    "funext",
    "subst",
    "unfold",
    "change",
    "show",
    "calc",
    "have",
    "haveI",
    "letI",
    "set",
    "norm_num",
    "ring",
    "ring_nf",
    "field_simp",
    "positivity",
    "omega",
    "decide",
    "trivial",
    "rfl",
    "symm",
    "push_cast",
    "norm_cast",
    "congr",
    "gcongr",
    "convert",
    "conv",
    "dsimp",
    "delta",
    "specialize",
    "use",
    "exists",
    "left",
    "right",
    "induction",
    "injection",
    "contradiction",
    "absurd",
    "by_cases",
    "by_contra",
    "push_neg",
    "nlinarith",
    "linarith",
    "linear_combination",
    "aesop",
    "tauto",
    "fun_prop",
    "measurability",
    "continuity",
    "bound",
    "grind",
    "mpv_ext",
    "transfer_simp",
)

TACTIC_LINE_RE = re.compile(
    r"^\s*(?:·\s*)?(?:" + "|".join(re.escape(t) for t in sorted(set(TACTIC_HEADS))) + r")\b"
)

EXCLUDED_DIRS = {"Archive", "Scratch"}


def tactic_lines(path: Path) -> list[tuple[int, str]]:
    """Return (line-number, normalized-text) for tactic-looking lines."""
    out: list[tuple[int, str]] = []
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = raw.strip()
        if not stripped or stripped.startswith("--") or stripped.startswith("/-"):
            continue
        if TACTIC_LINE_RE.match(raw):
            out.append((lineno, re.sub(r"\s+", " ", stripped)))
    return out


def consecutive_runs(lines: list[tuple[int, str]]) -> list[list[tuple[int, str]]]:
    """Split tactic lines into runs of consecutive source lines."""
    runs: list[list[tuple[int, str]]] = []
    current: list[tuple[int, str]] = []
    for item in lines:
        if current and item[0] != current[-1][0] + 1:
            runs.append(current)
            current = []
        current.append(item)
    if current:
        runs.append(current)
    return runs


def scan(root: Path, min_window: int, max_window: int, min_count: int):
    windows: dict[tuple[str, ...], list[tuple[str, int]]] = defaultdict(list)
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root.parent)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        for run in consecutive_runs(tactic_lines(path)):
            for size in range(min_window, max_window + 1):
                for i in range(len(run) - size + 1):
                    chunk = run[i : i + size]
                    key = tuple(text for _, text in chunk)
                    windows[key].append((str(rel), chunk[0][0]))

    hits = {k: v for k, v in windows.items() if len(v) >= min_count}

    # Suppress windows that are sub-sequences of a larger reported window
    # with the same occurrence count (they carry no extra information).
    keys_by_size = sorted(hits, key=len, reverse=True)
    kept: list[tuple[str, ...]] = []
    for key in keys_by_size:
        joined = "\n".join(key)
        redundant = any(
            joined in "\n".join(big) and len(hits[big]) >= len(hits[key]) for big in kept
        )
        if not redundant:
            kept.append(key)
    return {k: hits[k] for k in kept}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", default="TNLean", help="source root to scan")
    parser.add_argument("--min-window", type=int, default=3, help="minimum lines per pattern")
    parser.add_argument("--max-window", type=int, default=8, help="maximum lines per pattern")
    parser.add_argument("--min-count", type=int, default=3, help="minimum occurrences to report")
    parser.add_argument("--top", type=int, default=20, help="number of patterns to print")
    parser.add_argument(
        "--show-locations", type=int, default=3, help="locations to print per pattern"
    )
    args = parser.parse_args()

    results = scan(Path(args.root), args.min_window, args.max_window, args.min_count)
    ranked = sorted(
        results.items(), key=lambda kv: len(kv[0]) * len(kv[1]), reverse=True
    )

    if not ranked:
        print("No repeated tactic patterns found at the current thresholds.")
        return

    print(f"# Repeated tactic patterns (>= {args.min_count} occurrences)")
    print(f"# Ranked by lines x occurrences; showing top {args.top}\n")
    for key, locs in ranked[: args.top]:
        savings = len(key) * len(locs)
        print(f"## {len(locs)} occurrences x {len(key)} lines (weight {savings})")
        for line in key:
            print(f"    {line}")
        shown = locs[: args.show_locations]
        print("  at: " + ", ".join(f"{f}:{n}" for f, n in shown), end="")
        if len(locs) > len(shown):
            print(f" (+{len(locs) - len(shown)} more)")
        else:
            print()
        print()


if __name__ == "__main__":
    main()
