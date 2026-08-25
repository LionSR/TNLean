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
* Report declaration signatures longer than ``--signature-lines`` source
  lines.  This is a soft packaging signal, not a style failure.
* Report theorem and lemma proofs longer than ``--proof-lines`` source lines.
  This is a soft decomposition signal, not a style failure.

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

from lean_import_syntax import strip_lean_comments

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
DECLARATION_START_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|inductive|opaque|alias|instance)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)
THEOREM_START_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)


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


def long_signatures(root: Path, threshold: int) -> list[tuple[int, str, int, str]]:
    """Return declaration signatures spanning more than ``threshold`` lines.

    This deliberately line-based pass ends a signature at the first ``:=`` or
    declaration-level ``where`` token. It is advisory: an unusual declaration
    syntax may be omitted or conservatively overcounted, but it never changes
    the scanner's successful exit status.
    """
    hits: list[tuple[int, str, int, str]] = []
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root.parent)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        source = path.read_text(encoding="utf-8")
        uncommented, error = strip_lean_comments(source)
        if error is not None:
            continue
        lines = uncommented.splitlines()
        index = 0
        while index < len(lines):
            match = DECLARATION_START_RE.match(lines[index])
            if match is None:
                index += 1
                continue
            start = index
            end = index
            while end < len(lines):
                line = lines[end]
                if ":=" in line or re.search(r"\bwhere\s*$", line):
                    break
                end += 1
            length = end - start + 1
            if length > threshold:
                hits.append((length, str(rel), start + 1, match.group(1)))
            index = max(index + 1, end + 1)
    return sorted(hits, reverse=True)


def long_proofs(root: Path, threshold: int) -> list[tuple[int, str, int, str]]:
    """Return theorem/lemma bodies spanning more than ``threshold`` lines.

    Boundaries are the next named declaration after comments are erased.  The
    result is advisory and intentionally undercounts declarations containing
    nested named declarations rather than pretending to be a Lean parser.
    """
    hits: list[tuple[int, str, int, str]] = []
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root.parent)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        source = path.read_text(encoding="utf-8")
        uncommented, error = strip_lean_comments(source)
        if error is not None:
            continue
        lines = uncommented.splitlines()
        declarations = [
            index for index, line in enumerate(lines) if DECLARATION_START_RE.match(line)
        ]
        for position, start in enumerate(declarations):
            match = THEOREM_START_RE.match(lines[start])
            if match is None:
                continue
            boundary = declarations[position + 1] if position + 1 < len(declarations) else len(lines)
            body_start = next(
                (index for index in range(start, boundary) if ":=" in lines[index]),
                None,
            )
            if body_start is None:
                continue
            end = boundary
            while end > body_start and not lines[end - 1].strip():
                end -= 1
            length = end - body_start
            if length > threshold:
                hits.append((length, str(rel), start + 1, match.group(1)))
    return sorted(hits, reverse=True)


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
    parser.add_argument(
        "--signature-lines",
        type=int,
        default=20,
        help="report declaration signatures longer than this many source lines",
    )
    parser.add_argument(
        "--top-signatures",
        type=int,
        default=20,
        help="number of long declaration signatures to print",
    )
    parser.add_argument(
        "--proof-lines",
        type=int,
        default=150,
        help="report theorem or lemma bodies longer than this many source lines",
    )
    parser.add_argument(
        "--top-proofs",
        type=int,
        default=20,
        help="number of long theorem or lemma bodies to print",
    )
    args = parser.parse_args()

    results = scan(Path(args.root), args.min_window, args.max_window, args.min_count)
    ranked = sorted(
        results.items(), key=lambda kv: len(kv[0]) * len(kv[1]), reverse=True
    )

    signatures = long_signatures(Path(args.root), args.signature_lines)
    proofs = long_proofs(Path(args.root), args.proof_lines)

    if not ranked:
        print("No repeated tactic patterns found at the current thresholds.")
    else:
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

    print(
        f"# Declaration signatures (> {args.signature_lines} source lines): "
        f"{len(signatures)}; showing top {args.top_signatures}"
    )
    for length, path, line, name in signatures[: args.top_signatures]:
        print(f"{length:4}  {path}:{line}  {name}")

    print(
        f"# Theorem/lemma bodies (> {args.proof_lines} source lines): "
        f"{len(proofs)}; showing top {args.top_proofs}"
    )
    for length, path, line, name in proofs[: args.top_proofs]:
        print(f"{length:4}  {path}:{line}  {name}")


if __name__ == "__main__":
    main()
