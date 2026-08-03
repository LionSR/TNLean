#!/usr/bin/env python3
"""Weekly size-and-excess snapshot for the proof-debt ledger.

Measures the quantities the shrink rhythm in ``docs/proof_debt.md`` ratchets
down: total lines, cross-file duplicated windows, numbered-sequel files,
cap-riding files, degenerate-case sites, and sorries. Prints a human summary
and a Markdown table row to append to the Metrics section of
``docs/proof_debt_ledger.md``.

Usage: python3 scripts/loc_report.py [--row-only]
"""

import argparse
import datetime
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "TNLean")
WINDOW = 10
SEQUEL_RE = re.compile(r"[A-Za-z][0-9]+[a-z]?\.lean$")
DEGENERATE_RES = [
    re.compile(r"0 < D\b"),
    re.compile(r"0 < d\b"),
    re.compile(r"\bD ≠ 0\b|\bNeZero\b"),
    re.compile(r"\bFin 0\b|\bIsEmpty\b|\bisEmptyElim\b"),
]


def lean_files():
    for dirpath, _, filenames in os.walk(SRC):
        for name in filenames:
            if name.endswith(".lean"):
                yield os.path.join(dirpath, name)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-only", action="store_true",
                        help="print only the Markdown table row")
    args = parser.parse_args()

    total_lines = 0
    per_dir = Counter()
    sequel_files = sequel_lines = 0
    cap_riding = 0
    degenerate_sites = 0
    sorries = 0
    window_files = defaultdict(set)

    for path in lean_files():
        rel = os.path.relpath(path, ROOT)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        lines = text.split("\n")
        n = len(lines)
        total_lines += n
        per_dir["/".join(rel.split(os.sep)[:2])] += n
        if SEQUEL_RE.search(os.path.basename(path)):
            sequel_files += 1
            sequel_lines += n
        if 900 <= n <= 1000:
            cap_riding += 1
        for regex in DEGENERATE_RES:
            degenerate_sites += len(regex.findall(text))
        sorries += len(re.findall(r"\bsorry\b", text))
        stripped = [ln.strip() for ln in lines if ln.strip()]
        for i in range(len(stripped) - WINDOW + 1):
            window_files[hash(tuple(stripped[i:i + WINDOW]))].add(rel)

    dup_windows = sum(1 for fs in window_files.values() if len(fs) >= 2)
    today = datetime.date.today().isoformat()
    row = (f"| {today} | {total_lines:,} | {dup_windows:,} | "
           f"{sequel_files} ({sequel_lines:,}) | {cap_riding} | "
           f"{degenerate_sites:,} | {sorries} |")

    if args.row_only:
        print(row)
        return

    print(f"TNLean size report — {today}")
    print(f"  total lines:                 {total_lines:,}")
    for d, n in per_dir.most_common(8):
        print(f"    {d}: {n:,}")
    print(f"  duplicated {WINDOW}-line windows (>=2 files): {dup_windows:,}")
    print(f"  numbered-sequel files:       {sequel_files} ({sequel_lines:,} lines)")
    print(f"  cap-riding files (900-1000): {cap_riding}")
    print(f"  degenerate-case sites:       {degenerate_sites:,}")
    print(f"  sorries:                     {sorries}")
    print()
    print("Ledger row (append to Metrics in docs/proof_debt_ledger.md):")
    print(row)


if __name__ == "__main__":
    sys.exit(main())
