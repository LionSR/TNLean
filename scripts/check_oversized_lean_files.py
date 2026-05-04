#!/usr/bin/env python3
"""Report Lean files longer than the repository style limit."""

from __future__ import annotations

import argparse
from pathlib import Path

THRESHOLD = 1000
EXCLUDE_DIRS = (".lake", "lake-packages", "tmp")


def is_excluded(path: Path, root: Path) -> bool:
    """Return whether path should be skipped by the line-count guard."""
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(part in EXCLUDE_DIRS for part in rel_parts)


def count_lines(path: Path) -> int:
    """Count lines in a file without decoding Lean source text."""
    with path.open("rb") as handle:
        return sum(1 for _ in handle)


def check_files(root: Path) -> int:
    """Scan Lean files under root and return 1 when any exceed the limit."""
    oversized: list[tuple[int, str]] = []
    total = 0

    for path in root.rglob("*.lean"):
        if is_excluded(path, root):
            continue
        total += 1
        rel = path.relative_to(root).as_posix()
        lines = count_lines(path)
        if lines > THRESHOLD:
            oversized.append((lines, rel))

    for lines, rel in sorted(oversized, reverse=True):
        print(
            f"::error file={rel},line={THRESHOLD + 1},"
            f"title=Oversized Lean file::{rel}: {lines} lines "
            f"(limit: {THRESHOLD})"
        )

    print(f"Scanned {total} .lean files, {len(oversized)} exceed {THRESHOLD} lines.")
    if oversized:
        print(f"::error::{len(oversized)} oversized file(s) detected.")
        return 1
    print("All .lean files are within the line limit.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root")
    args = parser.parse_args()
    return check_files(args.root.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
