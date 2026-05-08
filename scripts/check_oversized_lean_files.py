#!/usr/bin/env python3
"""Guard against oversized Lean files (>1000 lines).

Every Lean file over 1000 lines must be split.
This is a hard gate: any ``.lean`` file exceeding 1000 lines fails the check.

Known oversized files can be listed via ``--known`` arguments; they are
reported as warnings but do **not** cause the check to fail.  Once a known
file is split, remove it from the ``--known`` list.
"""

from __future__ import annotations

import argparse
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

THRESHOLD: int = 1000  # lines — files exceeding this fail the check

# Directories to exclude from scanning (matched against relative-to-root parts)
EXCLUDE_DIRS: tuple[str, ...] = (".lake", "lake-packages", "tmp")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _is_excluded(path: Path, root: Path) -> bool:
    """Return True if *path* lives under an excluded directory or is not a .lean file."""
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(d in rel_parts for d in EXCLUDE_DIRS)


def _count_lines(path: Path) -> int:
    """Count lines in *path* efficiently."""
    with path.open("rb") as fh:
        return sum(1 for _ in fh)


# ---------------------------------------------------------------------------
# Core logic
# ---------------------------------------------------------------------------


def check_files(root: Path, known_oversized: set[str]) -> int:
    """Scan all .lean files under *root*; return 1 if any exceed the threshold, else 0.

    Files listed in *known_oversized* are reported as warnings (not errors)
    and do not cause the check to fail.  Unknown oversized files cause failure.
    """
    oversized: list[tuple[int, str]] = []
    known: list[tuple[int, str]] = []
    total: int = 0

    for path in root.rglob("*.lean"):
        if _is_excluded(path, root):
            continue
        total += 1

        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = str(path)

        lines = _count_lines(path)
        if lines > THRESHOLD:
            if rel in known_oversized:
                known.append((lines, rel))
            else:
                oversized.append((lines, rel))

    # Report known oversized files as warnings
    for lines, rel in sorted(known, reverse=True):
        print(
            f"::warning file={rel},line={THRESHOLD + 1},"
            f"title=Known oversized Lean file::{rel}: {lines} lines "
            f"(limit: {THRESHOLD}) — known, tracked for future splitting"
        )

    # Report unknown oversized files as errors
    for lines, rel in sorted(oversized, reverse=True):
        print(
            f"::error file={rel},line={THRESHOLD + 1},"
            f"title=Oversized Lean file::{rel}: {lines} lines "
            f"(limit: {THRESHOLD})"
        )

    total_oversized = len(known) + len(oversized)
    print(f"Scanned {total} .lean files, {total_oversized} exceed {THRESHOLD} lines"
          f" ({len(known)} known, {len(oversized)} new).")
    if oversized:
        print(f"::error::{len(oversized)} new oversized file(s) detected.")
        return 1
    if total_oversized == 0:
        print("All .lean files are within the line limit.")
    else:
        print(f"{len(known)} known oversized file(s) — no new oversized files.")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Lean files for oversized length violations."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repository root (default: .)",
    )
    parser.add_argument(
        "--known",
        action="append",
        default=[],
        metavar="PATH",
        help="Known oversized file (can be used multiple times). "
             "Reported as a warning, not an error.",
    )
    args = parser.parse_args()
    root_resolved = args.root.resolve()
    known_set: set[str] = set()
    for k in args.known:
        p = Path(k)
        if not p.is_absolute():
            p = root_resolved / p
        try:
            known_set.add(p.resolve().relative_to(root_resolved).as_posix())
        except ValueError:
            # If the path is not under root, keep it as-is
            known_set.add(p.as_posix())
    return check_files(root_resolved, known_set)


if __name__ == "__main__":
    raise SystemExit(main())
