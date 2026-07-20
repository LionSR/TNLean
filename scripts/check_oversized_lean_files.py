#!/usr/bin/env python3
"""Guard against oversized Lean files (>1000 lines).

Every Lean file over 1000 lines must be split.  Exact import-aggregator paths
may be exempted explicitly, but each exemption is validated: after Lean
comments are removed, the file must contain only ``import`` commands.

Known oversized files can be listed via ``--known`` arguments; they are
reported as warnings but do **not** cause the check to fail.  Once a known
file is split, remove it from the ``--known`` list.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

THRESHOLD: int = 1000
EXCLUDE_DIRS: tuple[str, ...] = (".lake", "lake-packages", "tmp")
IMPORT_COMMAND = re.compile(r"import\s+[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z0-9_']+)*")

SPLIT_GUIDANCE = (
    "Split by mathematical responsibility into concept-named modules; move shared "
    "definitions and setup into a family Basic.lean module; and keep only imports "
    "in a concept-named aggregator. Do not create numbered continuations such as "
    "Foo2.lean or Foo3.lean."
)


def _is_excluded(path: Path, root: Path) -> bool:
    """Return whether *path* is excluded or is not a Lean source file."""
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(directory in rel_parts for directory in EXCLUDE_DIRS)


def _count_lines(path: Path) -> int:
    with path.open("rb") as handle:
        return sum(1 for _ in handle)


def _strip_lean_comments(source: str) -> tuple[str, str | None]:
    """Remove nested block and line comments, or return a parse error."""
    output: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        pair = source[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    output.append("\n")
                index += 1
        elif pair == "/-":
            block_depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            if newline == -1:
                index = len(source)
            else:
                output.append("\n")
                index = newline + 1
        else:
            output.append(source[index])
            index += 1
    if block_depth:
        return "".join(output), "unterminated block comment"
    return "".join(output), None


def validate_import_aggregator(path: Path) -> str | None:
    """Return ``None`` exactly when *path* is a nonempty import-only Lean file."""
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return f"cannot read file: {error}"
    uncommented, error = _strip_lean_comments(source)
    if error is not None:
        return error
    commands = [line.strip() for line in uncommented.splitlines() if line.strip()]
    if not commands:
        return "file contains no import commands"
    for line_number, command in enumerate(commands, start=1):
        if IMPORT_COMMAND.fullmatch(command) is None:
            return (
                "contains non-import Lean code after comments are removed "
                f"(command {line_number}: {command!r})"
            )
    return None


def _normalize_paths(root: Path, paths: list[str]) -> tuple[set[str], list[str]]:
    normalized: set[str] = set()
    outside: list[str] = []
    for raw_path in paths:
        path = Path(raw_path)
        if not path.is_absolute():
            path = root / path
        try:
            relative = path.resolve().relative_to(root).as_posix()
        except ValueError:
            outside.append(raw_path)
        else:
            normalized.add(relative)
    return normalized, outside


def check_files(
    root: Path,
    known_oversized: set[str],
    generated_aggregators: set[str] | None = None,
) -> int:
    """Scan Lean files under *root* and return 1 for any policy violation."""
    generated_aggregators = generated_aggregators or set()
    oversized: list[tuple[int, str]] = []
    known: list[tuple[int, str]] = []
    errors = 0
    total = 0
    valid_aggregators: set[str] = set()

    for relative in sorted(generated_aggregators):
        path = root / relative
        if path.suffix != ".lean" or not path.is_file() or _is_excluded(path, root):
            print(
                f"::error file={relative},title=Invalid generated aggregator exemption::"
                f"{relative}: exemption must name an existing, scanned .lean file"
            )
            errors += 1
            continue
        reason = validate_import_aggregator(path)
        if reason is not None:
            print(
                f"::error file={relative},title=Invalid generated aggregator exemption::"
                f"{relative}: {reason}"
            )
            errors += 1
        else:
            valid_aggregators.add(relative)

    for path in root.rglob("*.lean"):
        if _is_excluded(path, root):
            continue
        total += 1
        relative = path.relative_to(root).as_posix()
        lines = _count_lines(path)
        if lines <= THRESHOLD or relative in valid_aggregators:
            continue
        if relative in known_oversized:
            known.append((lines, relative))
        else:
            oversized.append((lines, relative))

    for lines, relative in sorted(known, reverse=True):
        print(
            f"::warning file={relative},line={THRESHOLD + 1},"
            f"title=Known oversized Lean file::{relative}: {lines} lines "
            f"(limit: {THRESHOLD}) — known, tracked for future splitting"
        )

    for lines, relative in sorted(oversized, reverse=True):
        print(
            f"::error file={relative},line={THRESHOLD + 1},"
            f"title=Oversized Lean file::{relative}: {lines} lines "
            f"(limit: {THRESHOLD}). {SPLIT_GUIDANCE}"
        )

    total_oversized = len(known) + len(oversized)
    print(
        f"Scanned {total} .lean files, {total_oversized} nonexempt files exceed "
        f"{THRESHOLD} lines ({len(known)} known, {len(oversized)} new); "
        f"validated {len(valid_aggregators)} of {len(generated_aggregators)} "
        "exact aggregator exemption(s)."
    )
    if oversized:
        print(f"::error::{len(oversized)} new oversized file(s) detected.")
        print(f"Split guidance: {SPLIT_GUIDANCE}")
    if errors or oversized:
        return 1
    if total_oversized == 0:
        print("All nonexempt .lean files are within the line limit.")
    else:
        print(f"{len(known)} known oversized file(s) — no new oversized files.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Lean files for oversized length violations."
    )
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root")
    parser.add_argument(
        "--known",
        action="append",
        default=[],
        metavar="PATH",
        help="Known oversized file (repeatable; warning rather than error).",
    )
    parser.add_argument(
        "--generated-aggregator",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "Exact generated import-aggregator path to exempt (repeatable). "
            "The file is rejected unless its uncommented content is import-only."
        ),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    known, known_outside = _normalize_paths(root, args.known)
    aggregators, aggregator_outside = _normalize_paths(root, args.generated_aggregator)
    for path in known_outside + aggregator_outside:
        print(f"::error title=Path outside repository::{path}")
    if known_outside or aggregator_outside:
        return 1
    return check_files(root, known, aggregators)


if __name__ == "__main__":
    raise SystemExit(main())
