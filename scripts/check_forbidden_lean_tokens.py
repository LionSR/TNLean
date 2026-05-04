#!/usr/bin/env python3
"""Reject diffs that add forbidden Lean proof-integrity tokens."""

from __future__ import annotations

import argparse
import re
import subprocess

FORBIDDEN_TOKEN_RE = re.compile(
    r"(^|[^A-Za-z0-9_])"
    r"(sorry|admit|axiom|unsafe|native_decide|unsafeCast|unsafeCoerce|"
    r"lcProof|ofReduceBool|ofReduceNat)"
    r"([^A-Za-z0-9_]|$)"
)


def added_source_lines(diff: str) -> list[str]:
    """Return added source lines from a unified diff."""
    lines: list[str] = []
    for line in diff.splitlines():
        if line.startswith("+++ b/") or line == "+++ /dev/null":
            continue
        if line.startswith("+"):
            lines.append(line[1:])
    return lines


def added_lines(base_ref: str) -> list[str]:
    """Return added source lines from a zero-context git diff."""
    diff = subprocess.run(
        ["git", "diff", base_ref, "--unified=0"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    return added_source_lines(diff)


def check_diff(base_ref: str, message: str) -> int:
    matches = [line for line in added_lines(base_ref) if FORBIDDEN_TOKEN_RE.search(line)]
    if not matches:
        return 0
    for line in matches:
        print(line)
    print(f"::error::{message}")
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", default="HEAD", help="base ref for git diff")
    parser.add_argument(
        "--message",
        default="Diff adds a forbidden proof-integrity token.",
        help="GitHub Actions error message",
    )
    args = parser.parse_args()
    return check_diff(args.base_ref, args.message)


if __name__ == "__main__":
    raise SystemExit(main())
