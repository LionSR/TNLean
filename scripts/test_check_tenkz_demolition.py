#!/usr/bin/env python3
"""Regression tests for the persistent tenkz demolition guard."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_demolition as guard


def main() -> int:
    self_path = "scripts/check_tenkz_demolition.py"
    retired_literal = guard.RETIRED_LITERALS[2]
    retired_prefix = guard.RETIRED_PATH_PREFIXES[0]
    assert guard.path_failures(self_path) == []
    assert guard.content_failures(
        self_path, f"{retired_literal} {retired_prefix}"
    ) == []

    retired_path = f"{retired_prefix}anything.tex"
    path_hits = guard.path_failures(retired_path)
    assert path_hits == [f"retired tracked path: {retired_path}"]

    literal_hits = guard.content_failures(
        "docs/example.md", f"safe\n{retired_literal}\n" + "\\TN" + "Legacy\n"
    )
    assert len(literal_hits) == 2
    assert "retired pipeline reference" in literal_hits[0]
    assert "retired catalogue call" in literal_hits[1]

    print("PASS: demolition guard catches retired paths and content outside itself")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
