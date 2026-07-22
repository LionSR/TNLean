#!/usr/bin/env python3
"""Regression tests for the persistent tenkz demolition guard."""

from __future__ import annotations

import sys
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_demolition as guard


def assert_git_grep_empty(pattern: str, *, fixed: bool = False) -> None:
    command = ["git", "grep", "-n"]
    if fixed:
        command.append("-F")
    command.extend((pattern, "--", "."))
    result = subprocess.run(
        command, cwd=ROOT, text=True, capture_output=True, check=False
    )
    assert result.returncode == 1 and not result.stdout, (
        f"acceptance scan found retired residue: {result.stdout}"
    )


def main() -> int:
    assert guard.RETIRED_PATHS == frozenset(guard.RETIRED_ARTIFACT_PATHS)
    assert len(guard.RETIRED_PATHS) == 18
    artifact_names = {
        Path(path).name for path in guard.RETIRED_ARTIFACT_PATHS
    }
    assert artifact_names <= set(guard.RETIRED_LITERALS)
    loader_literal = "\\use" + "tikzlibrary{tn}"
    package_literal = "\\usepackage{tn_" + "diagrams}"
    assert {loader_literal, package_literal} <= set(guard.RETIRED_LITERALS)

    self_path = "scripts/check_tenkz_demolition.py"
    retired_literal = next(
        literal
        for literal in guard.RETIRED_LITERALS
        if literal.endswith("diagrams.py")
    )
    retired_prefix = guard.RETIRED_PATH_PREFIXES[0]
    assert guard.path_failures(self_path) == []
    assert not guard.should_scan_content(self_path)
    assert guard.content_failures(
        self_path, f"{retired_literal} {retired_prefix}"
    ) == []

    binary_path = "docs/slides/example.pdf"
    binary_fixture = "random bytes " + "\\TN" + "Legacy"
    assert not guard.should_scan_content(binary_path)
    assert guard.content_failures(binary_path, binary_fixture) == []
    assert guard.should_scan_content("docs/example.md")

    retired_path = f"{retired_prefix}anything.tex"
    path_hits = guard.path_failures(retired_path)
    assert path_hits == [f"retired tracked path: {retired_path}"]

    latex_line_break = "\\\\" + "TNLean"
    retired_call = "\\TN" + "Legacy"
    literal_hits = guard.content_failures(
        "docs/example.md",
        f"safe\n{latex_line_break}\n{retired_literal}\n{retired_call}\n",
    )
    assert len(literal_hits) == 2
    assert "retired pipeline reference" in literal_hits[0]
    assert "retired catalogue call" in literal_hits[1]

    tracked_legacy = subprocess.check_output(
        ["git", "ls-files", "tex/" + "tn/**"], cwd=ROOT, text=True
    )
    assert tracked_legacy == ""
    assert_git_grep_empty("\\\\" + "TN[A-Z]")
    assert_git_grep_empty("tex/" + "tn/")
    assert_git_grep_empty("tn_" + "diagrams")
    assert_git_grep_empty("\\use" + "tikzlibrary{" + "tn}", fixed=True)

    print("PASS: demolition guard catches retired paths and content outside itself")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
