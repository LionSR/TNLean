#!/usr/bin/env python3
"""Reject reintroduction of the retired tensor-network catalogue pipeline."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

RETIRED_PATHS = {
    "blueprint/src/Packages/tn_diagrams.py",
    "blueprint/src/tn_diagrams.sty",
    "blueprint/src/plastex_templates/TensorNetworkDiagrams.jinja2s",
    "scripts/build_tn_gallery.py",
    "scripts/check_tn_references.py",
    "docs/tn_diagram_grammar.md",
    "docs/tn_reference/compact_trace_cell.png",
    "docs/tn_reference/dense_fusion_tree.png",
    "docs/tn_reference/parallel_sector_buses.png",
    "docs/tn_reference/rotated_vertical_word.png",
    "docs/tn_reference/straight_purification.png",
    "tex/tn/tikzlibrarytn.code.tex",
    "tex/tn/tn_atoms.tex",
    "tex/tn/tn_catalogue.tex",
    "tex/tn/tn_core.tex",
    "tex/tn/tn_library.tex",
    "tex/tn/tn_motifs_mpdo.tex",
    "tex/tn/tn_slide_catalogue.tex",
}

RETIRED_PATH_PREFIXES = (
    "tex/tn/",
    "docs/tn_reference/",
)

RETIRED_LITERALS = (
    "tex/tn/",
    "docs/tn_reference",
    "tn_diagrams.py",
    "tn_diagrams.sty",
    "build_tn_gallery.py",
    "check_tn_references.py",
    "tikzlibrarytn.code.tex",
    "tn_atoms.tex",
    "tn_catalogue.tex",
    "tn_core.tex",
    "tn_library.tex",
    "tn_motifs_mpdo.tex",
    "tn_slide_catalogue.tex",
    "\\usetikzlibrary{tn}",
    "\\usepackage{tn_diagrams}",
)

# This guard must name the retired paths and literals plainly.  Exclude only
# its own content from residue scanning; its tracked path is still checked.
CONTENT_SCAN_EXCLUDES = {"scripts/check_tenkz_demolition.py"}

RETIRED_CALL = re.compile(r"\\TN[A-Z]")


def path_failures(relative: str) -> list[str]:
    failures = []
    if relative in RETIRED_PATHS or any(
        relative.startswith(prefix) for prefix in RETIRED_PATH_PREFIXES
    ):
        failures.append(f"retired tracked path: {relative}")
    return failures


def content_failures(relative: str, text: str) -> list[str]:
    if relative in CONTENT_SCAN_EXCLUDES:
        return []

    failures = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if RETIRED_CALL.search(line):
            failures.append(
                f"retired catalogue call: {relative}:{line_number}: {line.strip()}"
            )
        for literal in RETIRED_LITERALS:
            if literal in line:
                failures.append(
                    f"retired pipeline reference: {relative}:{line_number}: "
                    f"{line.strip()}"
                )
    return failures


def tracked_files() -> list[Path]:
    output = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT
    ).decode("utf-8")
    return [ROOT / path for path in output.rstrip("\0").split("\0") if path]


def main() -> int:
    failures: list[str] = []
    files = tracked_files()

    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        failures.extend(path_failures(relative))
        text = path.read_text(encoding="utf-8", errors="replace")
        failures.extend(content_failures(relative, text))

    if failures:
        print("FAIL: retired tensor-network catalogue residue found")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(
        "PASS: no retired tensor-network catalogue calls, paths, or pipeline "
        f"entry points in {len(files)} tracked files"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
