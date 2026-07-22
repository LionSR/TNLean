#!/usr/bin/env python3
"""Reject reintroduction of the retired tensor-network catalogue pipeline."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

RETIRED_ARTIFACT_COMPONENTS = (
    ("blueprint", "src", "Packages", "tn_" + "diagrams.py"),
    ("blueprint", "src", "tn_" + "diagrams.sty"),
    ("blueprint", "src", "plastex_templates", "TensorNetwork" + "Diagrams.jinja2s"),
    ("scripts", "build_" + "tn_gallery.py"),
    ("scripts", "check_" + "tn_references.py"),
    ("docs", "tn_" + "diagram_grammar.md"),
    ("docs", "tn_reference", "compact_trace_cell.png"),
    ("docs", "tn_reference", "dense_fusion_tree.png"),
    ("docs", "tn_reference", "parallel_sector_buses.png"),
    ("docs", "tn_reference", "rotated_vertical_word.png"),
    ("docs", "tn_reference", "straight_purification.png"),
    ("tex", "tn", "tikzlibrary" + "tn.code.tex"),
    ("tex", "tn", "tn_" + "atoms.tex"),
    ("tex", "tn", "tn_" + "catalogue.tex"),
    ("tex", "tn", "tn_" + "core.tex"),
    ("tex", "tn", "tn_" + "library.tex"),
    ("tex", "tn", "tn_" + "motifs_mpdo.tex"),
    ("tex", "tn", "tn_" + "slide_catalogue.tex"),
)
RETIRED_ARTIFACT_PATHS = tuple(
    "/".join(components) for components in RETIRED_ARTIFACT_COMPONENTS
)

RETIRED_PREFIX_COMPONENTS = (
    ("tex", "tn"),
    ("docs", "tn_reference"),
)
RETIRED_PATH_PREFIXES = tuple(
    "/".join(components) + "/" for components in RETIRED_PREFIX_COMPONENTS
)

RETIRED_PATHS = frozenset(RETIRED_ARTIFACT_PATHS)
RETIRED_LITERALS = tuple(
    dict.fromkeys(
        [prefix.rstrip("/") for prefix in RETIRED_PATH_PREFIXES]
        + [Path(path).name for path in RETIRED_ARTIFACT_PATHS]
        + [
            "\\use" + "tikzlibrary{" + "tn}",
            "\\usepackage{" + "tn_" + "diagrams}",
        ]
    )
)

# This guard must name the retired paths and literals plainly.  Exclude only
# its own content from residue scanning; its tracked path is still checked.
CONTENT_SCAN_EXCLUDES = {"scripts/check_tenkz_demolition.py"}
BINARY_SUFFIXES = frozenset(
    {
        ".7z",
        ".eps",
        ".gif",
        ".gz",
        ".jpeg",
        ".jpg",
        ".pdf",
        ".png",
        ".tar",
        ".webp",
        ".zip",
    }
)

RETIRED_CALL = re.compile(r"(?<!\\)\\TN[A-Z]")


def path_failures(relative: str) -> list[str]:
    failures = []
    if relative in RETIRED_PATHS or any(
        relative.startswith(prefix) for prefix in RETIRED_PATH_PREFIXES
    ):
        failures.append(f"retired tracked path: {relative}")
    return failures


def should_scan_content(relative: str) -> bool:
    return (
        relative not in CONTENT_SCAN_EXCLUDES
        and Path(relative).suffix.lower() not in BINARY_SUFFIXES
    )


def content_failures(relative: str, text: str) -> list[str]:
    if not should_scan_content(relative):
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
        if should_scan_content(relative):
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
