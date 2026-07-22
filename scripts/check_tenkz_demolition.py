#!/usr/bin/env python3
"""Reject reintroduction of the retired tensor-network catalogue pipeline."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

RETIRED_PATH_PREFIXES = (
    "tex/" + "tn/",
    "docs/" + "tn_reference/",
)

RETIRED_LITERALS = (
    "tex/" + "tn/",
    "docs/" + "tn_reference",
    "tn_" + "diagrams.py",
    "tn_" + "diagrams.sty",
    "build_" + "tn_gallery.py",
    "check_" + "tn_references.py",
    "tikzlibrary" + "tn.code.tex",
    "tn_" + "atoms.tex",
    "tn_" + "catalogue.tex",
    "tn_" + "core.tex",
    "tn_" + "library.tex",
    "tn_" + "motifs_mpdo.tex",
    "tn_" + "slide_catalogue.tex",
    "\\usetikzlibrary{" + "tn}",
    "\\usepackage{" + "tn_diagrams}",
)

RETIRED_CALL = re.compile(r"\\TN[A-Z]")


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
        for prefix in RETIRED_PATH_PREFIXES:
            if relative.startswith(prefix):
                failures.append(f"retired tracked path: {relative}")

        text = path.read_text(encoding="utf-8", errors="replace")
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
