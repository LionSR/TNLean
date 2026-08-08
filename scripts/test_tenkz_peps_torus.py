#!/usr/bin/env python3
"""Regression for the source-linked two-axis PEPS torus picture."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "blueprint/src"
CHAPTER = SOURCE_ROOT / "chapter/ch24_peps_ft_torus.tex"


def read_tex_tree(path: Path) -> str:
    """Read a TeX source after recursively expanding its input wrappers."""
    source = path.read_text(encoding="utf-8")

    def expand(match: re.Match[str]) -> str:
        target = match.group(1)
        if not target.endswith(".tex"):
            target += ".tex"
        return read_tex_tree(SOURCE_ROOT / target)

    return re.sub(r"\\input\{([^}]+)\}", expand, source)


def source_picture() -> str:
    """Return the single chapter-owned torus environment verbatim."""
    source = read_tex_tree(CHAPTER)
    pictures = re.findall(
        r"\\begin\{tenkz\}\[[\s\S]*?\\end\{tenkz\}",
        source,
    )
    assert len(pictures) == 1, (
        "expected exactly one source-linked torus picture",
        len(pictures),
    )
    picture = pictures[0]
    for spelling in (
        "west=trace",
        "east=trace",
        "north=trace",
        "south=trace",
        "frame=plane",
        "physical=up",
        r"\tn[at=(1,2), species=marked, label pos=nw]{A}",
    ):
        assert spelling in picture, spelling
    return picture


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1
    pdftotext = shutil.which("pdftotext")
    if pdftotext is None:
        print("FAIL: pdftotext is required")
        return 1

    picture = source_picture()
    fixture = rf"""
\documentclass[tikz,border=2pt]{{standalone}}
\usepackage{{tenkz}}
\begin{{document}}
\tenkzkernel
{picture}
\end{{document}}
"""
    with tempfile.TemporaryDirectory(prefix="tenkz_peps_torus_") as tmp:
        work = Path(tmp)
        tex = work / "peps-torus.tex"
        tex.write_text(fixture, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get(
            "TEXINPUTS", ""
        )
        run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if run.returncode:
            print(run.stdout)
            print("FAIL: source-linked PEPS torus picture did not compile")
            return 1

        audit = subprocess.run(
            [
                "python3",
                str(ROOT / "scripts/tenkz_audit.py"),
                "peps-torus.tnlog",
            ],
            cwd=work,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if audit.returncode:
            print(audit.stdout)
            print("FAIL: source-linked PEPS torus picture did not pass audit")
            return 1

        events = (work / "peps-torus.tnlog").read_text(encoding="utf-8").splitlines()
        pictures = [line for line in events if line.startswith("picture|")]
        traces = [
            line
            for line in events
            if line.startswith("wire|") and "|origin=trace|" in line
        ]
        horizontal = [line for line in traces if "|side=west-east" in line]
        vertical = [line for line in traces if "|side=north-south" in line]
        boundaries = [
            line for line in events if line.startswith("kernel-boundary|")
        ]

        extracted = subprocess.run(
            [pdftotext, "-layout", "peps-torus.pdf", "-"],
            cwd=work,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=True,
        ).stdout.split()

        assert len(pictures) == 1, pictures
        assert extracted.count("A") == 1, extracted
        assert len(horizontal) == 3, horizontal
        assert len(vertical) == 3, vertical
        assert len(traces) == 6, traces
        assert len(boundaries) == 1, boundaries
        boundary = boundaries[0]
        signature = boundary.split("signature=", 1)[1]
        entries = [entry.strip() for entry in signature.split(",")]
        assert entries == ["phys:n"] * 9, boundary

    print(
        "PASS: source-linked PEPS torus expands once with live customization, "
        "six two-axis traces, and boundary signature (0,9)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
