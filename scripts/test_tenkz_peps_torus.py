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
CHAPTER = ROOT / "blueprint/src/chapter/ch24_peps_ft_torus.tex"


def source_picture() -> str:
    """Return the single chapter-owned torus environment verbatim."""
    source = CHAPTER.read_text(encoding="utf-8")
    pictures = re.findall(
        r"\\begin\{tenkzlattice\}\[[\s\S]*?\\end\{tenkzlattice\}",
        source,
    )
    assert len(pictures) == 1, (
        "expected exactly one source-linked torus lattice",
        len(pictures),
    )
    picture = pictures[0]
    for spelling in (
        "west=trace",
        "east=trace",
        "north=trace",
        "south=trace",
        "frame=oblique",
        r"\tnsite[role=marked, label=$A$]{(1,2)}",
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
        traces = [line for line in events if line.startswith("trace|")]
        horizontal = [line for line in traces if "|axis=west-east|" in line]
        vertical = [line for line in traces if "|axis=north-south|" in line]
        boundaries = [line for line in events if line.startswith("boundary|")]

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
        for field in (
            "physical-up=9",
            "physical-down=0",
            "virtual-west=0",
            "virtual-east=0",
            "virtual-north=0",
            "virtual-south=0",
        ):
            assert field in boundary, boundary

    print(
        "PASS: source-linked PEPS torus expands once with live customization, "
        "six two-axis traces, and boundary signature (0,9)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
