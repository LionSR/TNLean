#!/usr/bin/env python3
"""Compile a campaign's tensor-network diagrams to SVG.

    python3 scripts/campaign_board/build_diagrams.py CAMPAIGN_DIR

Each CAMPAIGN_DIR/diagrams/NAME.tex holds one tenkz picture body. It is
compiled in a standalone document with the pinned tenkz package (fetch it
with `python3 scripts/fetch_tenkz.py`) along the blueprint's route, xelatex
to PDF and pdftocairo to SVG, and written to CAMPAIGN_DIR/diagrams/NAME.svg.
The SVGs are committed, so the hourly board job needs no TeX installation;
rerun this script after editing a source.
"""
from __future__ import annotations

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
TENKZ = ROOT / ".deps" / "tenkz" / "tex" / "tenkz"
DOCUMENT = r"""\documentclass[varwidth,border=2pt]{standalone}
\usepackage{amssymb,amsmath}
\usepackage{tenkz}
\begin{document}
%s
\end{document}
"""


def build(source: pathlib.Path, work: pathlib.Path) -> pathlib.Path:
    tex = work / (source.stem + ".tex")
    tex.write_text(DOCUMENT % source.read_text())
    env = {**os.environ, "TEXINPUTS": f"{TENKZ}//{os.pathsep}{os.environ.get('TEXINPUTS', '')}"}
    run = subprocess.run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                         cwd=work, env=env, capture_output=True, text=True)
    if run.returncode:
        errors = [ln for ln in run.stdout.splitlines() if ln.startswith("!") or "Error" in ln]
        sys.exit(f"{source}: xelatex failed\n" + "\n".join(errors[:8]))
    svg = source.with_suffix(".svg")
    subprocess.run(["pdftocairo", "-svg", str(tex.with_suffix(".pdf")), str(svg)], check=True)
    return svg


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    if not TENKZ.is_dir():
        sys.exit(f"{TENKZ} is missing; run python3 scripts/fetch_tenkz.py")
    for tool in ("xelatex", "pdftocairo"):
        if shutil.which(tool) is None:
            sys.exit(f"{tool} is not on PATH")
    sources = sorted((pathlib.Path(sys.argv[1]) / "diagrams").glob("*.tex"))
    with tempfile.TemporaryDirectory() as tmp:
        for source in sources:
            print(build(source, pathlib.Path(tmp)))


if __name__ == "__main__":
    main()
