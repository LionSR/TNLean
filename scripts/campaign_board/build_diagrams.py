#!/usr/bin/env python3
"""Compile a campaign's tensor-network diagrams to SVG.

    python3 scripts/campaign_board/build_diagrams.py CAMPAIGN_DIR

Each CAMPAIGN_DIR/diagrams/NAME.tex holds one tenkz picture body, or a
quantikz circuit for an argument that is a sequence of operations, set as a
display. Each CAMPAIGN_DIR/diagrams/inline/NAME.tex holds a short equation
set in running mathematics, so tenkz chooses its denser inline size class;
the board places these inside sentences. Every source is compiled in a
standalone document with the pinned tenkz package and quantikz (fetch it
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
DOCUMENT = r"""\documentclass[varwidth=60cm,border=2pt]{standalone}
\usepackage{amssymb,amsmath}
\usepackage{tenkz}
\usetikzlibrary{quantikz2}
\begin{document}
%s
\end{document}
"""
INLINE = "$%s$"


def build(source: pathlib.Path, work: pathlib.Path) -> pathlib.Path | None:
    tex = work / (source.stem + ".tex")
    body = source.read_text()
    tex.write_text(DOCUMENT % (INLINE % body.strip() if source.parent.name == "inline" else body))
    env = {**os.environ, "TEXINPUTS": f"{TENKZ}//{os.pathsep}{os.environ.get('TEXINPUTS', '')}"}
    run = subprocess.run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                         cwd=work, env=env, capture_output=True, text=True)
    if run.returncode:
        errors = [ln for ln in run.stdout.splitlines() if ln.startswith("!") or "Error" in ln]
        print(f"{source}: xelatex failed\n  " + "\n  ".join(errors[:6]), file=sys.stderr)
        return None
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
    root = pathlib.Path(sys.argv[1]) / "diagrams"
    sources = sorted(root.glob("*.tex")) + sorted((root / "inline").glob("*.tex"))
    with tempfile.TemporaryDirectory() as tmp:
        failed = [source for source in sources if build(source, pathlib.Path(tmp)) is None]
    if failed:
        sys.exit(f"{len(failed)} of {len(sources)} diagrams failed")
    print(f"built {len(sources)} diagrams")


if __name__ == "__main__":
    main()
