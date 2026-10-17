#!/usr/bin/env python3
"""Compile the note's tensor-network diagrams to SVG (and PNG for proofreading).

    python3 docs/notes/one_dimensional_note/build_diagrams.py [DIR] [NAME ...]

Same pipeline as scripts/campaign_board/build_diagrams.py (pinned tenkz +
quantikz, xelatex, pdftocairo): every DIR/diagrams/NAME.tex is one picture
body or a quantikz circuit; DIR/diagrams/inline/NAME.tex is an equation set in
running mathematics. Besides NAME.svg this script writes NAME.png next to it
for visual checks; the PNGs are not committed. With NAME arguments only those
sources are built. Exit status is nonzero if any source fails.
"""
from __future__ import annotations

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[3]
TENKZ = ROOT / ".deps" / "tenkz" / "tex" / "tenkz"
DOCUMENT = r"""\documentclass[varwidth=60cm,border=2pt]{standalone}
\usepackage{amssymb,amsmath}
\usepackage{tenkz}
\usetikzlibrary{quantikz2}
\usetikzlibrary{arrows.meta,calc,patterns,positioning,decorations.pathreplacing}
\begin{document}
%s
\end{document}
"""
INLINE = "$%s$"


def build(source: pathlib.Path, work: pathlib.Path) -> bool:
    tex = work / (source.stem + ".tex")
    body = source.read_text()
    tex.write_text(DOCUMENT % (INLINE % body.strip() if source.parent.name == "inline" else body))
    env = {**os.environ, "TEXINPUTS": f"{TENKZ}//{os.pathsep}{os.environ.get('TEXINPUTS', '')}"}
    run = subprocess.run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                         cwd=work, env=env, capture_output=True, text=True)
    if run.returncode:
        errors = [ln for ln in run.stdout.splitlines() if ln.startswith("!") or "Error" in ln or ln.startswith("l.")]
        print(f"{source}: xelatex failed\n  " + "\n  ".join(errors[:12]), file=sys.stderr)
        return False
    pdf = tex.with_suffix(".pdf")
    subprocess.run(["pdftocairo", "-svg", str(pdf), str(source.with_suffix(".svg"))], check=True)
    subprocess.run(["pdftocairo", "-png", "-r", "160", "-singlefile", str(pdf), str(source.with_suffix(""))], check=True)
    return True


def main() -> None:
    args = sys.argv[1:]
    directory = pathlib.Path(args[0]) if args and pathlib.Path(args[0]).is_dir() else pathlib.Path(__file__).resolve().parent
    names = args[1:] if args and pathlib.Path(args[0]).is_dir() else args
    if not TENKZ.is_dir():
        sys.exit(f"{TENKZ} is missing; run python3 scripts/fetch_tenkz.py")
    for tool in ("xelatex", "pdftocairo"):
        if shutil.which(tool) is None:
            sys.exit(f"{tool} is not on PATH")
    root = directory / "diagrams"
    sources = sorted(root.glob("*.tex")) + sorted((root / "inline").glob("*.tex"))
    if names:
        sources = [s for s in sources if s.stem in names]
    with tempfile.TemporaryDirectory() as tmp:
        failed = [s for s in sources if not build(s, pathlib.Path(tmp))]
    if failed:
        sys.exit(f"{len(failed)} of {len(sources)} diagrams failed: " + ", ".join(s.stem for s in failed))
    print(f"built {len(sources)} diagrams in {root}")


if __name__ == "__main__":
    main()
