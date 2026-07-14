#!/usr/bin/env python3
"""Build the labelled tensor-network audit gallery.

The gallery is derived from the public TeX declarations and the renderer's
parameter metadata.  It contains every public atom in both layout profiles,
every registered chapter-facing diagram, and every dark-theme slide diagram.
No second diagram registry is maintained here.
"""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "blueprint/src"
BUILD = ROOT / "tmp/tn-gallery"
OUTPUT = ROOT / "output/pdf/tn_diagram_audit_gallery.pdf"
RENDERER = SRC / "Packages/tn_diagrams.py"


def load_renderer():
    sys.path.insert(0, str(RENDERER.parent))
    spec = importlib.util.spec_from_file_location("tn_diagrams_gallery", RENDERER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {RENDERER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def labelled_page(label: str, body: str) -> str:
    return rf"""
\clearpage
\noindent\texttt{{\detokenize{{{label}}}}}
\vfill
\begin{{center}}
{body}
\end{{center}}
\vfill
"""


def light_source(renderer) -> str:
    atoms = {
        "TNTensor": r"\begin{TNDiagram}[PROFILE]\TNTensor{a}{(0,0)}\end{TNDiagram}",
        "TNComponent": r"\begin{TNDiagram}[PROFILE]\TNComponent{a}{(0,0)}{C}\end{TNDiagram}",
        "TNFactor": r"\begin{TNDiagram}[PROFILE]\TNFactor{a}{(0,0)}{V\otimes W}\end{TNDiagram}",
        "TNMap": r"\begin{TNDiagram}[PROFILE]\TNMap{a}{(0,0)}{U}\end{TNDiagram}",
        "TNState": r"\begin{TNDiagram}[PROFILE]\TNState{a}{(0,0)}{\rho}\end{TNDiagram}",
        "TNExpression": r"\begin{TNDiagram}[PROFILE]\TNExpression{a}{(0,0)}{X\oplus Y}\end{TNDiagram}",
        "TNInsertion": r"\begin{TNDiagram}[PROFILE]\TNInsertion{a}{(0,0)}{X}\end{TNDiagram}",
        "TNJunction": r"\begin{TNDiagram}[PROFILE]\TNJunction{a}{(0,0)}\end{TNDiagram}",
        "TNOperatorState": r"\begin{TNDiagram}[PROFILE]\TNOperatorState{a}{(0,0)}{\rho}\end{TNDiagram}",
        "TNSectorGauge": r"\begin{TNDiagram}[PROFILE]\TNSectorGauge{a}{(0,0)}{X_{j,q}}\end{TNDiagram}",
        "TNInverseSectorGauge": r"\begin{TNDiagram}[PROFILE]\TNInverseSectorGauge{a}{(0,0)}{X_{j,q}^{-1}}\end{TNDiagram}",
        "TNMPSSite": r"\begin{TNDiagram}[PROFILE]\TNMPSSite{a}{(0,0)}{A}\end{TNDiagram}",
        "TNMPOSite": r"\begin{TNDiagram}[PROFILE]\TNMPOSite{a}{(0,0)}{M}\end{TNDiagram}",
        "TNRotatedMPOSite": r"\begin{TNDiagram}[PROFILE]\TNRotatedMPOSite{a}{(0,0)}{M}\end{TNDiagram}",
        "TNPEPSSite": r"\begin{TNDiagram}[PROFILE]\TNPEPSSite{a}{(0,0)}{A}\end{TNDiagram}",
        "TNDoubleLayer": r"\begin{TNDiagram}[PROFILE]\TNDoubleLayer{a}{(0,0.40)}{(0,-0.40)}\end{TNDiagram}",
        "TNPurificationSite": r"\begin{TNDiagram}[PROFILE]\TNPurificationSite{a}{(0,0)}{A}{\overline A}\end{TNDiagram}",
        "TNStackedMPOProduct": r"\begin{TNDiagram}[PROFILE]\TNStackedMPOProduct{a}{(0,0)}{M_\alpha}{M_\beta}{}\end{TNDiagram}",
        "TNCompactTraceCell": r"\begin{TNDiagram}[PROFILE]\TNCompactTraceCell{a}{(0,0)}{M_\alpha}{X}{M_\alpha(X)}\end{TNDiagram}",
    }
    pages = []
    for profile in ("normal", "compact"):
        for name, call in atoms.items():
            pages.append(labelled_page(f"{name} [{profile}]", call.replace("PROFILE", profile)))
        for orientation in ("right", "left", "down", "up"):
            call = (
                r"\begin{TNDiagram}[PROFILE]"
                rf"\TNTrivalentMap{{a}}{{(0,0)}}{{U}}{{{orientation}}}{{v}}{{}}"
                r"\end{TNDiagram}"
            ).replace("PROFILE", profile)
            pages.append(
                labelled_page(f"TNTrivalentMap {orientation} [{profile}]", call)
            )

    for name in renderer._DIAGRAM_ARGS:
        pages.append(labelled_page(name, renderer._sample_tex_call(name)))

    return rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=18in,paperheight=12in,margin=0.55in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm,mathtools,tikz}}
\newcounter{{chapter}}
\pagestyle{{empty}}
\input{{macros/common}}
\input{{macros/tn_print}}
\begin{{document}}
{''.join(pages)}
\end{{document}}
"""


def dark_source() -> str:
    calls = {
        "SlideTNPeriodicMPS": r"\SlideTNPeriodicMPS{A}{N}",
        "SlideTNGaugeConjugation": r"\SlideTNGaugeConjugation{A}{B}{X}",
        "SlideTNBlockingIdentity": r"\SlideTNBlockingIdentity{A}{B}{L}",
        "SlideTNBlockingComparison": r"\SlideTNBlockingComparison{A}{L}",
        "SlideTNMixedTransfer": r"\SlideTNMixedTransfer{A}{B}{\rho}{N}",
        "SlideTNTransferMap": r"\SlideTNTransferMap{A}{\rho}",
    }
    pages = [labelled_page(name, call) for name, call in calls.items()]
    return rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=18in,paperheight=12in,margin=0.55in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm,mathtools,tikz,xcolor}}
\newcounter{{chapter}}
\definecolor{{darkbg}}{{RGB}}{{21,21,21}}
\definecolor{{cardbg}}{{RGB}}{{30,30,30}}
\definecolor{{dimwhite}}{{RGB}}{{180,180,180}}
\definecolor{{leangreen}}{{RGB}}{{34,180,34}}
\definecolor{{leanblue}}{{RGB}}{{70,130,180}}
\definecolor{{amber}}{{RGB}}{{255,191,0}}
\definecolor{{softred}}{{RGB}}{{220,80,80}}
\pagecolor{{darkbg}}\color{{white}}
\pagestyle{{empty}}
\input{{macros/common}}
\input{{../../docs/slides/tn_library_dark}}
\begin{{document}}
{''.join(pages)}
\end{{document}}
"""


def compile_tex(stem: str, source: str) -> Path:
    BUILD.mkdir(parents=True, exist_ok=True)
    tex = BUILD / f"{stem}.tex"
    tex.write_text(source, encoding="utf-8")
    result = subprocess.run(
        [
            "latexmk",
            "-lualatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-outdir={BUILD}",
            str(tex),
        ],
        cwd=SRC,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(f"Gallery build failed for {stem}:\n{result.stdout}")
    return BUILD / f"{stem}.pdf"


def main() -> int:
    renderer = load_renderer()
    light = compile_tex("tn_gallery_light", light_source(renderer))
    dark = compile_tex("tn_gallery_dark", dark_source())
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    pdfunite = shutil.which("pdfunite")
    if pdfunite is None:
        raise RuntimeError("pdfunite is required to assemble the audit gallery")
    subprocess.run([pdfunite, str(light), str(dark), str(OUTPUT)], check=True)
    print(OUTPUT)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
