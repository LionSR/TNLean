#!/usr/bin/env python3
"""Build the labelled tensor-network audit gallery.

The gallery is derived entirely from the public TeX declarations.  It contains
every registered atom, every chapter-facing diagram, and every dark-theme slide
diagram.  No second diagram registry is maintained here.
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


def declared_diagram_page(declaration) -> str:
    contexts = ", ".join(declaration.contexts)
    label = (
        f"{declaration.name} | role={declaration.role} | "
        f"profile={declaration.profile} | context={contexts}"
    )
    return rf"""
\clearpage
\noindent\texttt{{\detokenize{{{label}}}}}

\vspace{{1.5em}}
\noindent Actual publication size
\begin{{center}}
{declaration.sample}
\end{{center}}

\vfill
\noindent Magnified inspection view
\begin{{center}}
\scalebox{{1.75}}{{{declaration.sample}}}
\end{{center}}
\vfill
"""


def light_source(renderer) -> str:
    pages = []
    for atom in renderer.atom_declarations():
        port_schema = ", ".join(
            f"{port.name}:{port.kind}" for port in atom.ports
        ) or "no ports"
        pages.append(
            labelled_page(
                f"{atom.name} | profile={atom.profile} | ports={port_schema}",
                atom.sample,
            )
        )

    for declaration in renderer.diagram_declarations():
        pages.append(declared_diagram_page(declaration))

    return rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=18in,paperheight=12in,margin=0.55in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm,mathtools,tikz,graphicx}}
\newcounter{{chapter}}
\pagestyle{{empty}}
\input{{macros/common}}
\input{{macros/tn_print}}
\begin{{document}}
{''.join(pages)}
\end{{document}}
"""


def dark_source(renderer) -> str:
    pages = [
        labelled_page(name, call)
        for name, call in renderer.slide_diagram_samples()
    ]
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
    dark = compile_tex("tn_gallery_dark", dark_source(renderer))
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    pdfunite = shutil.which("pdfunite")
    if pdfunite is None:
        raise RuntimeError("pdfunite is required to assemble the audit gallery")
    subprocess.run([pdfunite, str(light), str(dark), str(OUTPUT)], check=True)
    print(OUTPUT)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
