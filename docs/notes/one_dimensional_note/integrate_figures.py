#!/usr/bin/env python3
"""Insert the compiled diagrams into the note's LaTeX parts as figures.

    python3 docs/notes/one_dimensional_note/integrate_figures.py

Each entry below names a diagram, the part file, the anchor line before which
the figure goes, and the caption key (the diagram's `src` in presentation.json,
whose caption is reused so the PDF and the digest page say the same thing).
Only diagrams whose SVG exists are inserted; a diagram already present in a
part is skipped, so the script is idempotent. Writes the assembled
one_dimensional_area_law_and_mps.tex.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
PRES = json.loads((HERE / "presentation.json").read_text())
CAPTIONS = {}
for t in PRES["theorems"]:
    if t.get("diagram"):
        CAPTIONS.setdefault(t["diagram"], "")
for route in PRES["routes"]:
    for st in route["stages"]:
        for d in st.get("diagrams", []):
            CAPTIONS[d["src"]] = d.get("caption", "")

# (name, inline?, part file, anchor text the figure is inserted before, caption override)
PLAN = [
    ("chain-cuts", False, "part1_arealaw.tex", r"\begin{lemma}[Reductions]", None),
    ("tilt", False, "part1_arealaw.tex", r"\begin{remark}[Rényi entropies near one]", None),
    ("tail-sketch", False, "part1_arealaw.tex", r"\begin{remark}[Rényi entropies near one]", None),
    ("chain-shells", False, "part1_arealaw.tex", r"\begin{lemma}[Single splitting]", None),
    ("filter-product", False, "part1_arealaw.tex", r"\paragraph{Stationarity.}", None),
    ("qc-single-split", False, "part1_arealaw.tex", r"\paragraph{Upper bound on the optimum.}", None),
    ("pinning", False, "part1_arealaw.tex", r"\paragraph{Conclusion.}", None),
    ("closing", False, "part1_arealaw.tex", r"\begin{remark}[What the constant depends on]", None),
    ("recursion", False, "part1_arealaw.tex", "@@END@@", None),
    ("chain-amplify", False, "part1_arealaw.tex", "@@END@@", None),
    ("chain-families", False, "part1_arealaw.tex", "@@END@@", None),
    ("mps-chain", False, "part2a_mps_information.tex", r"\begin{proposition}[Sequential truncation]", None),
    ("truncation-sequence", False, "part2a_mps_information.tex", r"\begin{theorem}[Theorem~\ref{thm:B}, two-line route]", None),
    ("split", True, "part2a_mps_information.tex", r"\subsection{The information reset}",
     r"The splitting lemma as a diagram: the isometry $V$ on the buffer $U$ turns $\Om$ into nearly a product of a purification $s$ of $\rho_T$ and a purification $s'$ of $\rho_E$."),
    ("chain-reset", False, "part2a_mps_information.tex", r"\begin{lemma}[Information reset]", None),
    ("replica-swap", False, "part2a_mps_information.tex", r"\subsection{The one-dimensional separation lemma}", None),
    ("qc-gaussian-filter", False, "part2a_mps_information.tex", r"\subsection{The one-dimensional separation lemma}", None),
    ("chain-logsep", False, "part2a_mps_information.tex", r"\begin{remark}[A route without Lieb--Robinson bounds]", None),
    ("qc-birth", False, "part2b_mps_protocol.tex", r"\begin{lemma}[Two-sheet exchange]", None),
    ("qc-death", False, "part2b_mps_protocol.tex", r"\begin{lemma}[Two-sheet exchange]", None),
    ("qc-exchange", False, "part2b_mps_protocol.tex", "\\begin{remark}\nIn the two-dimensional source these lemmas carry encoded holes", None),
    ("sweep-step", False, "part2b_mps_protocol.tex", r"\begin{construction}[The sweep]", None),
    ("band-words", False, "part2b_mps_protocol.tex", r"\begin{lemma}[The band dissolution is a bounded change]", None),
    ("party-graph", False, "part2b_mps_protocol.tex", r"\begin{remark}[Why no patches]", None),
    ("source-sampling", True, "part2b_mps_protocol.tex", r"\begin{lemma}[Column extraction",
     r"The random replacement of one pair source: the operator $\ket\eta\bra{\tilde\eta}$ equals the expectation of $\frac1k\sum_j U_j\otimes V_j$, the two factors joined by the sample index $j$."),
    ("column", True, "part2b_mps_protocol.tex", r"\section{Assembly on the chain}",
     r"Column extraction: fixing the input legs of the operator chain by a product-basis covector gives a ket chain with the same bonds."),
    ("block-to-sites", False, "part2b_mps_protocol.tex", r"\begin{remark}[Order of constants]", None),
]


WIDE = {"chain-cuts", "chain-shells", "filter-product", "pinning", "qc-single-split", "closing",
        "chain-families", "chain-amplify", "truncation-sequence", "chain-reset", "replica-swap",
        "qc-gaussian-filter", "chain-logsep", "qc-birth", "qc-death", "qc-exchange", "sweep-step",
        "band-words", "party-graph", "block-to-sites", "mps-chain"}


def body_for_figure(src: pathlib.Path, inline: bool) -> str:
    """The picture as inline-math-safe material for an adjustbox (display math becomes
    inline displaystyle math; an inline equation is wrapped in math delimiters)."""
    text = src.read_text()
    lines = [ln for ln in text.splitlines() if not ln.lstrip().startswith("%")]
    text = "\n".join(lines).strip()
    if inline:
        return "\\(" + text + "\\)"
    if text.startswith("\\[") and text.endswith("\\]"):
        return "\\(\\displaystyle " + text[2:-2].strip() + "\\)"
    return text


def figure(name: str, inline: bool, caption: str) -> str:
    src = HERE / ("diagrams/inline" if inline else "diagrams") / f"{name}.tex"
    rel = f"diagrams/fig/{name}.tex"
    (HERE / "diagrams" / "fig").mkdir(exist_ok=True)
    (HERE / rel).write_text(body_for_figure(src, inline) + "\n")
    env = "figure*" if name in WIDE else "figure"
    return (f"\\begin{{{env}}}[t]\n\\centering\n"
            f"\\begin{{adjustbox}}{{max width=\\linewidth}}\n\\input{{{rel}}}\n\\end{{adjustbox}}\n"
            f"\\caption{{{caption}}}\\label{{fig:{name}}}\n\\end{{{env}}}\n\n")


def main() -> None:
    inserted, missing = [], []
    for name, inline, part, anchor, override in PLAN:
        src = HERE / ("diagrams/inline" if inline else "diagrams") / f"{name}.tex"
        if not src.with_suffix(".svg").exists():
            missing.append(name)
            continue
        text = (HERE / part).read_text()
        if f"\\label{{fig:{name}}}" in text:
            # already placed: refresh the figure copy from the (possibly revised) source
            (HERE / "diagrams" / "fig").mkdir(exist_ok=True)
            (HERE / f"diagrams/fig/{name}.tex").write_text(body_for_figure(src, inline) + "\n")
            continue
        key = f"diagrams/{name}.svg"
        caption = override or CAPTIONS.get(key, "")
        caption = caption.replace("\\(", "$").replace("\\)", "$")
        fig = figure(name, inline, caption)
        if anchor == "@@END@@":
            text = text.rstrip("\n") + "\n\n" + fig
        else:
            if anchor not in text:
                sys.exit(f"{part}: anchor not found for {name}: {anchor[:40]}")
            text = text.replace(anchor, fig + anchor, 1)
        (HERE / part).write_text(text)
        inserted.append(name)
    parts = ["part0_preamble.tex", "part1_arealaw.tex", "part2a_mps_information.tex", "part2b_mps_protocol.tex", "bib.tex"]
    (HERE / "one_dimensional_area_law_and_mps.tex").write_text("".join((HERE / p).read_text() for p in parts))
    print("inserted:", ", ".join(inserted) or "none")
    print("missing svg:", ", ".join(missing) or "none")


if __name__ == "__main__":
    main()
