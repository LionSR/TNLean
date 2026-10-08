#!/usr/bin/env python3
"""Check and render the native parent-seam and faithful-padding diagrams.

Requires the pinned Tenkz checkout, XeLaTeX and pdftoppm. No Git history or
private refs are used, so shallow checkouts and source exports work. Renders
four displays individually and in the print preamble. --output-dir retains
small PDFs, PNGs and event logs; the default uses a temporary directory.
"""

from __future__ import annotations

import argparse
import itertools
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_blueprint_sweep import scan_units
from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"
FRAGMENT = SOURCE / "chapter/ch24_peps_dependent_parent_seam_diagrams.tex"
VIRTUAL = ("virtual", "")
PHYSICAL = ("physical", "")
CHECKS = (
    "check_empty_pictures", "check_dialects", "check_kernel_crossings",
    "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
    "check_equation_groups", "check_equation_boundaries",
)


def model():
    """The exact typed incidence/glyph/label contract for every drawn panel."""
    result = {}
    result["parentSeamM"] = (
        {
            "parentSeamM": ("M", {30: VIRTUAL, 330: VIRTUAL}),
            "parentSeamK": (r"\mathcal K_{A,C}", {
                150: VIRTUAL, 210: VIRTUAL, 0: ("physical", r"$\sigma$")}),
        },
        {"parentSeamTail": ("parentSeamM.30", "parentSeamK.150"),
         "parentSeamHead": ("parentSeamM.330", "parentSeamK.210")},
        {"parentSeamTail": r"\alpha^-", "parentSeamHead": r"\alpha^+"},
        1,
    )
    result["parentPadM"] = (
        {
            "parentPadM": ("M", {30: VIRTUAL, 330: VIRTUAL}),
            "parentPadA": (r"\mathcal K_{A,C}", {
                150: VIRTUAL, 210: VIRTUAL, 0: PHYSICAL}),
            "parentPadE": ("E", {180: PHYSICAL, 0: ("physical", "$j$")}),
            "parentPadSameM": ("M", {30: VIRTUAL, 330: VIRTUAL}),
            "parentPadB": (r"\mathcal K_{B,C}", {
                150: VIRTUAL, 210: VIRTUAL, 0: ("physical", "$j$")}),
        },
        {"parentPadTail": ("parentPadM.30", "parentPadA.150"),
         "parentPadHead": ("parentPadM.330", "parentPadA.210"),
         "parentPadPhysical": ("parentPadA.0", "parentPadE.180"),
         "parentPadSameTail": ("parentPadSameM.30", "parentPadB.150"),
         "parentPadSameHead": ("parentPadSameM.330", "parentPadB.210")},
        {"parentPadTail": r"\alpha^-", "parentPadHead": r"\alpha^+",
         "parentPadPhysical": "i", "parentPadSameTail": r"\alpha^-",
         "parentPadSameHead": r"\alpha^+"},
        2,
    )
    for prefix, maps, glyph, inner, outer in (
        ("parentLeft", ("E", "R"), r"\psi", ("i'", "j"), "i"),
        ("parentKernel", ("R", "E"), r"\Psi", ("j'", "i"), "j"),
    ):
        first, second = maps
        names = (prefix + "Psi", prefix + first, prefix + second)
        kinds = ("Original", "Ambient") if prefix == "parentLeft" else ("Ambient", "Original")
        wires = {prefix + kind: (names[n] + ".0", names[n + 1] + ".180")
                 for n, kind in enumerate(kinds)}
        result[names[0]] = (
            {names[0]: (glyph, {0: PHYSICAL}),
             names[1]: (first, {180: PHYSICAL, 0: PHYSICAL}),
             names[2]: (second, {180: PHYSICAL, 0: ("physical", f"${outer}$")}),
             prefix + "Recovered": (glyph, {0: ("physical", f"${outer}$")})},
            wires, {prefix + kind: label for kind, label in zip(kinds, inner)}, 2,
        )
    return result


EXPECTED = model()


def source_model(source: str):
    atoms = {}
    for options, glyph in re.findall(r"\\tn\[([^\]]+)\]\{([^\n]*)\}", source, re.S):
        name = re.search(r"\bname=(\w+)", options)
        ports = re.search(r"\bports=\{(.*?)\}\s*$", options, re.S)
        assert name and ports, options
        atom = {}
        for port in ports[1].split(","):
            parts = port.strip().split(":", 2)
            assert len(parts) in (2, 3), port
            angle = int(parts[0]) % 360
            assert angle not in atom, (name[1], angle)
            atom[angle] = (parts[1], parts[2] if len(parts) == 3 else "")
        assert name[1] not in atoms, name[1]
        atoms[name[1]] = (glyph, atom)
    pairs = re.findall(r"\\tnwire\[name=(\w+)\]\{([^}]+)\}\{([^}]+)\}", source)
    wires = {name: (start, end) for name, start, end in pairs}
    assert len(wires) == len(pairs), "duplicate wire name"
    labels = re.findall(r"\\tnmark\[[^\]]+\]\{on (\w+) 0\.5\}\{\$(.*?)\$\}", source)
    marks = dict(labels)
    assert len(marks) == len(labels), "duplicate wire label"
    return atoms, wires, marks


def check_incidence(anchor: str, source: str) -> None:
    atoms, wires, marks = source_model(source)
    expected_atoms, expected_wires, expected_marks, _ = EXPECTED[anchor]
    assert atoms == expected_atoms, (anchor, "typed atoms", atoms)
    assert wires == expected_wires, (anchor, "incidences", wires)
    assert marks == expected_marks, (anchor, "indices", marks)
    used = []
    for start, end in wires.values():
        used.extend((start, end))
        a, p = start.split(".")
        b, q = end.split(".")
        assert atoms[a][1][int(p)][0] == atoms[b][1][int(q)][0]
    assert len(set(used)) == len(used), (anchor, "multiply contracted port")
    # All and only the labelled physical tuple ports must remain uncontracted.
    free = [(kind, label) for name, (_, ports) in atoms.items()
            for angle, (kind, label) in ports.items() if f"{name}.{angle}" not in used]
    assert len(free) == EXPECTED[anchor][3]
    assert all(kind == "physical" and label for kind, label in free)


def check_scope(text: str) -> None:
    flat = " ".join(text.replace("%", "").split())
    for phrase in (
        r"periods $w,h\geq3$", r"$t(e)<h(e)$", r"\prod_{e\in C}X_e",
        r"$\alpha^-_e$ at $t(e)$", r"$\alpha^+_e$ at $h(e)$",
        r"same $z_e$", r"\prod_{v\in V}", r"every microscopic site",
        r"independently $G$-injective", r"matching semi-regular bond",
        r"positive microscopic plaquette-parent kernel", r"every choice of $c,r$",
        r"$R_vE_v=I$", r"$RE\psi=\psi$ for every original",
        r"$\Psi\in\ker H_B$", r"$ER\Psi=\Psi$ without an assumed",
        r"local-image condition", r"unique original representative",
        r"exactly the same boundary coefficients", r"coordinate projection",
        r"not assumed surjective", r"full microscopic commuting-closure classification is not asserted",
    ):
        # A comment may wrap a scope phrase across two lines.
        assert phrase in flat, ("missing scope", phrase)


def check_negative_mutations(units) -> int:
    """Reject changes that a boundary-count-only regression would miss."""
    mutations = (
        ("parentSeamM", "parentSeamK.150", "parentSeamK.210"),
        ("parentSeamM", r"$\alpha^-$", r"$\alpha^+$"),
        ("parentSeamM", "30:virtual,330:virtual", "30:physical,330:virtual"),
        ("parentPadM", "]{M}", "]{N}"),
        ("parentPadM", r"\mathcal K_{B,C}", r"\mathcal K_{A,C}"),
        ("parentLeftPsi", "]{E}", "]{R}"),
        ("parentKernelPsi", "0:physical:$j$", "0:physical:$i$"),
    )
    for anchor, old, new in mutations:
        text = units[anchor].source
        assert old in text, (anchor, old)
        changed = text.replace(old, new, 1)
        try:
            check_incidence(anchor, changed)
        except AssertionError:
            continue
        raise AssertionError(("accepted invalid diagram mutation", anchor, old, new))
    return len(mutations)


def check_grouped_contraction() -> None:
    """Exact integer fixture: grouping both cut incidences equals cutCoeff.

    This checks the formula used to compact the picture, not the Lean parent
    theorem. A triangle has dimensions 2, 3, 3 and independent physical sizes
    2, 1, 3; the first and third edges are cut. M is a joint, non-factorized
    function of all four cut indices. All original sites remain in the product.
    """
    edges = ((0, 1), (1, 2), (0, 2))
    dims, cut = (2, 3, 3), (0, 2)
    incident = {v: [(e, b) for e, ends in enumerate(edges)
                    for b, vertex in enumerate(ends) if vertex == v] for v in range(3)}
    physical = list(itertools.product(range(2), range(1), range(3)))

    def boundary(beta):
        a, b, c, d = (beta[(e, side)] for e in cut for side in (0, 1))
        return 1 + a + 2 * b - 3 * c + d + 5 * a * b * c * d

    def sites(beta, sigma):
        value = 1
        for v in range(3):
            value *= 1 + sigma[v] + sum((k + 1) * beta[p]
                                       for k, p in enumerate(incident[v]))
        return value

    endpoints = [(e, side) for e in range(3) for side in (0, 1)]
    for sigma in physical:
        literal = 0
        for indices in itertools.product(*(range(dims[e]) for e, _ in endpoints)):
            beta = dict(zip(endpoints, indices))
            weight = int(beta[(1, 0)] == beta[(1, 1)])
            literal += boundary(beta) * weight * sites(beta, sigma)
        grouped = 0
        for minus in itertools.product(*(range(dims[e]) for e in cut)):
            for plus in itertools.product(*(range(dims[e]) for e in cut)):
                beta = {(e, side): values[k] for k, e in enumerate(cut)
                        for side, values in ((0, minus), (1, plus))}
                kernel = 0
                for z in range(dims[1]):
                    beta[(1, 0)] = beta[(1, 1)] = z
                    kernel += sites(beta, sigma)
                grouped += boundary(beta) * kernel
        assert literal == grouped, (sigma, literal, grouped)
    # Faithful tagged padding: R E is identity; E R fixes precisely the range.
    tags = ({0: 0, 1: 1}, {0: 2}, {0: 3, 1: 4, 2: 5})
    original = {i: k + 1 for k, i in enumerate(physical)}
    extension = {tuple(tags[v][i[v]] for v in range(3)): value
                 for i, value in original.items()}
    recovered = {i: extension[tuple(tags[v][i[v]] for v in range(3))] for i in physical}
    assert recovered == original
    assert (0, 0, 0) not in extension  # ER is not ambient identity.


def environment():
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    return env


def compile_tex(stem: str, source: str, work: Path, signatures: int) -> None:
    from tenkz_audit import Audit

    tex = work / f"{stem}.tex"
    tex.write_text(source, encoding="utf-8")
    command = ["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name]
    # Two passes resolve the fragment's equation references and its companion labels.
    if stem == "parent-seams-combined":
        subprocess.run(command, cwd=work, env=environment(), check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    run = subprocess.run(
        command,
        cwd=work, env=environment(), text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )
    assert run.returncode == 0, (stem, run.stdout)
    assert "Overfull" not in run.stdout, (stem, "overflow", run.stdout)
    log = work / f"{stem}.tnlog"
    events = log.read_text(encoding="utf-8")
    boundary = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
    assert boundary == ["phys:e"] * signatures, (stem, boundary)
    drawn_atoms, drawn_wires, _ = source_model(source)
    atom_events = [line for line in events.splitlines() if line.startswith("atom|")]
    assert len(atom_events) == len(drawn_atoms), (stem, "atom count")
    for name, (_, ports) in drawn_atoms.items():
        matches = [line for line in atom_events if f"|name={name}|" in line]
        assert len(matches) == 1, (stem, name)
        for kind in ("virtual", "physical"):
            expected_count = sum(port_kind == kind for port_kind, _ in ports.values())
            assert matches[0].count(":" + kind) == expected_count, (stem, name, kind)
    wire_events = [line for line in events.splitlines() if line.startswith("wire|")]
    for name, (start, _) in drawn_wires.items():
        matches = [line for line in wire_events if f"|name={name}|" in line]
        assert len(matches) == 1, (stem, name)
        atom, angle = start.split(".")
        kind = drawn_atoms[atom][1][int(angle)][0]
        assert ("|port-type=physical|" in matches[0]) == (kind == "physical"), (stem, name)
    assert "kernel-error|" not in events, stem
    audit = Audit(log, tex)
    audit.parse_log()
    audit.link_tex()
    for check in CHECKS:
        getattr(audit, check)()
    assert not audit.findings, (stem, [(f.severity, f.rule, f.msg) for f in audit.findings])
    assert (work / f"{stem}.pdf").stat().st_size > 1000
    subprocess.run(
        ["pdftoppm", "-png", "-scale-to", "1300", f"{stem}.pdf", stem],
        cwd=work, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120,
    )
    assert any(work.glob(f"{stem}-*.png")), stem


def run(work: Path) -> None:
    ensure_pythonpath()
    for executable in ("xelatex", "pdftoppm"):
        assert shutil.which(executable), f"{executable} is required"
    check_scope(FRAGMENT.read_text(encoding="utf-8"))
    check_grouped_contraction()
    sources = [u for u in scan_units(SOURCE / "chapter") if u.path == FRAGMENT]
    assert len(sources) == len(EXPECTED), len(sources)
    units = {}
    for anchor in EXPECTED:
        matches = [u for u in sources if f"name={anchor}," in u.source]
        assert len(matches) == 1, (anchor, len(matches))
        unit = units[anchor] = matches[0]
        assert unit.display, anchor
        check_incidence(anchor, unit.source)
        fixture = r"""\documentclass[varwidth,border=3pt]{standalone}
\usepackage{amssymb,amsthm,amsmath,mathtools}
\newcounter{chapter}
\input{macros/common}
\usepackage{tenkz}
\input{macros/diagrams}
\begin{document}
""" + unit.source + "\n\\end{document}\n"
        compile_tex(anchor, fixture, work, EXPECTED[anchor][3])
    rejected = check_negative_mutations(units)
    preamble = (SOURCE / "print.tex").read_text(encoding="utf-8").split(r"\providecommand", 1)[0]
    lead = (SOURCE / "chapter/ch24_peps_native_parent_seam_cuts.tex").read_text(encoding="utf-8")
    fragment = FRAGMENT.read_text(encoding="utf-8")
    combined = preamble + r"""
\begin{document}
\chapter{Microscopic parent constraints}
\section{Native seam boundaries and physical recovery}
""" + lead + "\n\\clearpage\n" + fragment + r"""
\begin{thebibliography}{1}
\bibitem{Schuch2010PEPS}
N. Schuch, J. I. Cirac and D. P\'erez-Garc\'ia.
\emph{PEPS as ground states: Degeneracy and topology}.
Annals of Physics 325 (2010), 2153--2192.
\end{thebibliography}
\end{document}
"""
    compile_tex("parent-seams-combined", combined, work, 7)
    print(f"PASS: 4 displays / 7 panels rendered individually and together; exact typed "
          f"incidences and tuple labels; 7 signatures (0,1); {rejected} negative mutations "
          "rejected; grouped contraction/padding fixture; no audit findings")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        work = args.output_dir.resolve()
        work.mkdir(parents=True, exist_ok=True)
        run(work)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_parent_seams_") as tmp:
            run(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
