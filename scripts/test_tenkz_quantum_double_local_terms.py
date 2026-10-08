#!/usr/bin/env python3
"""Check the local quantum-double diagrams and nonabelian formula fixtures.

With the pinned Tenkz package and XeLaTeX, render the three pictures separately
and in the blueprint print preamble. The event-stream checks retain all open
virtual legs and all physical tuples. --no-render checks source and algebra
without TeX. These regressions do not replace the general Lean proofs.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import os
from pathlib import Path
import re
import subprocess
import tempfile

from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"
FRAGMENT = SOURCE / "chapter/ch24_peps_quantum_double_local_terms.tex"
MODULES = ("QuantumDoubleLocalConstraint", "QuantumDoubleBondAverage",
           "QuantumDoubleBondParent", "QuantumDoublePlaquetteConstraint")
VIRTUAL = ("virtual", "")


def expected_atoms():
    virtual = lambda label: ("virtual", f"${label}$")
    physical = lambda label: ("physical", f"${label}$")
    return {
        "qdK": ("K", {90: virtual("p"), 0: virtual("q"), 270: virtual("r"),
                       180: virtual("s"), 45: physical("a"), 315: physical("b"),
                       225: physical("c"), 135: physical("d")}),
        "qdLeft": ("K_L", {90: virtual("p"), 0: VIRTUAL, 270: virtual("r"),
                             180: virtual("s"), 135: physical(r"\sigma_L")}),
        "qdRight": ("K_R", {90: virtual("t"), 0: virtual("v"), 270: virtual("w"),
                              180: VIRTUAL, 45: physical(r"\sigma_R")}),
        "qdNW": ("K", {90: virtual("p"), 0: VIRTUAL, 270: VIRTUAL,
                        180: virtual("s"), 135: physical(r"\sigma_{NW}")}),
        "qdNE": ("K", {90: virtual("t"), 0: virtual("v"), 270: VIRTUAL,
                        180: VIRTUAL, 45: physical(r"\sigma_{NE}")}),
        "qdSE": ("K", {90: VIRTUAL, 0: virtual("k"), 270: virtual("l"),
                        180: VIRTUAL, 315: physical(r"\sigma_{SE}")}),
        "qdSW": ("K", {90: VIRTUAL, 0: VIRTUAL, 270: virtual("m"),
                        180: virtual("n"), 225: physical(r"\sigma_{SW}")}),
    }


EXPECTED_WIRES = {
    "qdShared": ("qdLeft.0", "qdRight.180"),
    "qdNorth": ("qdNW.0", "qdNE.180"),
    "qdWest": ("qdNW.270", "qdSW.90"),
    "qdSouth": ("qdSW.0", "qdSE.180"),
    "qdEast": ("qdNE.270", "qdSE.90"),
}
EXPECTED_LABELS = dict(zip(EXPECTED_WIRES, ("x", "x", "y", "z", "w")))
SIGNATURES = [
    "open:e, open:n, open:s, open:w, phys:135, phys:225, phys:315, phys:45",
    "open:e, open:n, open:n, open:s, open:s, open:w, phys:135, phys:45",
    "open:e, open:e, open:n, open:n, open:s, open:s, open:w, open:w, "
    "phys:135, phys:225, phys:315, phys:45",
]


def check_source(source):
    compact = re.sub(r"\s+", "", source)
    assert r"F(p,q,r,s)&=(pq^{-1},qr^{-1},rs^{-1},sp^{-1})" in compact
    assert r"\ket{F(p,x,r,s)}\otimes\ket{F(t,v,w,x)}" in compact
    assert r"\ket{F(p,x,y,s)}\otimes\ket{F(t,v,w,x)}" in compact
    assert r"\ket{F(w,k,l,z)}\otimes\ket{F(y,z,m,n)}" in compact
    atoms = {}
    for options, glyph in re.findall(r"\\tn\[([^\]]+)\]\{([^\n]*)\}", source, re.S):
        name = re.search(r"\bname=(\w+)", options)[1]
        raw_ports = re.search(r"\bports=\{(.*?)\}\s*$", options, re.S)[1]
        typed = {}
        for raw in raw_ports.split(","):
            pieces = raw.strip().split(":", 2)
            angle = int(pieces[0])
            assert angle not in typed
            typed[angle] = (pieces[1], pieces[2] if len(pieces) == 3 else "")
        assert name not in atoms
        atoms[name] = (glyph, typed)
    assert atoms == expected_atoms(), "tensor labels, typed ports or open indices changed"
    raw_wires = re.findall(r"\\tnwire\[name=(\w+)\]\{([^}]+)\}\{([^}]+)\}", source)
    wires = {name: (first, second) for name, first, second in raw_wires}
    assert len(wires) == len(raw_wires)
    assert wires == EXPECTED_WIRES, "contracted incidences changed"
    labels = dict(re.findall(
        r"\\tnmark\[[^\]]+\]\{on (\w+) 0\.5\}\{\$(.*?)\$\}", source))
    assert labels == EXPECTED_LABELS, "shared-color labels changed"
    assert r"\sigma_{NW,b}\sigma_{SW,a}" in source
    assert r"\sigma_{SE,d}\sigma_{NE,c}" in source
    assert r"\frac1{|G|}\sum_{u\in G}V_u" in source
    assert r"\ket{au^{-1},ub,c,d}\otimes\ket{e,f,gu^{-1},uh}" in source


def check_declaration_names(source):
    """Check tag spelling against source; this is not Lean elaboration."""
    declarations = set()
    for stem in MODULES:
        path = ROOT / "TNLean/PEPS/Examples" / f"{stem}.lean"
        declarations.update(re.findall(
            r"^(?:noncomputable )?(?:def|theorem|lemma|abbrev) (\w+)",
            path.read_text(), re.M))
    names = [name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", source)
             for name in group.split(",")]
    assert len(names) == len(set(names)), "duplicate declaration ownership"
    assert all(name.startswith("TNLean.PEPS.") and name.split(".")[-1] in declarations
               for name in names), "a declaration tag has no matching source declaration"
    assert {name.split(".")[-1] for name in names} == declarations, \
        "a changed production declaration has no mathematical blueprint owner"
    return len(names)


def check_mutations(source):
    mutations = [
        source.replace("{qdRight.180}", "{qdRight.0}"),
        source.replace("{qdSW.90}", "{qdSW.0}"),
        source.replace("90:virtual:$p$", "90:physical:$p$", 1),
        source.replace("{on qdEast 0.5}{$w$}", "{on qdEast 0.5}{$x$}"),
        source.replace(r"\sigma_{SE,d}\sigma_{NE,c}", r"\sigma_{NE,c}\sigma_{SE,d}"),
        source.replace(r"\frac1{|G|}\sum_{u\in G}V_u", r"\sum_{u\in G}V_u"),
        source.replace(r"\ket{au^{-1},ub,c,d}", r"\ket{u^{-1}a,ub,c,d}"),
    ]
    for changed in mutations:
        assert changed != source
        try:
            check_source(changed)
        except AssertionError:
            continue
        raise AssertionError("incorrect diagram or nonabelian formula was accepted")
    return len(mutations)


def check_nonabelian_fixture():
    """Use S3, so multiplication order and left/right actions cannot collapse."""
    group = tuple(itertools.permutations(range(3)))
    one = (0, 1, 2)
    mul = lambda p, q: tuple(p[q[i]] for i in range(3))
    inv = lambda p: tuple(p.index(i) for i in range(3))
    assert any(mul(p, q) != mul(q, p) for p in group for q in group)

    def spins(p, q, r, s):
        return (mul(p, inv(q)), mul(q, inv(r)), mul(r, inv(s)), mul(s, inv(p)))

    def holonomy(x):
        return mul(mul(mul(x[0], x[1]), x[2]), x[3])

    def action(u, pair):
        (a, b, c, d), (e, f, g, h) = pair
        return ((mul(a, inv(u)), mul(u, b), c, d),
                (e, f, mul(g, inv(u)), mul(u, h)))

    images = {spins(*colors) for colors in itertools.product(group, repeat=4)}
    flat = {x for x in itertools.product(group, repeat=4) if holonomy(x) == one}
    assert images == flat
    for a, b, c, d in flat:
        assert spins(one, inv(a), inv(mul(a, b)), inv(mul(mul(a, b), c))) == (a, b, c, d)
        # Explicit six-boundary-color reconstruction at the common color one.
        assert spins(a, one, inv(b), inv(mul(b, c))) == (a, b, c, d)
        assert spins(mul(mul(a, b), c), mul(b, c), c, one) == (a, b, c, d)
    # Every group element is used as both an exterior and an interior color.
    for shift in range(6):
        for step in range(6):
            p, r, s, t, v, w = (group[(shift + i * step) % 6] for i in range(6))
            contraction = Counter((spins(p, x, r, s), spins(t, v, w, x)) for x in group)
            for u in group:
                assert Counter({action(u, pair): n for pair, n in contraction.items()}) == contraction
                for x in group:
                    pair = (spins(p, x, r, s), spins(t, v, w, x))
                    assert action(u, pair) == (spins(p, mul(u, x), r, s), spins(t, v, w, mul(u, x)))
                    for v0 in group:
                        assert action(u, action(v0, pair)) == action(mul(u, v0), pair)
    for x, y, z, w in itertools.product(group, repeat=4):
        # Noncommuting exterior values are retained in all sixteen spins.
        nw, ne = spins(group[1], x, y, group[2]), spins(group[3], group[4], w, x)
        se, sw = spins(w, group[5], group[1], z), spins(y, z, group[2], group[3])
        assert holonomy((nw[1], sw[0], se[3], ne[2])) == one
        # Independent selected spins also test the non-flat ambient space.
        value = holonomy((x, y, z, w))
        for u in group:
            assert holonomy((mul(u, x), y, z, mul(w, inv(u)))) == mul(mul(u, value), inv(u))


def render(work, source):
    ensure_pythonpath()
    from tenkz_audit import Audit

    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    preamble = (SOURCE / "print.tex").read_text().split(r"\providecommand", 1)[0]
    pictures = re.findall(r"\\begin\{tenkzequation\}(.*?)\\end\{tenkzequation\}", source, re.S)
    assert len(pictures) == 3
    cases = [(f"qd-picture-{i}", body, [SIGNATURES[i]]) for i, body in enumerate(pictures)]
    cases.append(("qd-combined", r"\chapter{Explicit quantum-double local terms}" + source, SIGNATURES))
    for stem, body, signatures in cases:
        tex = work / f"{stem}.tex"
        tex.write_text(preamble + "\n\\begin{document}\n" + body + r"""
\begin{thebibliography}{1}
\bibitem{Schuch2010PEPS} N. Schuch, J. I. Cirac and D. P\'erez-Garc\'ia.
PEPS as ground states: degeneracy and topology. arXiv:1001.3807v3.
\end{thebibliography}
\end{document}
""")
        for _ in range(2):
            run = subprocess.run(["xelatex", "-halt-on-error", "-interaction=nonstopmode", tex.name],
                                 cwd=work, env=env, capture_output=True, text=True, timeout=120)
            assert run.returncode == 0, run.stdout[-5000:]
        assert "Overfull" not in run.stdout
        assert "undefined" not in run.stdout
        log = work / f"{stem}.tnlog"
        events = log.read_text()
        assert re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M) == signatures
        audit = Audit(log, tex)
        audit.parse_log()
        audit.link_tex()
        for check in ("check_empty_pictures", "check_dialects", "check_kernel_crossings",
                      "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
                      "check_equation_groups", "check_equation_boundaries"):
            getattr(audit, check)()
        assert not audit.findings, [(f.severity, f.rule, f.msg) for f in audit.findings]
        subprocess.run(["pdftoppm", "-png", "-scale-to", "1200", f"{stem}.pdf", stem],
                       cwd=work, check=True, capture_output=True, timeout=120)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--no-render", action="store_true")
    args = parser.parse_args()
    source = FRAGMENT.read_text()
    check_source(source)
    declarations = check_declaration_names(source)
    rejected = check_mutations(source)
    check_nonabelian_fixture()
    if not args.no_render:
        if args.output_dir:
            args.output_dir.mkdir(parents=True, exist_ok=True)
            render(args.output_dir.resolve(), source)
        else:
            with tempfile.TemporaryDirectory(prefix="qd-local-terms-") as tmp:
                render(Path(tmp), source)
    print(f"PASS: exact typed incidences; {declarations} declaration names exist in source; "
          f"{rejected} negative mutations rejected; S3 local/bond image, shared-bond "
          "contraction invariance, group action, hole flatness and ambient conjugation fixtures" +
          ("; source/algebra only" if args.no_render else "; 3 individual and 1 combined render, no audit findings"))


if __name__ == "__main__":
    main()
