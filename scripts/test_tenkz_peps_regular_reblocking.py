#!/usr/bin/env python3
"""Check SCP10 regular reblocking incidences and render the source displays.

Requires the pinned Tenkz checkout and XeLaTeX. --output-dir retains PDFs,
PNGs and event logs for pixel review. The default uses temporary files and
never changes the repository render cache. No Git history is required.
"""

from __future__ import annotations

import argparse
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
FRAGMENT = SOURCE / "chapter/ch24_peps_regular_reblocking_diagrams.tex"
# Each pair counts separate open virtual and physical indices. The final
# display bundles the complete coarse and surplus physical configurations.
EXPECTED = {
    "reblock3": [(8, 4)],
    "relativeUpper": [(0, 4), (0, 4)],
    "originalCoarseA": [(8, 5)],
    "fixedFine": [(0, 2), (0, 2)],
}
AUDIT_CHECKS = (
    "check_empty_pictures", "check_dialects", "check_kernel_crossings",
    "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
    "check_equation_groups", "check_equation_boundaries",
)


def source_atoms(source: str) -> dict[str, dict[int, tuple[str, str]]]:
    """Read the actual source ports rather than relying on boundary counts."""
    atoms = {}
    for options in re.findall(r"\\tn\[([^\]]+)\]", source, re.S):
        name = re.search(r"\bname=(\w+)", options)
        ports = re.search(r"\bports=\{(.*?)\}\s*(?:,|$)", options, re.S)
        assert name and ports, options
        atom = {}
        for item in ports[1].split(","):
            bits = item.strip().split(":", 2)
            assert len(bits) in (2, 3), (name[1], item)
            angle = int(bits[0]) % 360
            assert angle not in atom, (name[1], angle)
            atom[angle] = (bits[1], bits[2] if len(bits) == 3 else "")
        assert name[1] not in atoms, name[1]
        atoms[name[1]] = atom
    return atoms


def source_wires(source: str) -> dict[str, tuple[str, str]]:
    return {
        name: (start, end)
        for name, start, end in re.findall(
            r"\\tnwire\[name=(\w+)\]\{([^}]+)\}\{([^}]+)\}", source
        )
    }


def check_incidence(anchor: str, source: str) -> None:
    atoms, wires = source_atoms(source), source_wires(source)
    if anchor == "reblock3":
        # These are precisely lambda_i from the actual four-site contraction,
        # in native top/right/bottom/left order, including all four corners.
        legs = {
            0: ("t_1", "r_0", "x_1", "x_0"),
            1: ("x_1", "r_1", "b_1", "x_2"),
            2: ("x_3", "x_2", "b_0", "l_1"),
            3: ("t_0", "x_0", "x_3", "l_0"),
        }
        assert set(atoms) == {f"reblock{i}" for i in range(4)}
        assert wires == {
            "reblockX0": ("reblock3.0", "reblock0.180"),
            "reblockX1": ("reblock0.270", "reblock1.90"),
            "reblockX2": ("reblock2.0", "reblock1.180"),
            "reblockX3": ("reblock3.270", "reblock2.90"),
        }, wires
        for i, values in legs.items():
            ports = atoms[f"reblock{i}"]
            assert len(ports) == 5
            for angle, value in zip((90, 0, 270, 180), values):
                kind, label = ports[angle]
                assert kind == "virtual", (i, angle, kind)
                if value.startswith("x_"):
                    assert label == ""
                    assert f"reblock{i}.{angle}" in wires[f"reblockX{value[-1]}"]
                else:
                    assert label == f"${value}$", (i, angle, label, value)
            physical = [(a, label) for a, (kind, label) in ports.items() if kind == "physical"]
            assert physical == [((45 - 90 * i) % 360, rf"$\sigma_{i}$")], physical
        marks = dict(re.findall(
            r"\\tnmark\[[^\]]+\]\{on (reblockX\d) 0\.5\}\{\$(x_\d)\$\}", source
        ))
        assert marks == {f"reblockX{i}": f"x_{i}" for i in range(4)}, marks
    elif anchor == "relativeUpper":
        assert atoms == {
            "relativeUpper": {180: ("physical", "$a$"), 0: ("physical", "$c$")},
            "relativeLower": {180: ("physical", "$b$"), 0: ("physical", "$d'$")},
            "relativeCoarse": {180: ("physical", "$a$"), 0: ("physical", "$c$")},
            "relativeIdentityLeft": {180: ("physical", "$r$"), 0: ("virtual", "")},
            "relativeIdentityRight": {180: ("virtual", ""), 0: ("physical", "$s$")},
        }, atoms
        assert wires == {"relativeBellBond": ("relativeIdentityLeft.0", "relativeIdentityRight.180")}
        assert source.count("]{L_q}") == 3
        assert source.count("]{1}") == 2
    elif anchor == "originalCoarseA":
        assert len(atoms) == 5 and not wires
        assert atoms["originalCoarseA"] == {
            90: ("virtual", "$u_t$"), 0: ("virtual", "$u_r$"),
            270: ("virtual", "$u_b$"), 180: ("virtual", "$u_l$"),
            135: ("physical", "$s$"),
        }
        for name, side in zip(("Top", "Right", "Bottom", "Left"), "trbl"):
            assert atoms[f"surplus{name}"] == {
                90: ("virtual", f"$r_{side}$"),
                270: ("physical", rf"$\tau_{side}$"),
            }
        assert "]{A}" in source and source.count("]{1}") == 4
    else:
        assert anchor == "fixedFine"
        assert atoms == {
            "fixedFine": {0: ("physical", "")},
            "fixedSupport": {180: ("physical", ""), 45: ("physical", r"$\sigma$"),
                             315: ("physical", r"$\tau$")},
            "fixedCoarse": {0: ("physical", r"$\sigma$")},
            "fixedBell": {0: ("physical", r"$\tau$")},
        }, atoms
        assert wires == {"fixedSupportInput": ("fixedFine.0", "fixedSupport.180")}
        for glyph in (r"]{\widehat\Psi_f}", r"]{\widehat\Psi_c}", r"]{\Omega}", "]{I}"):
            assert glyph in source, glyph


def check_scope(text: str) -> None:
    for phrase in (
        r"scalar factor one", r"every positive coarse period", r"c_B=|G|\prod_i c_i",
        r"E|a,b\rangle=|a,a^{-1}b\rangle", r"L_q\otimes1",
        r"\omega=d^{-1/2}\sum_{r\in G}|r,r\rangle", r"No commutativity",
        r"periods $w,h\geq3$", r"every bond is untwisted",
        r"I\Psi_f=R\Psi_c\otimes\Omega", r"same original tensor $A$",
        r"no surjectivity onto either ambient physical space is assumed",
    ):
        assert phrase in text, ("scope statement missing", phrase)
    # A diagram companion must not duplicate the theorem declarations.
    assert r"\lean{" not in text and r"\leanok" not in text
    for figure in ("renorm-gg-sym", "renorm-g-id-and-split", "renorm-fixedpoint"):
        assert figure in text
        assert (ROOT / f"Papers/1001.3807/figs4/{figure}.pdf").is_file()
    paper = (ROOT / "Papers/1001.3807/paper_v3.tex").read_text(encoding="utf-8")
    assert r"T^\dagger (L_g\otimes" in paper
    assert r"figs4/renorm-fixedpoint" in paper



def check_rejected_mutations(units: dict[str, str], text: str) -> None:
    """Protect the guards against source errors that preserve leg counts."""
    cases = (
        ("reblock3", "{reblock0.180}", "{reblock0.90}"),
        ("reblock3", "$r_0$", "$r_1$"),
        ("reblock3", r"135:physical:$\sigma_3$", r"135:virtual:$\sigma_3$"),
        ("relativeUpper", "{relativeIdentityRight.180}", "{relativeCoarse.180}"),
        ("originalCoarseA", "]{A}", "]{P_0}"),
        ("fixedFine", r"]{\widehat\Psi_c}", r"]{\widehat\Psi_0}"),
    )
    for anchor, old, new in cases:
        source = units[anchor]
        assert old in source, (anchor, "stale mutation", old)
        try:
            check_incidence(anchor, source.replace(old, new, 1))
        except AssertionError:
            continue
        raise AssertionError((anchor, "malformed diagram passed", old, new))
    try:
        check_scope(text.replace(r"|a,a^{-1}b\rangle", r"|a,ba^{-1}\rangle"))
    except AssertionError:
        return
    raise AssertionError("incorrect nonabelian coordinate order passed")

def compile_tex(work: Path, stem: str, fixture: str, expected: list[tuple[int, int]]) -> str:
    from tenkz_audit import Audit

    tex = work / f"{stem}.tex"
    tex.write_text(fixture, encoding="utf-8")
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )
    assert run.returncode == 0, (stem, run.stdout)
    assert "Overfull" not in run.stdout, (stem, "overflow", run.stdout)
    log = work / f"{stem}.tnlog"
    events = log.read_text(encoding="utf-8")
    signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
    actual = [(len(re.findall(r"\bopen:", s)), len(re.findall(r"\bphys:", s))) for s in signatures]
    assert actual == expected, (stem, actual, expected)
    assert "kernel-error|" not in events, (stem, "kernel error")
    audit = Audit(log, tex)
    audit.parse_log()
    audit.link_tex()
    for check in AUDIT_CHECKS:
        getattr(audit, check)()
    assert not audit.findings, (stem, [(f.severity, f.rule, f.msg) for f in audit.findings])
    assert (work / f"{stem}.pdf").stat().st_size > 1000
    if shutil.which("pdftoppm"):
        subprocess.run(
            ["pdftoppm", "-png", "-scale-to", "1400", f"{stem}.pdf", stem],
            cwd=work, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120,
        )
        assert list(work.glob(f"{stem}-*.png"))
    return events


def check_events(anchor: str, events: str) -> None:
    atoms = [line for line in events.splitlines() if line.startswith("atom|")]
    wires = [line for line in events.splitlines() if line.startswith("wire|")]
    if anchor == "reblock3":
        assert len(atoms) == 4
        assert sum("|origin=" not in line for line in wires) == 5
        assert all(line.count(":virtual") == 4 and line.count(":physical") == 1 for line in atoms)
    elif anchor == "relativeUpper":
        assert len(atoms) == 5
        assert sum("relativeBellBond" in line for line in wires) == 1
    elif anchor == "originalCoarseA":
        assert len(atoms) == 5
        assert sum("|origin=" not in line for line in wires) == 1
    else:
        assert len(atoms) == 4
        joined = [line for line in wires if "|name=fixedSupportInput|" in line]
        assert len(joined) == 1 and "|port-type=physical|" in joined[0], joined


def run(work: Path) -> None:
    ensure_pythonpath()
    assert shutil.which("xelatex"), "xelatex is required"
    check_scope(FRAGMENT.read_text(encoding="utf-8"))
    units = [u for u in scan_units(SOURCE / "chapter") if u.path == FRAGMENT]
    assert len(units) == len(EXPECTED), len(units)
    source_by_anchor = {}
    for anchor, expected in EXPECTED.items():
        matches = [u for u in units if f"name={anchor}," in u.source]
        assert len(matches) == 1, (anchor, len(matches))
        unit = matches[0]
        assert unit.display
        check_incidence(anchor, unit.source)
        source_by_anchor[anchor] = unit.source
        fixture = rf"""\documentclass[varwidth,border=2pt]{{standalone}}
\usepackage{{amssymb,amsthm,amsmath,mathtools}}
\newcounter{{chapter}}
\input{{macros/common}}
\usepackage{{tenkz}}
\input{{macros/diagrams}}
\begin{{document}}
{unit.source}
\end{{document}}
"""
        events = compile_tex(work, anchor, fixture, expected)
        check_events(anchor, events)
    check_rejected_mutations(source_by_anchor, FRAGMENT.read_text(encoding="utf-8"))
    # Exercise shared kernel state and pagination with the real print preamble.
    preamble = (SOURCE / "print.tex").read_text(encoding="utf-8").split(r"\providecommand", 1)[0]
    combined = preamble + r"""
\begin{document}
\chapter{Regular PEPS reblocking}
\section{Geometry, relative coordinates and normalized states}
""" + FRAGMENT.read_text(encoding="utf-8") + r"\end{document}"
    compile_tex(work, "regular-reblocking-combined", combined,
                [signature for signatures in EXPECTED.values() for signature in signatures])
    print("PASS: 4 source displays (6 panels) render individually and together; exact corner, "
          "boundary, Bell and physical-support incidences; 7 malformed variants rejected; "
          "all typed signatures match; no audit findings")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        work = args.output_dir.resolve()
        work.mkdir(parents=True, exist_ok=True)
        run(work)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_regular_reblocking_") as tmp:
            run(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
