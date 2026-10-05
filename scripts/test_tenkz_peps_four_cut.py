#!/usr/bin/env python3
"""Render SCP10's four literal cuts and verify all labelled incidences.

Run with the pinned Tenkz checkout and XeLaTeX available. --output-dir keeps
four source-derived PDFs, PNGs and event logs for visual inspection; otherwise
all rendering uses a temporary directory. No repository render cache is used.
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
FRAGMENT = SOURCE / "chapter/ch24_peps_four_cut_diagrams.tex"
CUTS = {"M": (0, 0), "N": (1, 0), "P": (0, 1), "Q": (1, 1)}
VERTICES = {"A": (0, 1), "B": (1, 1), "C": (0, 0), "D": (1, 0)}


def check_incidence(source: str, boundary: str, cut: tuple[int, int]) -> None:
    """Check source wire endpoints and visible labels against native geometry."""
    prefix = f"fourCut{boundary}"
    wires = {
        name: (start, end)
        for name, start, end in re.findall(
            r"\\tnwire\[name=(\w+)\]\{([^}]+)\}\{([^}]+)\}", source
        )
    }
    labels = {
        name: (direction, int(x), int(y), sign or None)
        for name, direction, x, y, sign in re.findall(
            r"\\tnmark\[[^\]]+\]\{on (\w+) [\d.]+\}"
            r"\{\$([HV])_\{([01])([01])\}(?:\^\{([+-])\})?\$\}", source
        )
    }
    assert len(wires) == 12, (boundary, wires)
    assert len(labels) == 12, (boundary, labels)
    assert set(labels) == set(wires), boundary
    sites = {xy: site for site, xy in VERTICES.items()}
    actual_uncut, actual_cut = set(), set()
    used_ports = []
    c, r = cut
    for name, (direction, x, y, sign) in labels.items():
        edge = (direction, x, y)
        tail = (x, y) if direction == "H" else (x, (y + 1) % 2)
        head = ((x + 1) % 2, y) if direction == "H" else (x, y)
        is_cut = (x + 1) % 2 == c if direction == "H" else (y + 1) % 2 == r
        start, end = wires[name]
        used_ports.extend((start, end))
        if sign is None:
            assert not is_cut, (boundary, edge, "cut edge drawn uncut")
            assert {start.split(".")[0], end.split(".")[0]} == {
                prefix + sites[tail], prefix + sites[head]
            }, (boundary, name, tail, head)
            actual_uncut.add(edge)
        else:
            assert is_cut, (boundary, edge, "uncut edge assigned to boundary")
            endpoint = head if sign == "+" else tail
            assert start.split(".")[0] == prefix + sites[endpoint], (boundary, name)
            assert end.split(".")[0] == prefix + "Boundary", (boundary, name)
            actual_cut.add((edge, sign))
    assert len(used_ports) == len(set(used_ports)) == 24, (boundary, "shared endpoint")
    assert len(actual_uncut) == 4 and len(actual_cut) == 8, boundary
    assert len(actual_uncut | {edge for edge, _ in actual_cut}) == 8, boundary
    for edge in {edge for edge, _ in actual_cut}:
        assert {(edge, "+"), (edge, "-")} <= actual_cut, (boundary, edge)


def render(unit, boundary: str, work: Path) -> None:
    from tenkz_audit import Audit

    stem = f"four-cut-{boundary}"
    tex = work / f"{stem}.tex"
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
    tex.write_text(fixture, encoding="utf-8")
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )
    assert run.returncode == 0, (boundary, run.stdout)
    log = work / f"{stem}.tnlog"
    events = log.read_text(encoding="utf-8")
    signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
    assert len(signatures) == 1, (boundary, signatures)
    signature = signatures[0]
    assert len(re.findall(r"\bopen:", signature)) == 0, (boundary, signature)
    assert len(re.findall(r"\bphys:", signature)) == 4, (boundary, signature)
    assert "kernel-error|" not in events, boundary
    atoms = [line for line in events.splitlines() if line.startswith("atom|")]
    assert len(atoms) == 5, (boundary, atoms)
    for site in "ABCD":
        matches = [line for line in atoms if f"|name=fourCut{boundary}{site}|" in line]
        assert len(matches) == 1, (boundary, site)
        assert matches[0].count(":virtual") == 4, (boundary, site)
        assert matches[0].count(":physical") == 1, (boundary, site)
    central = [line for line in atoms if f"|name=fourCut{boundary}Boundary|" in line]
    assert len(central) == 1 and central[0].count(":virtual") == 8, boundary
    assert ":physical" not in central[0], boundary
    wires = [line for line in events.splitlines() if line.startswith("wire|")]
    assert sum("Uncut" in line for line in wires) == 4, boundary
    assert sum("Hend|" in line or "Vend|" in line for line in wires) == 8, boundary
    audit = Audit(log, tex)
    audit.parse_log()
    audit.link_tex()
    for check in ("check_empty_pictures", "check_dialects", "check_kernel_crossings",
                  "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
                  "check_equation_groups", "check_equation_boundaries"):
        getattr(audit, check)()
    assert not audit.findings, (boundary, [(f.severity, f.rule, f.msg) for f in audit.findings])
    assert (work / f"{stem}.pdf").stat().st_size > 1000, boundary
    if shutil.which("pdftoppm"):
        subprocess.run(
            ["pdftoppm", "-png", "-scale-to", "1100", "-singlefile",
             f"{stem}.pdf", stem], cwd=work, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120,
        )
        assert (work / f"{stem}.png").stat().st_size > 1000, boundary


def check_combined(work: Path) -> None:
    """Exercise shared Tenkz state and page breaks with the print preamble."""
    # Use the actual report preamble, including macros/print and unicode-math.
    preamble = (SOURCE / "print.tex").read_text(encoding="utf-8").split(
        r"\providecommand", 1
    )[0]
    fixture = preamble + r"""
\begin{document}
\chapter{Four literal seam cuts}
\section{Boundary contractions}
% Leave less than one diagram of room so the first box must cross a page break.
\noindent\rule{0pt}{0.45\textheight}\par
\input{chapter/ch24_peps_four_cut_diagrams}
\end{document}
"""
    stem = "four-cuts-combined"
    (work / f"{stem}.tex").write_text(fixture, encoding="utf-8")
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", f"{stem}.tex"],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )
    assert run.returncode == 0, ("combined render", run.stdout)
    assert "Overfull" not in run.stdout, ("combined overflow", run.stdout)
    events = (work / f"{stem}.tnlog").read_text(encoding="utf-8")
    signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
    assert len(signatures) == 4, ("combined signatures", signatures)
    for signature in signatures:
        assert len(re.findall(r"\bopen:", signature)) == 0, signature
        assert len(re.findall(r"\bphys:", signature)) == 4, signature
    assert "kernel-error|" not in events, "combined kernel error"
    assert (work / f"{stem}.pdf").stat().st_size > 1000


def run(work: Path) -> None:
    ensure_pythonpath()
    assert shutil.which("xelatex"), "xelatex is required"
    units = [u for u in scan_units(SOURCE / "chapter") if u.path == FRAGMENT]
    assert len(units) == 4, len(units)
    for boundary, cut in CUTS.items():
        matches = [u for u in units if f"name=fourCut{boundary}A," in u.source]
        assert len(matches) == 1, (boundary, len(matches))
        unit = matches[0]
        assert unit.display, (boundary, "diagram must have a display scope")
        check_incidence(unit.source, boundary, cut)
        render(unit, boundary, work)
    check_combined(work)
    print("PASS: 4 source cuts render individually and together; each has 8 labelled bonds, 4 uncut pairings, "
          "one joint 8-leg boundary, and external signature (0,4); no audit findings")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        work = args.output_dir.resolve()
        work.mkdir(parents=True, exist_ok=True)
        run(work)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_peps_four_cut_") as tmp:
            run(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
