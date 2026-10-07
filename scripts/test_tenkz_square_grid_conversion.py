#!/usr/bin/env python3
"""Render and audit the four-bond, four-physical-leg open-square contraction."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

from tenkz_blueprint_sweep import scan_units
from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"
FRAGMENT = SOURCE / "chapter/ch24_peps_square_grid_conversion.tex"


def run(work: Path) -> None:
    ensure_pythonpath()
    from tenkz_audit import Audit

    units = [unit for unit in scan_units(SOURCE / "chapter") if unit.path == FRAGMENT]
    assert len(units) == 1 and units[0].display
    unit = units[0]
    expected = {
        "squareGridH1": ("squareGridTL.0", "squareGridTR.180"),
        "squareGridH0": ("squareGridBL.0", "squareGridBR.180"),
        "squareGridV0": ("squareGridTL.270", "squareGridBL.90"),
        "squareGridV1": ("squareGridTR.270", "squareGridBR.90"),
        "squareGridPhysical01": ("squareGridTL.135", "open nw"),
        "squareGridPhysical11": ("squareGridTR.45", "open ne"),
        "squareGridPhysical00": ("squareGridBL.225", "open sw"),
        "squareGridPhysical10": ("squareGridBR.315", "open se"),
    }
    wires = {
        name: (left, right)
        for name, left, right in re.findall(
            r"\\tnwire\[name=(\w+)(?:,[^\]]*)?\]\{([^}]+)\}\{([^}]+)\}", unit.source
        )
    }
    assert wires == expected, wires
    endpoints = [port for pair in wires.values() for port in pair if not port.startswith("open")]
    assert len(endpoints) == len(set(endpoints)) == 12
    preamble = (SOURCE / "print.tex").read_text().split(r"\providecommand", 1)[0]
    tex = work / "square-grid.tex"
    tex.write_text(preamble + "\n\\begin{document}\n" + unit.source + "\n\\end{document}\n")
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    render = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=120,
    )
    (work / "render.txt").write_text(render.stdout)
    assert render.returncode == 0, render.stdout
    assert "Overfull" not in render.stdout, render.stdout
    log = tex.with_suffix(".tnlog")
    events = log.read_text()
    assert "kernel-error|" not in events, events
    signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
    assert len(signatures) == 1, signatures
    assert len(re.findall(r"\bopen:", signatures[0])) == 0, signatures
    assert len(re.findall(r"\bphys:", signatures[0])) == 4, signatures
    atoms = [line for line in events.splitlines() if line.startswith("atom|")]
    assert len(atoms) == 4, atoms
    for atom in atoms:
        assert atom.count(":virtual") == 2 and atom.count(":physical") == 1, atom
    audit = Audit(log, tex)
    audit.parse_log()
    audit.link_tex()
    for check in ("check_empty_pictures", "check_dialects", "check_kernel_crossings",
                  "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
                  "check_equation_groups", "check_equation_boundaries"):
        getattr(audit, check)()
    assert not audit.findings, [(finding.severity, finding.rule, finding.msg)
                                for finding in audit.findings]
    subprocess.run(["pdftoppm", "-png", "-scale-to", "1500", "-singlefile",
                    str(tex.with_suffix(".pdf")), str(work / "square-grid")], check=True)
    print("Square-grid diagram passed: four exact bonds, four physical legs, no virtual boundary.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        run(args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="square-grid-") as temporary:
            run(Path(temporary))
