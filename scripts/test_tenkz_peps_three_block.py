#!/usr/bin/env python3
"""Render and audit the literal SCP10 three-core, eight-boundary-leg diagram.

Uses an already available pinned Tenkz checkout and XeLaTeX. The output keeps
its event log and a PNG for direct inspection when --output-dir is supplied.
No repository build cache is created or changed.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from tenkz_blueprint_sweep import scan_units
from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"
FRAGMENT = SOURCE / "chapter/ch24_peps_general_three_block_intersection.tex"


def run(work: Path) -> None:
    ensure_pythonpath()
    from tenkz_audit import Audit

    units = [unit for unit in scan_units(SOURCE / "chapter") if unit.path == FRAGMENT]
    assert len(units) == 1 and units[0].display, "Expected one complete displayed contraction"
    unit = units[0]
    assert "name=generalThreeX" in unit.source
    preamble = (SOURCE / "print.tex").read_text().split(r"\providecommand", 1)[0]
    fixture = preamble + "\n\\begin{document}\n\\chapter{Three-block open contraction}\n" + unit.source
    fixture += "\n\\end{document}\n"
    tex = work / "three-block.tex"
    tex.write_text(fixture)
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    render = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120,
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
    assert len(re.findall(r"\bphys:", signatures[0])) == 3, signatures
    atoms = [line for line in events.splitlines() if line.startswith("atom|")]
    assert len(atoms) == 4, atoms
    for site in "ABC":
        selected = [line for line in atoms if f"|name=generalThree{site}|" in line]
        assert len(selected) == 1, (site, selected)
        assert selected[0].count(":virtual") == 4, selected
        assert selected[0].count(":physical") == 1, selected
    boundary = [line for line in atoms if "|name=generalThreeX|" in line]
    assert len(boundary) == 1 and boundary[0].count(":virtual") == 8, boundary
    assert ":physical" not in boundary[0], boundary
    wires = [line for line in events.splitlines() if line.startswith("wire|")]
    assert sum("name=generalThreeInternal" in line for line in wires) == 2, wires
    assert sum("name=generalThreeX" in line for line in wires) == 8, wires
    # Each explicitly named virtual port belongs to exactly one internal or boundary wire.
    pairs = re.findall(r"\\tnwire(?:\[[^\]]*\])?\{([^}]+)\}\{([^}]+)\}", unit.source)
    endpoints = [port for pair in pairs for port in pair
                 if re.fullmatch(r"generalThree[ABCX]\.\d+", port)]
    assert len(endpoints) == len(set(endpoints)) == 23, endpoints
    audit = Audit(log, tex)
    audit.parse_log()
    audit.link_tex()
    for check in ("check_empty_pictures", "check_dialects", "check_kernel_crossings",
                  "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
                  "check_equation_groups", "check_equation_boundaries"):
        getattr(audit, check)()
    assert not audit.findings, [(f.severity, f.rule, f.msg) for f in audit.findings]
    if shutil.which("pdftoppm"):
        subprocess.run(
            ["pdftoppm", "-png", "-scale-to", "1200", "-singlefile", tex.with_suffix(".pdf").name,
             "three-block"], cwd=work, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
    print("PASS: three four-legged tensors, two internal bonds, one joint eight-leg boundary, "
          "external signature (0,3), and no diagram audit findings")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        work = args.output_dir.resolve()
        work.mkdir(parents=True, exist_ok=True)
        run(work)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz-three-block-") as temporary:
            run(Path(temporary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
