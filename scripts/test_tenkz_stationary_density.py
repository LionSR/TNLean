#!/usr/bin/env python3
"""Audit open physical density legs and the closed quadratic overlap."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_paths import ensure_pythonpath, tenkz_tex

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch12_symmetry_stationary_physical_density.tex"


def check(work: Path) -> None:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    chapter = CHAPTER.read_text(encoding="utf-8")
    bodies = []
    for name in ("DENSITY", "OVERLAP"):
        begin = f"% TENKZ-STATIONARY-{name}-BEGIN"
        end = f"% TENKZ-STATIONARY-{name}-END"
        assert chapter.count(begin) == chapter.count(end) == 1
        body = chapter.split(begin, 1)[1].split(end, 1)[0]
        assert body.count(r"\begin{tenkz}") == 1
        bodies.append(body)
    density, overlap = bodies
    assert "rows={ket,bra}, cols=1, bonds=none" in density
    assert r"west={cup=$\Lambda$}, east=cup" in density
    assert "90:physical:$s$" in density and "270:physical:$t$" in density
    assert "at=on bond" not in density
    assert "rows={wire}, cols=4, boundary=periodic" in overlap
    assert overlap.count(r"\tn[skin=box, label pos=n]{K}") == 2
    assert r"\tn[skin=box, label pos=n]{G_N}" in overlap
    assert r"\tn[skin=box, label pos=n]{G_N^\dagger}" in overlap
    tex = work / "stationary-density.tex"
    tex.write_text(
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
        "\\usepackage{tenkz}\n\\pagestyle{empty}\n\\begin{document}\n"
        + "\n".join(bodies) + "\n\\end{document}\n", encoding="utf-8"
    )
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    (work / "render.log").write_text(run.stdout, encoding="utf-8")
    if run.returncode:
        print(run.stdout)
        raise SystemExit("FAIL: stationary density diagrams did not compile")
    audit = Audit(work / "stationary-density.tnlog", tex)
    audit.run()
    hard = [finding for finding in audit.findings if finding.severity == "HARD"]
    assert not hard, hard
    signatures = [event.attrs["signature"] for event in audit.events()
                  if event.kind == "kernel-boundary"]
    assert len(signatures) == 2, signatures
    assert signatures[1] == "", signatures
    assert signatures[0] == "phys:n, phys:s", signatures
    assert "virtual" not in signatures[0], signatures
    assert "Overfull \\hbox" not in run.stdout
    print("Boundary signatures:", signatures)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, help="Keep the native render for visual review")
    args = parser.parse_args()
    if args.output_dir is None:
        with tempfile.TemporaryDirectory(prefix="tenkz_stationary_density_") as tmp:
            check(Path(tmp))
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check(args.output_dir)
    print("PASS: the density has two open physical legs and its quadratic overlap is scalar")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
