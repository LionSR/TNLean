#!/usr/bin/env python3
"""Check the two-site physical-isometry contraction and its boundary signature."""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_paths import ensure_pythonpath, tenkz_tex

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_isometric_gap_transport.tex"
TAG = "TENKZ-ISOMETRIC-GAP"
EXPECTED_WIRES = {
    ("Ezero.270", "h.90@1"),
    ("Eone.270", "h.90@2"),
    ("h.270@1", "Fzero.90"),
    ("h.270@2", "Fone.90"),
}
EXPECTED_PANELS = [
    ("phys:n, phys:n, phys:s, phys:s", 1, 4),
    ("phys:n, phys:n, phys:s, phys:s", 5, 8),
]


def check(work: Path) -> None:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    chapter = CHAPTER.read_text(encoding="utf-8")
    begin, end = f"% {TAG}-BEGIN", f"% {TAG}-END"
    assert chapter.count(begin) == chapter.count(end) == 1
    body = chapter.split(begin, 1)[1].split(end, 1)[0]
    wires = re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body)
    assert len(wires) == 4 and set(wires) == EXPECTED_WIRES, wires
    assert body.count("bonds=none") == 2
    assert body.count(r"]{E}") == body.count(r"]{E^\dagger}") == 2
    assert "Contracted indices a_0,a_1,b_0,b_1 each range over Fin d." in body
    assert "each range over Fin m." in body
    assert "north outputs" in body and "south inputs" in body
    # Slot order pins site 0 and site 1 on both sides of the operator.
    assert r"90@1:physical:$\alpha_0$, 90@2:physical:$\alpha_1$" in body
    assert r"270@1:physical:$\beta_0$, 270@2:physical:$\beta_1$" in body
    assert r"E_{\alpha_0a_0}E_{\alpha_1a_1}" in chapter
    assert r"h_{a_0a_1,b_0b_1}" in chapter
    assert r"\overline{E_{\beta_0b_0}E_{\beta_1b_1}}" in chapter
    body = body.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
    body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
    body = body.replace("    $=$", "    =")
    tex = work / "isometric-gap-transport.tex"
    tex.write_text(
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
        "\\usepackage{tenkz}\n\\pagestyle{empty}\n\\begin{document}\n"
        + body + "\n\\end{document}\n",
        encoding="utf-8",
    )
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    (work / "compile.log").write_text(run.stdout, encoding="utf-8")
    if run.returncode:
        raise SystemExit(f"FAIL: diagram did not compile; see {work / 'compile.log'}")
    audit = Audit(work / "isometric-gap-transport.tnlog", tex)
    audit.run()
    hard = [finding for finding in audit.findings if finding.severity == "HARD"]
    assert not hard, hard
    panels, atoms, wires = [], [], []
    for event in audit.events():
        if event.kind == "atom":
            atoms.append(event)
        elif event.kind == "wire":
            wires.append(event)
        elif event.kind == "kernel-boundary":
            panels.append((event.attrs["signature"], len(atoms), len(wires)))
            assert not any(w.attrs.get("origin") in {"grid", "trace"} for w in wires)
            labels = [w.attrs["port-label"] for w in wires
                      if w.attrs.get("origin") == "port-open"]
            assert sorted(labels) == sorted([
                r"\alpha _0", r"\alpha _1", r"\beta _0", r"\beta _1",
            ]), labels
            atoms, wires = [], []
    assert panels == EXPECTED_PANELS, panels
    checks = [event.attrs for event in audit.log_events if event.kind == "check"]
    assert checks and all(c.get("result") == "equal" for c in checks), checks
    print("PASS: two operator panels; four m-dimensional open legs; "
          "four d-dimensional contractions; adjoint inputs; matching native signatures")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, help="retain rendered regression artifacts")
    args = parser.parse_args()
    if args.output_dir is not None:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check(args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_isometric_gap_") as tmp:
            check(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
