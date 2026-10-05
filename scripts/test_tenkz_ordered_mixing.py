#!/usr/bin/env python3
"""Check the actual-block, mixed-overlap, and normalized-preparation networks."""

from __future__ import annotations

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
CHAPTER = ROOT / "blueprint/src/chapter/ch32_log_depth_inhomogeneous_mixing.tex"

# Each tuple is the open boundary, number of tensors, number of emitted wires.
# The final panel must contain only the reference ring: no virtual wire may
# be silently introduced between the three independent physical isometries.
EXPECTED_PANELS = [
    ("open:e, open:w, phys:n, phys:n", 2, 5),
    ("open:e, open:w, phys:n, phys:n", 1, 4),
    ("open:e, open:w, phys:n, phys:n", 2, 5),
    ("", 6, 9),
    ("phys:n, phys:n, phys:n", 10, 13),
    ("phys:n, phys:n, phys:n, phys:n", 6, 10),
    ("phys:n, phys:n, phys:n, phys:n", 2, 4),
    ("open:w", 3, 3),
    ("open:w", 1, 1),
]
EXPECTED_WIRES = {
    "WINDOW": {("wa.0", "wb.180"), ("wb.0", "wrho.180")},
    "VARYING": {
        ("vpzero.0", "vpone.180"),
        ("vpzero.180", "vleft.0"),
        ("vleft.270", "vleftbottom.90"),
        ("vleftbottom.0", "vrightbottom.180"),
        ("vrightbottom.90", "vright.270"),
        ("vright.180", "vpone.0"),
    },
    "BLOCK": {("iso.270", "pos.90")},
    "OVERLAP": {
        ("pzero.270", "fzero.90"),
        ("pone.270", "fone.90"),
        ("ptwo.270", "ftwo.90"),
    },
    "PREPARATION": {
        ("wzero.270", "refzero.90"),
        ("wone.270", "refone.90"),
        ("wtwo.270", "reftwo.90"),
        ("refzero.0", "refone.180"),
        ("refone.0", "reftwo.180"),
        ("refzero.180", "leftturn.0"),
        ("leftturn.270", "leftbottom.90"),
        ("leftbottom.0", "rightbottom.180"),
        ("rightbottom.90", "rightturn.270"),
        ("rightturn.180", "reftwo.0"),
    },
}


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    chapter = CHAPTER.read_text(encoding="utf-8")
    bodies = []
    chapter += (ROOT / "blueprint/src/chapter/ch32_log_depth_varying_reference.tex").read_text(
        encoding="utf-8"
    )
    chapter += (ROOT / "blueprint/src/chapter/ch32_log_depth_window_mixing.tex").read_text(
        encoding="utf-8"
    )
    order = ["BLOCK", "OVERLAP", "PREPARATION", "VARYING", "WINDOW"]
    for name in order:
        expected = EXPECTED_WIRES[name]
        tag = "TENKZ-WINDOW-MIXING-TRANSPORT" if name == "WINDOW" else f"TENKZ-ORDERED-MIXING-{name}"
        begin, end = f"% {tag}-BEGIN", f"% {tag}-END"
        assert chapter.count(begin) == chapter.count(end) == 1
        body = chapter.split(begin, 1)[1].split(end, 1)[0]
        wires = re.findall(
            r"\\tnwire(?:\[[^]]*\])?\s*\{([^}]+)\}\s*\{([^}]+)\}", body
        )
        assert len(wires) == len(expected) and set(wires) == expected, name
        if name in {"BLOCK", "VARYING", "WINDOW"}:
            assert r"\begin{tenkzequation}" in body
            assert r"\begin{tenkzeq}" not in body
        if name == "WINDOW":
            assert r"{F_a}" in body and r"{F_{a+s}}" in body
            assert r"{\sigma_{a+2s}}" in body and r"{\sigma_a}" in body
            assert body.count("180:virtual:$x$") == 2
        if name == "VARYING":
            assert body.count("skin=none") == 4
            assert r"{\sqrt{\sigma_1}}" in body
            assert r"{\sqrt{\sigma_0}}" in body
            assert r"90@1:physical:$r_0$, 90@2:physical:$l_1$" in body
            assert r"90@1:physical:$r_1$, 90@2:physical:$l_0$" in body
        if name == "OVERLAP":
            assert body.count(r"{\overline{P_\infty}}") == 3
            assert "boundary=periodic" in body
        if name == "PREPARATION":
            assert "bonds=none" in body and "boundary=periodic" not in body
            assert body.count("skin=none") == 4
            assert body.count(r"{P_\infty}") == 3
        # The web renderer supports the presentational wrapper. The standalone
        # regression additionally runs the native hard equation-signature check.
        body = body.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
        body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
        body = re.sub(r"(?m)^(\s*)\$=\$(\s*)$", r"\1=\2", body)
        bodies.append(body)
    source = (
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
        "\\usepackage{tenkz}\n\\pagestyle{empty}\n\\begin{document}\n"
        + "\n".join(bodies) + "\n\\end{document}\n"
    )
    with tempfile.TemporaryDirectory(prefix="tenkz_ordered_mixing_") as tmp:
        work = Path(tmp)
        tex = work / "ordered-mixing.tex"
        tex.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
        run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=work, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False,
        )
        if run.returncode:
            print(run.stdout)
            raise SystemExit("FAIL: ordered mixing diagrams did not compile")
        audit = Audit(work / "ordered-mixing.tnlog", tex)
        audit.run()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        assert not hard, hard
        panels, atoms, wires = [], [], []
        for event in audit.events():
            if event.kind == "atom":
                atoms.append(event)
            elif event.kind == "wire":
                wires.append(event)
            elif event.kind == "kernel-boundary":
                panels.append((event.attrs["signature"], len(atoms), len(wires)))
                if len(panels) == 5:
                    assert not any(w.attrs.get("origin") in {"grid", "trace"} for w in wires)
                    assert [w.attrs["port-label"] for w in wires
                            if w.attrs.get("origin") == "port-open"] == ["I_0", "I_1", "I_2"]
                atoms, wires = [], []
        assert panels == EXPECTED_PANELS, panels
    print("PASS: nine panels retain block indices, cyclic pairing, and right-to-left window transport")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
