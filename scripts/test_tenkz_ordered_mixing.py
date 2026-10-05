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
]
EXPECTED_WIRES = {
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
    for name, expected in EXPECTED_WIRES.items():
        tag = f"TENKZ-ORDERED-MIXING-{name}"
        begin, end = f"% {tag}-BEGIN", f"% {tag}-END"
        assert chapter.count(begin) == chapter.count(end) == 1
        body = chapter.split(begin, 1)[1].split(end, 1)[0]
        wires = re.findall(
            r"\\tnwire(?:\[[^]]*\])?\s*\{([^}]+)\}\s*\{([^}]+)\}", body
        )
        assert len(wires) == len(expected) and set(wires) == expected, name
        if name == "OVERLAP":
            assert body.count(r"{\overline{P_\infty}}") == 3
            assert "boundary=periodic" in body
        if name == "PREPARATION":
            assert "bonds=none" in body and "boundary=periodic" not in body
            assert body.count("skin=none") == 4
            assert body.count(r"{P_\infty}") == 3
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
    print("PASS: five panels retain block indices, conjugated overlap, and one reference ring")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
