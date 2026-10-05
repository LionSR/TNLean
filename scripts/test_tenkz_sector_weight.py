#!/usr/bin/env python3
"""Check the closed branch contraction for the GHZ sector-weight obstruction."""

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
CHAPTER = ROOT / "blueprint/src/chapter/ch32_log_depth_sector_weights.tex"
EXPECTED = {
    ("brai.270", "obsx.90"), ("braj.270", "obsy.90"), ("brar.270", "obsr.90"),
    ("obsx.270", "keti.90"), ("obsy.270", "ketj.90"), ("obsr.270", "ketr.90"),
}


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    chapter = CHAPTER.read_text(encoding="utf-8")
    start, end = "% TENKZ-SECTOR-WEIGHT-BEGIN", "% TENKZ-SECTOR-WEIGHT-END"
    assert chapter.count(start) == chapter.count(end) == 1
    body = chapter.split(start, 1)[1].split(end, 1)[0]
    wires = re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body)
    assert len(wires) == len(EXPECTED) and set(wires) == EXPECTED
    source = (
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb,tenkz}\n"
        "\\pagestyle{empty}\n\\begin{document}\n" + body + "\n\\end{document}\n"
    )
    with tempfile.TemporaryDirectory(prefix="tenkz_sector_weight_") as tmp:
        work = Path(tmp)
        tex = work / "sector-weight.tex"
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
            raise SystemExit("FAIL: sector-weight diagram did not compile")
        audit = Audit(work / "sector-weight.tnlog", tex)
        audit.run()
        assert not [f for f in audit.findings if f.severity == "HARD"]
        events = list(audit.events())
        atoms = [e for e in events if e.kind == "atom"]
        wires = [e for e in events if e.kind == "wire"]
        boundaries = [e.attrs["signature"] for e in events if e.kind == "kernel-boundary"]
        assert len(atoms) == 9, atoms
        assert len(wires) == 6, wires
        assert boundaries == [""], boundaries
        output = os.environ.get("TENKZ_TEST_OUTPUT")
        if output:
            Path(output).mkdir(parents=True, exist_ok=True)
            for suffix in ["tex", "pdf", "tnlog", "log"]:
                shutil.copy(work / f"sector-weight.{suffix}", Path(output))
    print("PASS: three independent branch contractions, nine tensors, six physical wires, no open legs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
