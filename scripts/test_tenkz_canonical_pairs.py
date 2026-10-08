#!/usr/bin/env python3
"""Render and audit the four source-linked canonical fixed-point equations."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch32_log_depth_canonical_pairs.tex"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default="xelatex")
    args = parser.parse_args()
    engine = shutil.which(args.engine)
    if engine is None:
        raise SystemExit(f"Missing TeX engine: {args.engine}")
    source = CHAPTER.read_text(encoding="utf-8")
    equations = re.findall(r"\\begin\{tenkzequation\}[\s\S]*?\\end\{tenkzequation\}", source)
    assert len(equations) == 4, "Expected embedding, assembly, GHZ, and polar restriction"
    # The web renderer supports tenkzequation. Native scoped equations are used
    # only in this extracted regression to check equality of the typed boundaries.
    assert r"\begin{tenkzeq}" not in source
    equations = [
        re.sub(r"\$=([^$]*)\$", lambda m: "=" + (f"${m[1]}$" if m[1].strip() else ""),
               equation.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
               .replace(r"\end{tenkzequation}", r"\end{tenkzeq}"))
        for equation in equations
    ]
    signatures = [
        "open:n, open:n",
        "open:e, open:w, phys:n",
        ", ".join(["open:n"] * 6),
        "open:s, open:s, phys:n",
    ]
    assert r"\sqrt{\sigma_j}" in equations[0]
    assert r"\chi_3(\alpha')" in equations[2]
    assert r"\frac{\mu_{j,k_j}^q}{c_j}" in equations[3]
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    audit = ensure_pythonpath() / "tenkz_audit.py"
    with tempfile.TemporaryDirectory(prefix="tenkz_canonical_pairs_") as tmp:
        work = Path(tmp)
        for index, (equation, signature) in enumerate(zip(equations, signatures), 1):
            name = f"canonical-pairs-{index}"
            tex = work / f"{name}.tex"
            tex.write_text(
                r"\documentclass[border=6pt]{standalone}" "\n"
                r"\usepackage{amsmath,amssymb,tenkz}" "\n"
                r"\begin{document}\tenkzkernel" "\n"
                + equation + "\n" + r"\end{document}" "\n",
                encoding="utf-8",
            )
            run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
                cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=120,
            )
            assert run.returncode == 0, run.stdout
            log = work / f"{name}.tnlog"
            result = subprocess.run(
                ["python3", str(audit), str(log), str(tex)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=30,
            )
            assert result.returncode == 0, result.stdout
            events = log.read_text(encoding="utf-8").splitlines()
            boundaries = [line for line in events if line.startswith("kernel-boundary|")]
            assert boundaries == [f"kernel-boundary|signature={signature}"] * 2, boundaries
            checks = [line for line in events if line.startswith("check|")]
            assert len(checks) == 1 and "|result=equal|" in checks[0], checks
            assert (work / f"{name}.pdf").stat().st_size > 0
    print("PASS: four canonical-pair equations, eight panels, four equal typed boundaries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
