#!/usr/bin/env python3
"""Focused contract tests for the executable tenkz language registry."""

from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

import tenkz_language


ROOT = Path(__file__).resolve().parents[1]


def run(*args: str, cwd: Path = ROOT, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args, cwd=cwd, check=check, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )


def compile_source(source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="tenkz-language-") as tmp:
        path = Path(tmp)
        (path / "case.tex").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:"
        return subprocess.run(
            ("xelatex", "-interaction=nonstopmode", "-halt-on-error", "case.tex"),
            cwd=path, env=env, check=False, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120,
        )


def compile_event_source(source: str) -> tuple[subprocess.CompletedProcess[str], str]:
    with tempfile.TemporaryDirectory(prefix="tenkz-language-events-") as tmp:
        path = Path(tmp)
        (path / "case.tex").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:"
        result = subprocess.run(
            ("xelatex", "-interaction=nonstopmode", "-halt-on-error", "case.tex"),
            cwd=path, env=env, check=False, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120,
        )
        log = (path / "case.tnlog").read_text(encoding="utf-8") if result.returncode == 0 else ""
        return result, log


def main() -> int:
    run("python3", "scripts/tenkz_language.py", "check")
    mpo_preludes = [
        entry.fields
        for entry in tenkz_language.load_registry()
        if entry.kind == "prelude" and entry.fields[:2] == ("skin", "mpo")
    ]
    if mpo_preludes != [("skin", "mpo", "base=box")]:
        raise SystemExit("the executable registry lost the stock MPO box declaration")
    reference = tenkz_language.REFERENCE.read_text(encoding="utf-8")
    if "Prelude class & Name & Declaration" not in reference or "base=box" not in reference:
        raise SystemExit("the generated language reference omitted the stock MPO declaration")
    good = compile_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\tndeclareatom{\tnphase}{skin=box, ports={west:virtual,east:virtual}}
\begin{document}
\begin{tenkz}[rows={wire}]\tn{A}&\tnphase{B}\end{tenkz}
\end{document}
""")
    if good.returncode:
        raise SystemExit(f"typed declaration did not compile:\n{good.stdout}")
    bad = compile_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\tndeclareatom{\tnbad}{skin=box, ports={west:physical}}
\begin{document}x\end{document}
""")
    if bad.returncode == 0 or "TKZ-ATOM-INVALID-PORT" not in bad.stdout:
        raise SystemExit("invalid typed port did not produce TKZ-ATOM-INVALID-PORT")
    canonical, canonical_events = compile_event_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[boundary=periodic]\tn{A}&\tn{B}\end{tenkz}
\end{document}
""")
    compatible, compatible_events = compile_event_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[periodic]\tn{A}&\tn{B}\end{tenkz}
\end{document}
""")
    if canonical.returncode or compatible.returncode:
        raise SystemExit("canonical/compatibility event-equivalence probe did not compile")
    if canonical_events != compatible_events:
        raise SystemExit("boundary=periodic and periodic emitted different semantic events")
    print("PASS: registry, typed atom diagnostic, and alias event equivalence")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
