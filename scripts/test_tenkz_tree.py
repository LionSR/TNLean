#!/usr/bin/env python3
"""Regression checks for wire/ribbon fusion-tree skins and tree audit data."""

from __future__ import annotations

import io
import os
import shutil
import subprocess
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

from tenkz_audit import Audit


ROOT = Path(__file__).resolve().parents[1]
SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\tndeclare{species}{anyon}{hue=source:red}
% With fusion bases chosen and multiplicity labels suppressed, both calls
% denote the same basis morphism; only the skin changes.
\tntree[tree style=wire, species=anyon]{((a\,b)_x\,c)_e}
\tntree[tree style=ribbon, species=anyon]{((a\,b)_x\,c)_e}
\tntree[tree style=ribbon, species=anyon, role=marked]{(a\,(b\,c)_u)_e}
\end{document}
"""

NESTED_CD_SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\usepackage{tikz-cd}
\pagestyle{empty}
\begin{document}
\begin{tikzcd}[column sep=large]
  \tntree{(a\,b)_c} \arrow[r, "F"] \arrow[d, "G"']
    & \tntree{(b\,a)_c} \arrow[d, "G"] \\
  A \arrow[r, "F"'] & B
\end{tikzcd}
\makeatletter
\typeout{TENKZ-CELL-SHAPE=\csname pgf@sh@ns@\tikzcdmatrixname-1-1\endcsname}
\makeatother
\end{document}
"""


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("SKIP: xelatex not found")
        return 0
    with tempfile.TemporaryDirectory(prefix="tenkz-tree-") as tmp:
        work = Path(tmp)
        tex = work / "trees.tex"
        tex.write_text(SOURCE, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get("TEXINPUTS", "")
        try:
            run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
                cwd=work,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
        except subprocess.TimeoutExpired as exc:
            print(exc.stdout or "")
            print("FAIL: wire/ribbon tree fixture timed out after 120 seconds")
            return 1
        if run.returncode:
            print(run.stdout)
            print("FAIL: wire/ribbon tree fixture did not compile")
            return 1

        log = work / "trees.tnlog"
        audit = Audit(log, tex)
        with redirect_stdout(io.StringIO()):
            status = audit.run()
        if status:
            raise AssertionError("audit rejected valid wire/ribbon tree events")
        lines = log.read_text(encoding="utf-8").splitlines()
        if len(lines) != 3:
            raise AssertionError(f"expected three tree events, got {len(lines)}")
        if "style=wire" not in lines[0] or "style=ribbon" not in lines[1]:
            raise AssertionError("tree style was not recorded")
        topology = "topology=((1,2),3)"
        if topology not in lines[0] or topology not in lines[1]:
            raise AssertionError("the two skins did not preserve one topology")
        if "role=marked|species=anyon" not in lines[2]:
            raise AssertionError("tree role/species semantics were not recorded")

        nested_tex = work / "nested-cd-trees.tex"
        nested_tex.write_text(NESTED_CD_SOURCE, encoding="utf-8")
        nested_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", nested_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if nested_run.returncode:
            print(nested_run.stdout)
            print("FAIL: nested tikz-cd tree fixture did not compile")
            return 1
        if "TENKZ-CELL-SHAPE=asymmetrical rectangle" not in nested_run.stdout:
            raise AssertionError("tenkz changed the enclosing tikz-cd cell shape")

        nested_log = work / "nested-cd-trees.tnlog"
        nested_audit = Audit(nested_log, nested_tex)
        with redirect_stdout(io.StringIO()):
            nested_status = nested_audit.run()
        if nested_status:
            raise AssertionError("audit rejected valid nested tikz-cd tree events")
        nested_lines = nested_log.read_text(encoding="utf-8").splitlines()
        tree_events = sum(line.startswith("tree|") for line in nested_lines)
        if tree_events != 2:
            raise AssertionError(
                "nested tikz-cd cells did not log one tree event per \\tntree: "
                f"got {tree_events}"
            )

        malformed = work / "malformed.tnlog"
        overlong = "9" * 5000
        deep = "(" * 1500 + "1" + ",2)" * 1500
        malformed.write_text(
            "tree|picture=0|id=1|style=ribbon|leaves=3|vertices=2|"
            "topology=((1,3),2)|role=none|species=none\n"
            "tree|picture=0|id=2|style=wire|leaves=2|vertices=1|"
            "topology=(1,{a})|role=none|species=none\n"
            f"tree|picture=0|id=3|style=wire|leaves=2|vertices=1|"
            f"topology=({overlong},2)|role=none|species=none\n"
            f"tree|picture=0|id=4|style=ribbon|leaves=1501|vertices=1500|"
            f"topology={deep}|role=none|species=none\n"
            f"tree|picture=0|id={overlong}|style=wire|leaves=2|vertices=1|"
            f"topology=(1,2)|role=none|species=none\n",
            encoding="utf-8",
        )
        malformed_audit = Audit(malformed, None)
        malformed_audit.parse_log()
        failures = [
            finding for finding in malformed_audit.findings
            if finding.rule == "malformed-tree"
        ]
        if len(failures) != 4:
            raise AssertionError("audit accepted noncanonical tree topology")
        numeric_failures = [
            finding for finding in malformed_audit.findings
            if finding.rule == "malformed-event"
            and "tree field id=" in finding.msg
        ]
        if len(numeric_failures) != 1:
            raise AssertionError("audit integer validator accepted an overlong tree id")

    print("PASS: wire/ribbon trees share topology and emit structural audit data")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
