#!/usr/bin/env python3
"""Regression check for the II_RFP block-and-multiplicity routing graph."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

from tenkz_audit import Audit


ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch26_mps_rfp_core.tex"
BEGIN = "% TENKZ-II-RFP-BEGIN"
END = "% TENKZ-II-RFP-END"


def attrs(line: str) -> tuple[str, dict[str, str]]:
    fields = line.split("|")
    return fields[0], dict(field.split("=", 1) for field in fields[1:])


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1

    chapter = CHAPTER.read_text(encoding="utf-8")
    if chapter.count(BEGIN) != 1 or chapter.count(END) != 1:
        raise AssertionError("II_RFP routing markers must occur exactly once")
    body = chapter.split(BEGIN, 1)[1].split(END, 1)[0]
    source = (
        "\\documentclass{article}\n"
        "\\usepackage{tenkz}\n"
        "\\pagestyle{empty}\n"
        "\\begin{document}\n"
        f"{body}\n"
        "\\end{document}\n"
    )

    with tempfile.TemporaryDirectory(prefix="tenkz_index_routing_") as tmp:
        work = Path(tmp)
        tex = work / "ii-rfp-routing.tex"
        tex.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get("TEXINPUTS", "")
        run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if run.returncode:
            print(run.stdout)
            print("FAIL: II_RFP routing fixture did not compile")
            return 1
        log_path = work / "ii-rfp-routing.tnlog"
        lines = log_path.read_text(encoding="utf-8").splitlines()
        audit = Audit(log_path, tex)
        audit.parse_log()
        audit.check_dialects()
        hard = [finding for finding in audit.findings if finding.severity == "HARD"]
        if hard:
            raise AssertionError(f"II_RFP event stream has hard findings: {hard}")

    parsed = [attrs(line) for line in lines]
    atoms = {
        event["name"]: event["kind"]
        for kind, event in parsed
        if kind == "atom"
    }
    expected_atoms = {
        "rfpWest": "boundary", "rfpX": "box", "rfpLambda": "box",
        "rfpU": "box", "rfpMain": "dot", "rfpM": "box",
        "rfpXinv": "box", "rfpEast": "boundary",
        "rfpPhysical": "boundary", "rfpJwest": "boundary",
        "rfpXj": "dot", "rfpLambdaj": "dot", "rfpUj": "dot",
        "rfpXinvj": "dot", "rfpJeast": "boundary",
        "rfpQwest": "boundary", "rfpXq": "dot", "rfpMq": "dot",
        "rfpXinvq": "dot", "rfpQeast": "boundary",
    }
    if atoms != expected_atoms:
        raise AssertionError(f"II_RFP atoms changed: {atoms}")

    joins = [
        frozenset((event["from"], event["to"]))
        for kind, event in parsed
        if kind == "join"
    ]
    expected_joins = {
        frozenset(edge)
        for edge in (
            ("rfpWest.east", "rfpX.west"),
            ("rfpX.east", "rfpLambda.west"),
            ("rfpLambda.east", "rfpU.south west"),
            ("rfpU.south east", "rfpXinv.north west"),
            ("rfpU.south", "rfpMain.north"),
            ("rfpMain.east", "rfpM.west"),
            ("rfpM.east", "rfpXinv.west"),
            ("rfpXinv.east", "rfpEast.west"),
            ("rfpPhysical.south", "rfpU.north"),
            ("rfpX.south", "rfpXj.north"),
            ("rfpXj.south", "rfpXq.north"),
            ("rfpLambda.south", "rfpLambdaj.north"),
            ("rfpMain.south", "rfpUj.north"),
            ("rfpM.south", "rfpMq.north"),
            ("rfpXinv.south", "rfpXinvj.north"),
            ("rfpXinvj.south", "rfpXinvq.north"),
            ("rfpJwest.east", "rfpXj.west"),
            ("rfpXj.east", "rfpLambdaj.west"),
            ("rfpLambdaj.east", "rfpUj.west"),
            ("rfpUj.east", "rfpXinvj.west"),
            ("rfpXinvj.east", "rfpJeast.west"),
            ("rfpQwest.east", "rfpXq.west"),
            ("rfpXq.east", "rfpMq.west"),
            ("rfpMq.east", "rfpXinvq.west"),
            ("rfpXinvq.east", "rfpQeast.west"),
        )
    }
    if len(joins) != len(expected_joins) or set(joins) != expected_joins:
        raise AssertionError("II_RFP join graph changed")

    degree: Counter[str] = Counter()
    for edge in joins:
        for endpoint in edge:
            degree[endpoint.split(".", 1)[0]] += 1
    boundary_names = {name for name, kind in atoms.items() if kind == "boundary"}
    if any(degree[name] != 1 for name in boundary_names):
        raise AssertionError(f"II_RFP boundary is not open exactly once: {degree}")
    expected_coeff_degrees = {
        "rfpX": 3, "rfpLambda": 3, "rfpU": 4,
        "rfpM": 3, "rfpXinv": 4,
    }
    if any(degree[name] != value for name, value in expected_coeff_degrees.items()):
        raise AssertionError(f"II_RFP coefficient arity changed: {degree}")

    print("PASS: II_RFP block and multiplicity rails retain their routed arities")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
