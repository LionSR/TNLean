#!/usr/bin/env python3
"""Regression check for the II_RFP block-and-multiplicity routing graph."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

from tenkz_audit import Audit


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "blueprint/src"
CHAPTER = SOURCE_ROOT / "chapter/ch26_mps_rfp_core.tex"
BEGIN = "% TENKZ-II-RFP-BEGIN"
END = "% TENKZ-II-RFP-END"


def read_tex_tree(path: Path) -> str:
    """Read a TeX source after recursively expanding its input wrappers."""
    source = path.read_text(encoding="utf-8")

    def expand(match: re.Match[str]) -> str:
        target = match.group(1)
        if not target.endswith(".tex"):
            target += ".tex"
        return read_tex_tree(SOURCE_ROOT / target)

    return re.sub(r"\\input\{([^}]+)\}", expand, source)


# The figure's contraction graph, spelled endpoint by endpoint.  An
# endpoint is an atom face (``name.bearing``) or an open boundary end
# (``open w`` / ``open e`` / ``open n``).  The graph, the coefficient
# arities, and the boundary signature are the mathematical content of
# the figure; everything else is presentation.
EXPECTED_PORTS = {
    "X": {"180": "virtual", "0": "virtual", "270": "virtual"},
    "rho": {"180": "virtual", "0": "virtual", "270": "virtual"},
    "mid": {"90": "virtual", "0": "virtual", "270": "virtual"},
    "M": {"180": "virtual", "0": "virtual", "270": "virtual"},
    "Xinv": {"180": "virtual", "0": "virtual", "135": "virtual",
             "270": "virtual"},
    "U": {"225": "virtual", "270": "virtual", "315": "virtual",
          "90": "physical"},
    "jX": {"180": "virtual", "0": "virtual", "90": "virtual",
           "270": "virtual"},
    "jrho": {"180": "virtual", "0": "virtual", "90": "virtual"},
    "jU": {"180": "virtual", "0": "virtual", "90": "virtual"},
    "jXinv": {"180": "virtual", "0": "virtual", "90": "virtual",
              "270": "virtual"},
    "qX": {"180": "virtual", "0": "virtual", "90": "virtual"},
    "qM": {"180": "virtual", "0": "virtual", "90": "virtual"},
    "qXinv": {"180": "virtual", "0": "virtual", "90": "virtual"},
}
EXPECTED_WIRES = {
    frozenset(edge)
    for edge in (
        ("X.180", "open w"),
        ("X.0", "rho.180"),
        ("U.225", "rho.0"),
        ("U.270", "mid.90"),
        ("U.315", "Xinv.135"),
        ("mid.0", "M.180"),
        ("M.0", "Xinv.180"),
        ("Xinv.0", "open e"),
        ("U.90", "open n"),
        ("X.270", "jX.90"),
        ("rho.270", "jrho.90"),
        ("mid.270", "jU.90"),
        ("Xinv.270", "jXinv.90"),
        ("jX.270", "qX.90"),
        ("M.270", "qM.90"),
        ("jXinv.270", "qXinv.90"),
        ("jX.180", "open w"),
        ("jX.0", "jrho.180"),
        ("jrho.0", "jU.180"),
        ("jU.0", "jXinv.180"),
        ("jXinv.0", "open e"),
        ("qX.180", "open w"),
        ("qX.0", "qM.180"),
        ("qM.0", "qXinv.180"),
        ("qXinv.0", "open e"),
    )
}
EXPECTED_COEFF_ARITIES = {"X": 3, "rho": 3, "U": 4, "M": 3, "Xinv": 4}
EXPECTED_BOUNDARY = "open:e, open:e, open:e, open:w, open:w, open:w, phys:n"


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1

    chapter = read_tex_tree(CHAPTER)
    if chapter.count(BEGIN) != 1 or chapter.count(END) != 1:
        raise AssertionError("II_RFP routing markers must occur exactly once")
    body = chapter.split(BEGIN, 1)[1].split(END, 1)[0]

    declared_ports: dict[str, dict[str, str]] = {}
    for match in re.finditer(
        r"\\tn\[(?P<options>[^]]*)\]\s*\{", body, re.DOTALL
    ):
        options = match["options"]
        name = re.search(r"name=(?P<name>[A-Za-z]+)", options)
        ports = re.search(r"ports=\{(?P<ports>[^}]*)\}", options, re.DOTALL)
        if name is None or ports is None:
            continue
        declared_ports[name["name"]] = {
            bearing.strip(): port_type.split(":", 1)[0].strip()
            for item in ports["ports"].split(",")
            for bearing, port_type in [item.split(":", 1)]
        }
    if declared_ports != EXPECTED_PORTS:
        raise AssertionError(
            f"II_RFP port declarations changed: {declared_ports}"
        )

    wires = [
        frozenset((match["a"].strip(), match["b"].strip()))
        for match in re.finditer(
            r"\\tnwire(?:\[[^]]*\])?\s*\{(?P<a>[^}]+)\}\s*\{(?P<b>[^}]+)\}",
            body,
        )
    ]
    if len(wires) != len(EXPECTED_WIRES) or set(wires) != EXPECTED_WIRES:
        raise AssertionError("II_RFP contraction graph changed")

    # Every declared port is consumed exactly once: the wired faces of
    # each atom must be exactly its declared bearings.
    wired: dict[str, Counter[str]] = {}
    for edge in wires:
        for endpoint in edge:
            if endpoint.startswith("open "):
                continue
            name, bearing = endpoint.split(".", 1)
            wired.setdefault(name, Counter())[bearing] += 1
    for name, bearings in EXPECTED_PORTS.items():
        used = wired.get(name, Counter())
        if used != Counter(bearings.keys()):
            raise AssertionError(
                f"II_RFP port usage for {name} changed: {dict(used)}"
            )

    arities = {
        name: len(EXPECTED_PORTS[name]) for name in EXPECTED_COEFF_ARITIES
    }
    if arities != EXPECTED_COEFF_ARITIES:
        raise AssertionError(f"II_RFP coefficient arity changed: {arities}")

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
        audit = Audit(log_path, tex)
        audit.parse_log()
        audit.check_dialects()
        hard = [finding for finding in audit.findings if finding.severity == "HARD"]
        if hard:
            raise AssertionError(f"II_RFP event stream has hard findings: {hard}")
        events = audit.events()

    boundary = [
        event.attrs["signature"]
        for event in events
        if event.kind == "kernel-boundary"
    ]
    if boundary != [EXPECTED_BOUNDARY]:
        raise AssertionError(f"II_RFP boundary signature changed: {boundary}")

    print("PASS: II_RFP block and multiplicity rails retain their routed arities")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
