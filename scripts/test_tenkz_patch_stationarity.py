#!/usr/bin/env python3
"""Check the source-owned ordered coordinate insertion and its production render."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

from tenkz_paths import ensure_pythonpath

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
import tenkz_pic  # noqa: E402

CHAPTER = ROOT / "blueprint/src/chapter/ch24_peps_regularized_patch_stationarity.tex"
EXPECTED_WIRES = [
    ("open w", "coordinateouter.180"),
    ("coordinateouter.0", "coordinateinsert.180"),
    ("coordinateinsert.0", "coordinateinner.180"),
    ("coordinateinner.0", "coordinatestate.180"),
]


def main() -> int:
    chapter = CHAPTER.read_text(encoding="utf-8")
    units = re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", chapter, re.S)
    assert len(units) == 1, "one source-owned ordered insertion"
    unit = units[0]
    assert not re.search(r"\\(?:begin\{tikzpicture\}|draw\b|fill\b|node\b)", chapter)
    wires = re.findall(r"\\tnwire(?:\[[^]]*\])?\{([^}]+)\}\{([^}]+)\}", unit)
    assert wires == EXPECTED_WIRES, ("action order or open boundary changed", wires)
    for source in [
        "at=(1,1), name=coordinateouter", "at=(1,3), name=coordinateinsert",
        "at=(1,5), name=coordinateinner", "at=(1,7), name=coordinatestate",
        r"{P_j^+}", r"{D_j}", r"{P_j^-}", r"{\Omega}",
    ]:
        assert source in unit, source
    labels = {
        "coordinateouter": r"P_j^+", "coordinateinsert": r"D_j",
        "coordinateinner": r"P_j^-", "coordinatestate": r"\Omega",
    }
    for name, label in labels.items():
        atom = rf"\\tn\[[^]]*name={name},[^]]*\]\{{{re.escape(label)}\}}"
        assert re.search(atom, unit, re.S), (name, "wrong ordered-factor label")
    for source in [
        r"D_j=\iota_{X_j}(BK_j-K_jB)",
        r"\Delta_j=P_j^+D_jP_j^-\Omega",
        "carries the full space", "need not be supported on",
        "Starting at", "acts first", "second", "last",
    ]:
        assert source in chapter, source
    with tempfile.TemporaryDirectory(prefix="tenkz_patch_stationarity_") as tmp:
        work = Path(tmp)
        svg, cold_hit = tenkz_pic.render_unit(unit, work)
        assert svg is not None and svg.is_file(), "production rendering unavailable"
        assert not cold_hit, "fresh output directory must render"
        assert "<path" in svg.read_text(encoding="utf-8"), "missing SVG ink"
        stamp = svg.stat().st_mtime_ns
        digest = hashlib.sha256(svg.read_bytes()).hexdigest()
        again, warm_hit = tenkz_pic.render_unit(unit, work)
        assert warm_hit and again == svg
        assert stamp == svg.stat().st_mtime_ns
        assert digest == hashlib.sha256(svg.read_bytes()).hexdigest()
        event_log = tenkz_pic.unit_event_log(unit, work)
        assert event_log is not None, "complete event stream required"
        raw = event_log.read_text(encoding="utf-8")
        assert len(re.findall(r"^atom\|", raw, re.M)) == 4
        assert len(re.findall(r"^wire\|", raw, re.M)) == 4
        assert re.findall(r"^kernel-boundary\|signature=(.*)$", raw, re.M) == ["phys:w"]
        assert "kernel-error|" not in raw
        source_file = work / "ordered-insertion.tex"
        source_file.write_text(unit + "\n", encoding="utf-8")
        audit = Audit(event_log, source_file)
        audit.run()
        findings = [
            {"severity": f.severity, "rule": f.rule, "message": f.msg}
            for f in audit.findings
        ]
        assert not [f for f in findings if f["severity"] == "HARD"], findings
        record = {
            "result": "passed",
            "chapter": str(CHAPTER.relative_to(ROOT)),
            "chapter_sha256": hashlib.sha256(CHAPTER.read_bytes()).hexdigest(),
            "production_renderer": "blueprint/src/Packages/tenkz_pic.py",
            "unit_hash": tenkz_pic.unit_hash(unit),
            "svg_sha256": digest,
            "route": tenkz_pic.toolchain().route,
            "cold_cache_hit": cold_hit, "warm_cache_hit": warm_hit,
            "warm_file_unchanged": True,
            "atoms": 4, "wires": 4, "boundary": "phys:w",
            "semantic_checks": [
                "right-to-left action: original lower-index product, lifted commutator, original higher-index product",
                "all four wires are full-space configuration indices",
                "three internal contractions and exactly one global output index",
                "outer products have no asserted support on the selected region",
            ],
            "findings": findings,
            "limits": ["Standalone production renderer; not a full plasTeX web build."],
        }
        output = os.environ.get("TENKZ_TEST_OUTPUT")
        if output:
            target = Path(output)
            target.mkdir(parents=True, exist_ok=True)
            shutil.copy2(svg, target / "ordered-insertion.svg")
            shutil.copy2(event_log, target / "ordered-insertion.tnlog")
            shutil.copy2(source_file, target / source_file.name)
            (target / "diagram-validation.json").write_text(json.dumps(record, indent=2) + "\n")
            (target / "ordered-insertion-document.tex").write_text(tenkz_pic._latex_document(unit))
    print("PASS: ordered insertion, four global tensors, three contractions, one output; cold/warm production render")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
