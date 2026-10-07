#!/usr/bin/env python3
"""Audit the source-linked D² endpoint picture with an individual-site middle."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_paths import ensure_pythonpath, tenkz_tex

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch12_symmetry_string_order_finite_endpoints.tex"


def check(work: Path) -> None:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    chapter = CHAPTER.read_text(encoding="utf-8")
    begin = "% TENKZ-STRING-BLOCK-ENDPOINTS-BEGIN"
    end = "% TENKZ-STRING-BLOCK-ENDPOINTS-END"
    assert chapter.count(begin) == chapter.count(end) == 1
    body = chapter.split(begin, 1)[1].split(end, 1)[0]
    assert body.count(r"\begin{tenkz}") == 1
    assert "rows={ket,bra}, cols=5" in body
    assert r"west={cup=$\Lambda$}, east=cup" in body
    assert body.count(r"\tn[label pos=n]{A^{[q]}}") == 2
    assert body.count(r"\tn[label pos=s, conjugate]{\overline{A^{[q]}}}") == 2
    for column, operator in ((1, "x"), (2, "u"), (4, "u"), (5, "y")):
        assert f"at=on bond-1-{column}-2-{column} 0.5]{{{operator}}}" in body
    assert body.count(r"$q\text{ sites}$") == 2
    assert body.count(r"$N\text{ sites}$") == 1
    assert r"{u^{[q]}}" not in body and r"{u^{\otimes q}}" not in body
    source = (
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
        "\\usepackage{tenkz}\n\\pagestyle{empty}\n\\begin{document}\n"
        + body + "\n\\end{document}\n"
    )
    tex = work / "string-endpoints.tex"
    tex.write_text(source, encoding="utf-8")
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    (work / "render.log").write_text(run.stdout, encoding="utf-8")
    if run.returncode:
        print(run.stdout)
        raise SystemExit("FAIL: physical endpoint diagram did not compile")
    audit = Audit(work / "string-endpoints.tnlog", tex)
    audit.run()
    hard = [finding for finding in audit.findings if finding.severity == "HARD"]
    assert not hard, hard
    signatures = [event.attrs["signature"] for event in audit.events()
                  if event.kind == "kernel-boundary"]
    assert signatures == [""], signatures
    assert "Overfull \\hbox" not in run.stdout, "Endpoint picture exceeds the text width"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, help="Keep the native render for visual review")
    args = parser.parse_args()
    if args.output_dir is None:
        with tempfile.TemporaryDirectory(prefix="tenkz_string_endpoints_") as tmp:
            check(Path(tmp))
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check(args.output_dir)
    print("PASS: D² endpoint blocks and N individual twists have scalar boundary signature")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
