#!/usr/bin/env python3
"""Regression checks for tenkz manual example extraction and coverage."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "tenkz_manual_doctest.py"
SPEC = importlib.util.spec_from_file_location("tenkz_manual_doctest", SCRIPT)
assert SPEC and SPEC.loader
DOCTEST = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = DOCTEST
SPEC.loader.exec_module(DOCTEST)


def main() -> int:
    manual = DOCTEST.displayed_examples()
    reference = DOCTEST.reference_examples()
    if len(manual) != 9:
        raise AssertionError(f"expected 9 displayed TeX examples, found {len(manual)}")
    if len(reference) != 18:
        raise AssertionError(f"expected 18 reference examples, found {len(reference)}")
    if any(r"\begin{document}" not in example.document for example in manual):
        raise AssertionError("a displayed example was not wrapped as a document")
    if any("tenkz_rmp.sh" in example.document for example in manual):
        raise AssertionError("the displayed shell session was treated as TeX")

    fixture = r"""
\begin{tnmultiples}[
  variants={a={title={A [nested] title}},b={title=B}}]
\begin{tenkz} \tn{A} \end{tenkz}
\end{tnmultiples}
"""
    with tempfile.TemporaryDirectory(prefix="tenkz-doctest-unit-") as tmp:
        path = Path(tmp) / "fixture.tex"
        path.write_text(fixture, encoding="utf-8")
        extracted = DOCTEST.extract_displayed_examples(path)
    if len(extracted) != 1 or r"\begin{tenkz}" not in extracted[0].document:
        raise AssertionError("nested tnmultiple options confused body extraction")

    print("PASS: tenkz manual doctest extraction and reference coverage")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
