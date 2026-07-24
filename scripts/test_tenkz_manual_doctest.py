#!/usr/bin/env python3
"""Regression checks for tenkz manual example extraction and coverage."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from types import SimpleNamespace
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
\begin{tnmultiples}% a commented } must not affect the option scanner
[
  caption={domain [0,1)}, % nor may this commented } affect it
  index={options={[some key=val, other=x]}},
  variants={{dot}{dot},{box}{box}}]
\verb|\end{tnmultiples}|
\begin{tenkz} \tn[variant]{A} \end{tenkz}
\end{tnmultiples}
\begin{Verbatim}
\tntree{((ab)c)}
\end{Verbatim}
\begin{Verbatim}
\usepackage[
  draft
]{graphicx}
\begin{tenkz} \tn{multiline-package} \end{tenkz}
\end{Verbatim}
% \begin{tnexample}
% \begin{tenkz} \tn{commented} \end{tenkz}
% \end{tnexample}
\begin{Verbatim}
\documentclass[
  border=2pt
]{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz} \tn{complete} \end{tenkz}
\end{document}
\end{Verbatim}
"""
    with tempfile.TemporaryDirectory(prefix="tenkz-doctest-unit-") as tmp:
        path = Path(tmp) / "fixture.tex"
        path.write_text(fixture, encoding="utf-8")
        extracted = DOCTEST.extract_displayed_examples(path)
    if len(extracted) != 5 or any(
        r"\begin{tenkz}" not in example.document for example in extracted[:2]
    ):
        raise AssertionError("nested tnmultiple options confused body extraction")
    if not all("variant/.style" in example.document for example in extracted[:2]):
        raise AssertionError("tnmultiples variants were not installed independently")
    if r"\tntree" not in extracted[2].document:
        raise AssertionError("a registry command in Verbatim was not recognized as TeX")
    multiline_package = extracted[3].document
    if multiline_package.index("]{graphicx}") > multiline_package.index(
        r"\begin{document}"
    ):
        raise AssertionError("a multiline package declaration was split across the body")
    complete = extracted[4].document
    if complete.count(r"\documentclass") != 1 or r"\tn{commented}" in complete:
        raise AssertionError("complete or commented Verbatim documents were mishandled")

    captured: dict[str, object] = {}
    original_run = DOCTEST.subprocess.run

    def capture_run(*args: object, **kwargs: object) -> SimpleNamespace:
        captured.update(kwargs)
        return SimpleNamespace(returncode=0, stdout="")

    DOCTEST.subprocess.run = capture_run
    try:
        with tempfile.TemporaryDirectory(prefix="tenkz-doctest-path-") as tmp:
            DOCTEST.compile_example(reference[0], "xelatex", Path(tmp))
    finally:
        DOCTEST.subprocess.run = original_run
    texinputs = str(captured["env"]["TEXINPUTS"])
    if not texinputs.startswith(f"{reference[0].source.parent}//:"):
        raise AssertionError("a reference example cannot resolve files beside its source")
    if r"\tnarrow" in DOCTEST._strip_tex_comments(r"\\% \tnarrow"):
        raise AssertionError("an even-backslash percent did not start a TeX comment")
    if r"\tnarrow" not in DOCTEST._strip_tex_comments(r"\% \tnarrow"):
        raise AssertionError("an escaped percent incorrectly started a TeX comment")

    print("PASS: tenkz manual doctest extraction and reference coverage")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
