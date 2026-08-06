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
    if len(manual) != 14:
        raise AssertionError(f"expected 14 displayed TeX examples, found {len(manual)}")
    if len(reference) != 25:
        raise AssertionError(f"expected 25 reference examples, found {len(reference)}")
    if any(r"\begin{document}" not in example.document for example in manual):
        raise AssertionError("a displayed example was not wrapped as a document")
    if any("tenkz_rmp.py" in example.document for example in manual):
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
\verb|\documentclass{standalone}| \documentclasswrapper \usepackagewrapper{foo}
\string\usepackage{missing-package} \\usepackage{also-missing} \tntree{(ab)}
\end{Verbatim}
\begin{Verbatim}
shell command % \tntree{commented}
\end{Verbatim}
\begin{Verbatim}
\usepackage[
  draft
]{graphicx}
\usepackage{amsmath,tenkz}
\begin{tenkz} \tn{multiline-package} \end{tenkz}
\end{Verbatim}
% \begin{tnexample}
% \begin{tenkz} \tn{commented} \end{tenkz}
% \end{tnexample}
\newif\ifdraft
\newcommand{\storedguard}{\IfFileExists}
\let\ifalias\ifdraft
\let\ifnever\iffalse
\let\ifbare\if
\iffalse
\IfFileExists
\newif\iflocal
\let\iflocalbare\if
\iftrue
\newcommand{\stored}{\fi}
\ifalias
\fi
\if@twocolumn
\fi
\ifbare ab
\fi
\ifdraft
\ifthenelse{ignored}{ignored}{ignored}
\fi
\begin{tnexample}
\begin{tenkz} \tn{false-branch} \end{tenkz}
\end{tnexample}
\fi
\IfFileExists{missing-conditional.tex}{\newif\ifghost}{}
\iffalse
\ifghost
\fi
\begin{tnexample}
\begin{tenkz} \tn{inactive-file-declaration} \end{tenkz}
\end{tnexample}
\IfFileExists{present-conditional.tex}{\newif\ifpresent}{}
\iffalse
\ifpresent
\fi
\begin{tnexample}
\begin{tenkz} \tn{active-file-declaration} \end{tenkz}
\end{tnexample}
\fi
\def\iflate{not yet a conditional}
\iffalse
\iflate
\fi
\begin{tnexample}
\begin{tenkz} \tn{declaration-order} \end{tenkz}
\end{tnexample}
\newif\iflate
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
        (Path(tmp) / "present-conditional.tex").write_text("", encoding="utf-8")
        path.write_text(fixture, encoding="utf-8")
        extracted = DOCTEST.extract_displayed_examples(path)
    if len(extracted) != 8 or any(
        r"\begin{tenkz}" not in example.document for example in extracted[:2]
    ):
        raise AssertionError("nested tnmultiple options confused body extraction")
    if not all("variant/.style" in example.document for example in extracted[:2]):
        raise AssertionError("tnmultiples variants were not installed independently")
    if r"\tntree" not in extracted[2].document:
        raise AssertionError("a registry command in Verbatim was not recognized as TeX")
    if not extracted[3].document.startswith(r"\documentclass{article}") or (
        r"\documentclasswrapper" not in extracted[3].document
    ):
        raise AssertionError("a documentclass spelling inside verb was executed")
    multiline_package = extracted[4].document
    if multiline_package.index("]{graphicx}") > multiline_package.index(
        r"\begin{document}"
    ):
        raise AssertionError("a multiline package declaration was split across the body")
    if r"\tn{inactive-file-declaration}" not in extracted[5].document:
        raise AssertionError("an inactive file branch declared a conditional")
    if r"\tn{declaration-order}" not in extracted[6].document:
        raise AssertionError("a later newif declaration changed an earlier false branch")
    complete = extracted[7].document
    if complete.count(r"\documentclass") != 1 or r"\tn{commented}" in complete:
        raise AssertionError("complete or commented Verbatim documents were mishandled")

    captured: dict[str, object] = {}
    original_run = DOCTEST.subprocess.run

    def capture_run(*args: object, **kwargs: object) -> SimpleNamespace:
        captured.update(kwargs)
        return SimpleNamespace(returncode=0, stdout=reference[0].coverage_marker)

    DOCTEST.subprocess.run = capture_run
    try:
        with tempfile.TemporaryDirectory(prefix="tenkz-doctest-path-") as tmp:
            DOCTEST.compile_example(reference[0], "xelatex", Path(tmp))
    finally:
        DOCTEST.subprocess.run = original_run
    texinputs = str(captured["env"]["TEXINPUTS"])
    if not texinputs.startswith(f"{reference[0].source.parent}//:"):
        raise AssertionError("a reference example cannot resolve files beside its source")
    if f":{DOCTEST.MANUAL_DIR}//:" not in texinputs:
        raise AssertionError("a manual example cannot resolve files from the manual root")
    if r"\tnarrow" in DOCTEST._strip_tex_comments(r"\\% \tnarrow"):
        raise AssertionError("an even-backslash percent did not start a TeX comment")
    if r"\tnarrow" not in DOCTEST._strip_tex_comments(r"\% \tnarrow"):
        raise AssertionError("an escaped percent incorrectly started a TeX comment")
    if DOCTEST._has_executable_command(r"\verb|\tn| \string\tn \\tn", "tn"):
        raise AssertionError("a non-executed command spelling satisfied reference coverage")
    if DOCTEST._is_tenkz_verbatim(
        r"\verb|\tn| \string\tn \\tn", Path.cwd()
    ):
        raise AssertionError("a non-executed command spelling classified a Verbatim block")
    if DOCTEST._is_tenkz_verbatim(
        r"% \begin{tenkz} \tn{commented} \end{tenkz}", Path.cwd()
    ):
        raise AssertionError("a commented environment classified a Verbatim block")
    package_names = DOCTEST._package_names(
        "\\usepackage{amsmath,% package note\n tenkz}"
    )
    if "tenkz" not in package_names:
        raise AssertionError("a comment hid tenkz in a multi-package declaration")
    repeated_package = (
        "\\iffalse\n\\usepackage{tenkz}\n\\fi\n"
        "\\IfFileExists{missing-instrumentation.tex}"
        "{\\usepackage{tenkz}}{}\n"
        "% \\usepackage{tenkz}\n"
        "\\usepackage{tenkz}\n"
        "\\begin{document}\\tn{A}\\end{document}\n"
    )
    instrumented, marker = DOCTEST._instrument_command(
        repeated_package, "tn", Path.cwd()
    )
    if instrumented.index(marker) < instrumented.rindex("\\usepackage{tenkz}"):
        raise AssertionError("runtime instrumentation used a commented package spelling")
    inert_invocations = (
        "\\usepackage{tenkz}\n"
        "\\iffalse\n\\tn{dead}\\fi\n"
        "\\newcommand{\\stored}{\\tn{stored}}\n"
        "\\begin{document}\\tn{live}\\end{document}\n"
    )
    instrumented, marker = DOCTEST._instrument_command(
        inert_invocations, "tn", Path.cwd()
    )
    if instrumented.index(marker) < instrumented.index(r"\begin{document}"):
        raise AssertionError("runtime instrumentation selected an inert invocation")
    inert_only = (
        "\\usepackage{tenkz}\n"
        "\\iffalse\n\\tn{dead}\\fi\n"
        "\\newcommand{\\stored}{\\tn{stored}}\n"
    )
    try:
        DOCTEST._instrument_command(inert_only, "tn", Path.cwd())
    except ValueError as error:
        if "no executable invocation" not in str(error):
            raise
    else:
        raise AssertionError("an inert command spelling counted as executable")
    escaped_verb = (
        "Write \\\\verb|without a closing delimiter on this line\n"
        "\\usepackage{tenkz}\n"
    )
    if r"\usepackage{tenkz}" not in DOCTEST._mask_inline_verbatim(escaped_verb):
        raise AssertionError("an escaped verb spelling masked a later source line")
    first_label = DOCTEST._source_label(DOCTEST.CHAPTERS / "basic" / "example.tex")
    second_label = DOCTEST._source_label(DOCTEST.CHAPTERS / "advanced" / "example.tex")
    if first_label == second_label:
        raise AssertionError("chapter-relative case labels are not unique")
    colliding_labels = {
        DOCTEST._source_label(DOCTEST.CHAPTERS / relative)
        for relative in ("basic/a_b.tex", "basic/a-b.tex", "a/b.tex", "a-b.tex")
    }
    if len(colliding_labels) != 4:
        raise AssertionError("source labels are not injective over paths")
    displayed_input = r"""
\begin{Verbatim}
\input{missing-example.tex}
\end{Verbatim}
"""
    if r"\input" in DOCTEST._mask_display_environments(displayed_input):
        raise AssertionError("a displayed input spelling remained in the structural graph")
    with tempfile.TemporaryDirectory(prefix="tenkz-doctest-graph-") as tmp:
        manual_dir = Path(tmp) / "manual"
        manual_dir.mkdir()
        chapters = manual_dir / "chapters2"
        chapters.mkdir()
        root = manual_dir / "manual2.tex"
        child = chapters / "child.tex"
        local = chapters / "local.tex"
        root.write_text(
            "\\newif\\ifshared\n"
            "\\newcommand{\\optionalchapter}{\\input{missing.tex}}\n"
            "\\verb|\\IfFileExists| \\string\\IfFileExists \\\\IfFileExists\n"
            "\\texttt{\\detokenize{\\IfFileExists}}\n"
            "\\begin{Verbatim}\n\\IfFileExists\n\\end{Verbatim}\n"
            "\\verb|100%|\\IfFileExists{missing-after-verb.tex}"
            "{\\input{missing-after-verb.tex}}"
            "{\\IfFileExists{chapters2/% continued\nchild.tex}"
            "{\\IfFileExists{chapters2/child}"
            "{\\input{chapters2/wrong-extensionless-branch.tex}}"
            "{\\IfFileExists{missing-generated.tex}"
            "{\\input{chapters2/missing-generated.tex}}"
            "{\\input chapters2/child}}}"
            "{\\input{chapters2/also-missing.tex}}}\n",
            encoding="utf-8",
        )
        child.write_text(
            "\\iffalse\\ifshared\\fi"
            "\\input{missing-shared-conditional.tex}\\fi\n"
            "\\IfFileExists{local.tex}{\\input{local.tex}}"
            "{\\input{missing-local.tex}}\n",
            encoding="utf-8",
        )
        local.write_text("", encoding="utf-8")
        ambient = Path(tmp) / "ambient"
        nested = ambient / "nested"
        nested.mkdir(parents=True)
        (nested / "ambient-only.tex").write_text("", encoding="utf-8")
        original_manual = DOCTEST.MANUAL
        original_manual_dir = DOCTEST.MANUAL_DIR
        original_chapters = DOCTEST.CHAPTERS
        DOCTEST.MANUAL = root
        DOCTEST.MANUAL_DIR = manual_dir
        DOCTEST.CHAPTERS = chapters
        original_texinputs = DOCTEST.os.environ.get("TEXINPUTS")
        try:
            sources = DOCTEST._manual_sources()
            DOCTEST.os.environ["TEXINPUTS"] = str(ambient)
            if DOCTEST._tex_file_exists(Path("ambient-only.tex"), manual_dir):
                raise AssertionError("a plain TEXINPUTS root was searched recursively")
            DOCTEST.os.environ["TEXINPUTS"] = f"{ambient}//"
            if not DOCTEST._tex_file_exists(Path("ambient-only.tex"), manual_dir):
                raise AssertionError("a recursive TEXINPUTS root was not searched")
            DOCTEST.os.environ.pop("TEXINPUTS", None)
            if DOCTEST.shutil.which("kpsewhich") and not DOCTEST._tex_file_exists(
                Path("article.cls"), manual_dir
            ):
                raise AssertionError("the default TeX search path was omitted")
        finally:
            if original_texinputs is None:
                DOCTEST.os.environ.pop("TEXINPUTS", None)
            else:
                DOCTEST.os.environ["TEXINPUTS"] = original_texinputs
            DOCTEST.MANUAL = original_manual
            DOCTEST.MANUAL_DIR = original_manual_dir
            DOCTEST.CHAPTERS = original_chapters
    ordered_parent = (
        "\\let\\ifformat\\if@twocolumn\n"
        "\\input{child.tex}\n"
        "\\newif\\iflaterparent\n"
    )
    child_offset = ordered_parent.index(r"\input")
    inherited = DOCTEST._conditionals_before(
        ordered_parent, child_offset, (), Path.cwd()
    )
    if "iflaterparent" in inherited:
        raise AssertionError("a declaration after input was inherited by the child")
    if "ifformat" not in inherited:
        raise AssertionError("an alias to a format conditional was not inherited")
    guarded_parent = (
        "\\IfFileExists{missing-conditional.tex}"
        "{\\newif\\ifguarded}{}\\input{child.tex}\n"
    )
    guarded_offset = guarded_parent.index(r"\input")
    guarded_inherited = DOCTEST._conditionals_before(
        guarded_parent, guarded_offset, (), Path.cwd()
    )
    if "ifguarded" in guarded_inherited:
        raise AssertionError("an inactive file branch leaked a child conditional")
    ordered_child = (
        "\\def\\iflaterparent{ordinary command}\n"
        "\\iffalse\n\\iflaterparent\n\\fi\n"
        "\\begin{tnexample}\n"
        "\\begin{tenkz}\\tn{ordered inheritance}\\end{tenkz}\n"
        "\\end{tnexample}\n"
    )
    with tempfile.TemporaryDirectory(prefix="tenkz-doctest-order-") as tmp:
        order_path = Path(tmp) / "child.tex"
        order_path.write_text(ordered_child, encoding="utf-8")
        if len(DOCTEST.extract_displayed_examples(order_path, inherited)) != 1:
            raise AssertionError("a later parent declaration hid a live child example")
    if {source.resolve() for source in sources} != {
        root.resolve(),
        child.resolve(),
        local.resolve(),
    }:
        raise AssertionError("the manual root or a traversed source was omitted")

    print("PASS: tenkz manual doctest extraction and reference coverage")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
