#!/usr/bin/env python3
"""Regression checks for measured grid enclosures."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_audit import Audit, canonical_hash


ROOT = Path(__file__).resolve().parents[1]

SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
% Two no-feature controls must remain structurally identical.
\begin{tenkz}[tensor style=box]
  \tn{X} & \tn{Y}
\end{tenkz}
\begin{tenkz}[tensor style=box]
  \tn{X} & \tn{Y}
\end{tenkz}

% Flat and asymmetric K1 ranges.
\begin{tenkz}[physical=up, tensor style=box]
  \tn{A}\tnspan[box, label pos=west]{3}{A^{[3]}} & \tndots & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={op,op}, tensor style=box]
  \tn{A}\tnspan[box]{3}{R} & \tn{B} & \tn{C} \\
  \tn{D}\tnspan[box, label pos=east]{2}{S} & \tn{E} &
\end{tenkz}

% A fusion bar has no glyph node, but its wedge, fused stub, and label are
% measured ink.  A box containing only that bar must resolve on either row
% instead of manufacturing an unregistered owner-cell name.
\begin{tenkz}[rows={wire,wire}]
  \tnfuse[span=2]{V}\tnspan[box, label pos=west]{1}{F} \\
  \tnspan[box, label pos=east]{1}{G}
\end{tenkz}

\end{document}
"""

EMPTY_BOX_LABEL_PROBE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\newcount\tenkzTestEmptySpanLabelNodes
\begin{document}
\begingroup
\tikzset{tn label/.append style={/utils/exec={%
  \global\advance\tenkzTestEmptySpanLabelNodes by 1\relax}}}
\begin{tenkz}[tensor style=box]
  \tn{A}\tnspan[box]{1}{}
\end{tenkz}
\endgroup
\ifnum\tenkzTestEmptySpanLabelNodes=0\relax\else
  \errmessage{empty box span materialized a phantom label node}
\fi
\end{document}
"""

NEGATIVE = {
    "shade": (r"""
\begin{tenkz}\tn{A}\tnspan[shade]{1}{A}\end{tenkz}
""", "/tenkz/span/shade"),
    "range": (r"""
\begin{tenkz}\tn{A}\tnspan[box]{0}{A}\end{tenkz}
""", "has length 0"),
    "label-position": (r"""
\begin{tenkz}\tn{A}\tnspan[box, label pos=around]{1}{A}\end{tenkz}
""", "Choice 'around' unknown"),
}


ENCLOSURE_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\begin{tenkz}
  \tnskip\tnspan[box]{1}{bad} &
  \tn{A}\tnspan[box]{1}{good} &
  \tn{B}\tnspan[box, label pos=around]{1}
    {\typeout{TENKZ-BAD-CHOICE-INK}bad} &
  \tn{C}\tnspan[shade=blue]{1}{\typeout{TENKZ-BAD-KEY-INK}bad} &
  \tn{D}\tnspan[box]{1}{\typeout{TENKZ-GOOD-OPTION-SPAN-INK}good}
  \typeout{TENKZ-EMPTY-SPAN-RECOVERED}
\end{tenkz}
\end{document}
"""


SPAN_SYNTAX_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\newcommand*{\tenkzTestBadSpanInk}{%
  \typeout{TENKZ-BAD-SPAN-SYNTAX-INK}bad}
\newcommand*{\tenkzTestGoodSpanInk}{%
  \typeout{TENKZ-GOOD-SPAN-SYNTAX-INK}good}
\begin{document}
\begin{tenkz}
  \tn{A}\tnspan[box]{notaninteger}{\tenkzTestBadSpanInk} &
  \tn{B}\tnspan[box]{1+1}{\tenkzTestBadSpanInk} &
  \tn{C}\tnspan[box]{02}{\tenkzTestGoodSpanInk} & \tn{D}
  \\
  \tn[box, species=undeclared]{X}
    \tnspan[box]{1}{\tenkzTestBadSpanInk} &
  \tn{Y}\tnspan[box]{1}{\tenkzTestGoodSpanInk} & \tn{Z} & \tn{W}
  \\
  \tn[role=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[physical=sideways]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[tri=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[mystery=1]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tnfuse[span=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tnfuse[span=2, combined=sideways]{X}
    \tnspan[box]{1}{\tenkzTestBadSpanInk} & \tn{Y} & &
  \\
  \tn[wide=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk}
    & \tn{Z} & &
  \\
  \tn[wires=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tnfuse[span=0]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[west at=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[up at={1,bogus}]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
  \\
  \tn[legs at=bogus]{X}\tnspan[box]{1}{\tenkzTestBadSpanInk} & & &
\end{tenkz}
\typeout{TENKZ-SPAN-SYNTAX-RECOVERED}
\end{document}
"""


def compile_tex(
    engine: str, work: Path, name: str, source: str,
    env: dict[str, str], *, halt_on_error: bool = True,
) -> subprocess.CompletedProcess[str]:
    tex = work / f"{name}.tex"
    tex.write_text(source, encoding="utf-8")
    command = [engine, "-interaction=nonstopmode"]
    if halt_on_error:
        command.append("-halt-on-error")
    command.append(tex.name)
    return subprocess.run(
        command,
        cwd=work,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
    )


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1
    with tempfile.TemporaryDirectory(prefix="tenkz-enclosures-") as tmp:
        work = Path(tmp)
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get("TEXINPUTS", "")

        fixture = "enclosure-regression"
        run = compile_tex(engine, work, fixture, SOURCE, env)
        if run.returncode:
            print(run.stdout)
            raise AssertionError("valid enclosure fixture did not compile")

        audit = Audit(work / f"{fixture}.tnlog", work / f"{fixture}.tex")
        if audit.run() != 0:
            raise AssertionError("valid enclosure fixture failed structural audit")

        pictures = audit.pictures
        if len(pictures) != 5:
            summary = [
                (picture.ident, picture.lang,
                 [event.kind for event in picture.events])
                for picture in pictures
            ]
            raise AssertionError(f"expected 5 pictures, found {summary}")
        if canonical_hash(pictures[0]) != canonical_hash(pictures[1]):
            raise AssertionError("no-feature controls changed structural topology")

        spans = [event for event in audit.events() if event.kind == "span"]
        got_spans = {
            (event.attrs["row"], event.attrs["col"], event.attrs["length"],
             event.attrs["kind"])
            for event in spans
        }
        expected_spans = {
            ("1", "1", "1", "box"),
            ("1", "1", "3", "box"),
            ("2", "1", "1", "box"),
            ("2", "1", "2", "box"),
        }
        if not expected_spans <= got_spans or len(spans) != 5:
            raise AssertionError(f"unexpected span records: {got_spans}")

        empty_label = compile_tex(
            engine, work, "empty-box-label", EMPTY_BOX_LABEL_PROBE, env
        )
        if empty_label.returncode:
            print(empty_label.stdout)
            raise AssertionError("empty box span materialized label geometry")

        # Synthetic logs exercise the audit independently of TeX's own
        # fail-closed grammar, including forward references and cross-kind
        # duplicate names.
        audit_cases = {
            "malformed-event": """picture|id=1|lang=grid
atom|picture=1|cell=not-a-cell|kind=dot
""",
        }
        for rule, log_source in audit_cases.items():
            log_path = work / f"audit-{rule}.tnlog"
            log_path.write_text(log_source, encoding="utf-8")
            bad_audit = Audit(log_path, None)
            bad_audit.parse_log()
            bad_audit.check_dialects()
            if rule not in {finding.rule for finding in bad_audit.findings}:
                raise AssertionError(f"audit failed to report {rule}")

        wrapper = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
%s
\end{document}
"""
        for name, (body, diagnostic) in NEGATIVE.items():
            failed = compile_tex(engine, work, name, wrapper % body, env)
            if failed.returncode == 0:
                raise AssertionError(f"negative fixture {name!r} compiled")
            if diagnostic not in failed.stdout:
                print(failed.stdout)
                raise AssertionError(
                    f"negative fixture {name!r} missed diagnostic {diagnostic!r}"
                )

        span_syntax = compile_tex(
            engine, work, "span-syntax-recovery", SPAN_SYNTAX_RECOVERY,
            env, halt_on_error=False,
        )
        if span_syntax.returncode == 0:
            raise AssertionError("span syntax recovery compilation succeeded")
        if span_syntax.stdout.count("decimal integer syntax") != 2:
            print(span_syntax.stdout)
            raise AssertionError("span syntax recovery missed diagnostics")
        if "combined=sideways is not a fusion side" not in span_syntax.stdout:
            print(span_syntax.stdout)
            raise AssertionError("fusion-side recovery missed its diagnostic")
        if "TENKZ-SPAN-SYNTAX-RECOVERED" not in span_syntax.stdout:
            raise AssertionError("span syntax recovery missed its sentinel")
        if "TENKZ-BAD-SPAN-SYNTAX-INK" in span_syntax.stdout:
            raise AssertionError("invalid span syntax rendered label ink")
        if "TENKZ-GOOD-SPAN-SYNTAX-INK" not in span_syntax.stdout:
            raise AssertionError("valid canonical span missed label ink")
        syntax_events = (work / "span-syntax-recovery.tnlog").read_text(
            encoding="utf-8"
        ).splitlines()
        syntax_spans = [
            line for line in syntax_events if line.startswith("span|")
        ]
        invalid_fuse_bonds = [
            line for line in syntax_events
            if line.startswith("bond|")
            and ("|row=8|" in line or "|row=9|" in line)
        ]
        if invalid_fuse_bonds:
            raise AssertionError(
                "invalid fusion syntax entered the frozen topology: "
                f"{invalid_fuse_bonds!r}"
            )
        if len(syntax_spans) != 2 or not any(
            "|row=1|col=3|length=2|" in line for line in syntax_spans
        ) or not any(
            "|row=2|col=2|length=1|" in line for line in syntax_spans
        ) or any(
            "|row=2|col=1|" in line for line in syntax_spans
        ):
            raise AssertionError(
                f"span lengths were not rejected/canonicalized: {syntax_spans!r}"
            )

        # Shared enclosure resolution is a transaction boundary for
        # measured box spans.  Under nonstop recovery an empty grid span
        # must leave neither a registry entry nor a semantic event, while
        # later valid controls in the same picture still commit normally.
        enclosure_recovered = compile_tex(
            engine, work, "enclosure-recovery", ENCLOSURE_RECOVERY,
            env, halt_on_error=False,
        )
        if enclosure_recovered.returncode == 0:
            raise AssertionError("enclosure recovery compilation succeeded")
        for diagnostic in (
            "An enclosure needs at least one rendered member",
            "Choice 'around' unknown",
            "/tenkz/span/shade",
            "passed 'blue'",
        ):
            if diagnostic not in enclosure_recovered.stdout:
                print(enclosure_recovered.stdout)
                raise AssertionError(
                    f"enclosure recovery missed diagnostic {diagnostic!r}"
                )
        for marker in (
            "TENKZ-EMPTY-SPAN-RECOVERED",
        ):
            if marker not in enclosure_recovered.stdout:
                print(enclosure_recovered.stdout)
                raise AssertionError(
                    f"enclosure fixture did not reach marker {marker!r}"
                )
        for marker in (
            "TENKZ-BAD-CHOICE-INK",
            "TENKZ-BAD-KEY-INK",
        ):
            if marker in enclosure_recovered.stdout:
                raise AssertionError(
                    f"invalid deferred span rendered label marker {marker!r}"
                )
        if "TENKZ-GOOD-OPTION-SPAN-INK" not in enclosure_recovered.stdout:
            raise AssertionError("valid deferred span did not render its label")
        enclosure_log = work / "enclosure-recovery.tnlog"
        enclosure_events = enclosure_log.read_text(
            encoding="utf-8"
        ).splitlines()
        span_events = [
            line for line in enclosure_events if line.startswith("span|")
        ]
        for column in ("1", "3", "4"):
            if any(f"|col={column}|" in line for line in span_events):
                raise AssertionError(
                    f"invalid span in column {column} emitted a semantic event"
                )
        if sum("|col=2|" in line for line in span_events) != 1:
            raise AssertionError(
                f"valid box-span control emitted {span_events!r}"
            )
        if sum("|col=5|" in line for line in span_events) != 1:
            raise AssertionError(
                f"valid option-span control emitted {span_events!r}"
            )

    print("PASS: measured enclosure grammar, records, and failures are stable")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
