#!/usr/bin/env python3
"""Regression checks for measured grid and lattice enclosures."""

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
\makeatletter
\newcount\tenkzTestLatticeBodyRuns
\makeatother
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

% A three-sheet lattice body remains a live execute-once customization layer
% after the public region command moves to dialect dispatch.  The global count
% detects both a skipped body and an accidental once-per-sheet replay.
\begin{tenkzlattice}[
    rows=2, cols=3, sheets={ket,op,bra}, physical=up]
  \global\advance\tenkzTestLatticeBodyRuns by 1\relax
  \tikzset{region selected/.append style={rounded corners=0pt}}
  \pgfkeysifdefined{/tenkz/region/label/.@cmd}{}{%
    \errmessage{legacy lattice region family missing}}
  \tnregion[slot=selected, label={$Q$}]{(1-2,2-3)}
  \tnedge[role=marked]{(1,1,1)-(1,2,1)}
\end{tenkzlattice}
\ifnum\tenkzTestLatticeBodyRuns=1\relax\else
  \errmessage{three-sheet lattice body did not execute exactly once}
\fi

\end{document}
"""

LATTICE_STYLE_PROBE = r"""
\documentclass[tikz,border=2pt]{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkzlattice}[rows=2, cols=3, physical=up]
%s
  \tnregion[slot=selected]{(1-2,2-3)}
\end{tenkzlattice}
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
    "duplicate-lattice-name": (r"""
\begin{tenkzlattice}[rows=2, cols=2]
  \tnregion[name=R]{(1,1)}
  \tnregion[name=R]{(2,2)}
\end{tenkzlattice}
""", "already defined in this"),
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


DUPLICATE_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\newcommand*{\tenkzTestDuplicateLatticeInk}{%
  \typeout{TENKZ-DUPLICATE-LATTICE-INK}bad}
\newcommand*{\tenkzTestBadLatticeSlotInk}{%
  \typeout{TENKZ-BAD-LATTICE-SLOT-INK}bad}
\newcommand*{\tenkzTestBadLatticeSetInk}{%
  \typeout{TENKZ-BAD-LATTICE-SET-INK}bad}
\newcommand*{\tenkzTestRejectedInk}{%
  \typeout{TENKZ-REJECTED-DECLARATION-INK}bad}
\newcommand*{\tenkzTestValidLatticeInk}{%
  \typeout{TENKZ-VALID-LATTICE-INK}good}
\newcommand*{\tenkzTestValidNorthLabel}{%
  \typeout{TENKZ-VALID-NORTH-LABEL}north}
\makeatletter
\ExplSyntaxOn
\cs_new_protected:Npn \tenkzTestLatticeRegistry
  {
    \prop_if_in:NnT \l_tenkz_cs_names_prop {BadSlot}
      { \typeout{TENKZ-TEST-BAD-LATTICE-SLOT-REGISTERED} }
    \prop_if_in:NnT \l_tenkz_cs_names_prop {BadSet}
      { \typeout{TENKZ-TEST-BAD-LATTICE-SET-REGISTERED} }
    \prop_if_in:NnT \l_tenkz_cs_names_prop {BadKey}
      { \typeout{TENKZ-TEST-BAD-LATTICE-KEY-REGISTERED} }
    \prop_if_in:NnT \l_tenkz_cs_names_prop {BadEmpty}
      { \typeout{TENKZ-TEST-BAD-LATTICE-EMPTY-REGISTERED} }
  }
\ExplSyntaxOff
\makeatother
\begin{document}
\begin{tenkzlattice}[rows=2, cols=2]
  \tnregion[name=R]{(1,1)}
  \tnregion[name=R, label={\tenkzTestDuplicateLatticeInk}]
    {(2,2)}
  \tnregion[slot=secondary]{R}
  \tnregion[slot=bogus, name=BadSlot,
    label={\tenkzTestBadLatticeSlotInk}]{(2,1)}
  \tnregion[name=BadSet, label={\tenkzTestBadLatticeSetInk}]{missing}
  \tnregion[mystery=1, name=BadKey, label={\tenkzTestRejectedInk}]{(2,1)}
  \tnregion[name=BadEmpty, label={\tenkzTestRejectedInk}]{}
  \tenkzTestLatticeRegistry
  \tnregion[name=S, label={\tenkzTestValidLatticeInk}]
    {(1,2)}
  \tnregion[slot=collar]{S}
  \tnregion[label pos=north, label={\tenkzTestValidNorthLabel}]{S}
\end{tenkzlattice}
\typeout{TENKZ-DUPLICATE-RECOVERED}
\end{document}
"""

REGION_ROLE_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\newcommand*{\tenkzTestRejectedRegionRoleLabel}{%
  \typeout{TENKZ-REJECTED-REGION-ROLE-LABEL}$R$}
\newcommand*{\tenkzTestValidRegionAfterRole}{%
  \typeout{TENKZ-VALID-REGION-AFTER-ROLE}$S$}
\begin{document}
\begin{tenkzlattice}[
    rows=2, cols=2, frame=oblique, physical=up,
    boundary=none, outer legs=none]
  \tnregion[label={\tenkzTestRejectedRegionRoleLabel}, role=marked]{(1,1)}
  \tnregion[name=S, label={\tenkzTestValidRegionAfterRole}]{(2,2)}
\end{tenkzlattice}
\typeout{TENKZ-REGION-ROLE-RECOVERED}
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
    converter = shutil.which("pdftocairo")
    if converter is None:
        print("FAIL: pdftocairo is required")
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
        if len(pictures) != 6:
            summary = [
                (picture.ident, picture.lang,
                 [event.kind for event in picture.events])
                for picture in pictures
            ]
            raise AssertionError(f"expected 8 pictures, found {summary}")
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

        lattice_regions = [
            event for event in audit.events()
            if event.kind == "region" and "cells" in event.attrs
        ]
        if any(event.attrs.get("lang") != "lattice" for event in lattice_regions):
            raise AssertionError("lattice region events lost their dialect tag")
        if len(lattice_regions) != 1 or lattice_regions[0].attrs["cells"] != (
            "1-2,1-3,2-2,2-3"
        ):
            raise AssertionError("lattice public-region dispatch is incomplete")
        lattice_edges = [
            event for event in audit.events() if event.kind == "edge"
        ]
        if len(lattice_edges) != 1 or {
            key: lattice_edges[0].attrs.get(key)
            for key in ("from", "to", "role")
        } != {"from": "1-1-1", "to": "1-2-1", "role": "marked"}:
            raise AssertionError(
                f"three-sheet body edge did not survive exactly once: {lattice_edges}"
            )
        generated_lattices = [
            event for event in audit.events() if event.kind == "lattice"
        ]
        if len(generated_lattices) != 1 or generated_lattices[0].attrs.get(
            "sheets"
        ) != "3":
            raise AssertionError(
                "body customization did not coexist with generated lattice ink"
            )

        # A non-empty lattice body is a live style-extension layer, not only
        # a command-recording buffer.  Raster comparison observes the final
        # path after every draw option has been applied, so a later hardcoded
        # corner radius cannot silently erase the customization.
        style_sources = {
            "lattice-default": "",
            "lattice-sharp": (
                r"\tikzset{region selected/.append style={rounded corners=0pt}}"
            ),
        }
        rasters: dict[str, bytes] = {}
        for name, body in style_sources.items():
            style_run = compile_tex(
                engine, work, name, LATTICE_STYLE_PROBE % body, env
            )
            if style_run.returncode:
                print(style_run.stdout)
                raise AssertionError(f"lattice style probe {name!r} did not compile")
            raster_run = subprocess.run(
                [converter, "-png", "-r", "300", "-singlefile",
                 f"{name}.pdf", name],
                cwd=work,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
            if raster_run.returncode:
                print(raster_run.stdout)
                raise AssertionError(f"lattice style probe {name!r} did not render")
            rasters[name] = (work / f"{name}.png").read_bytes()
        if rasters["lattice-default"] == rasters["lattice-sharp"]:
            raise AssertionError("lattice body style extension changed no final ink")

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
            "malformed-event": """picture|id=1|lang=lattice
site|picture=1|cell=not-a-cell|mode=removed
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

        # `role=` describes sites and edges, whereas a region is classified
        # by `slot=`.  The exact option combination from #4930 must stop at
        # that grammatical distinction, before label-anchor geometry runs.
        role_recovered = compile_tex(
            engine, work, "region-role-recovery", REGION_ROLE_RECOVERY,
            env, halt_on_error=False,
        )
        if role_recovered.returncode == 0:
            raise AssertionError("region-role recovery compilation succeeded")
        if "A lattice region has no 'role' key" not in role_recovered.stdout:
            print(role_recovered.stdout)
            raise AssertionError("region-role recovery missed its diagnostic")
        for opaque_error in (
            "Missing $ inserted",
            "No shape named",
            "no shape known",
        ):
            if opaque_error in role_recovered.stdout:
                print(role_recovered.stdout)
                raise AssertionError(
                    f"region-role recovery reached {opaque_error!r}"
                )
        for marker in (
            "TENKZ-VALID-REGION-AFTER-ROLE",
            "TENKZ-REGION-ROLE-RECOVERED",
        ):
            if marker not in role_recovered.stdout:
                print(role_recovered.stdout)
                raise AssertionError(
                    f"region-role recovery missed {marker!r}"
                )
        if "TENKZ-REJECTED-REGION-ROLE-LABEL" in role_recovered.stdout:
            raise AssertionError("rejected region-role label reached drawing")
        role_events = (work / "region-role-recovery.tnlog").read_text(
            encoding="utf-8"
        ).splitlines()
        role_regions = [
            line for line in role_events if line.startswith("region|")
        ]
        if len(role_regions) != 1 or "|cells=2-2" not in role_regions[0]:
            raise AssertionError(
                f"invalid region role emitted events {role_regions!r}"
            )

        # A duplicate semantic name is a rejected transaction, not merely a
        # diagnostic.  In nonstop mode it must not draw the second atom/join,
        # emit a second event, mutate the first declaration's registries, or
        # append a lattice region to the deferred render pass.  Later valid
        # declarations in each dialect must still commit.
        duplicate_recovered = compile_tex(
            engine, work, "duplicate-recovery", DUPLICATE_RECOVERY,
            env, halt_on_error=False,
        )
        if duplicate_recovered.returncode == 0:
            raise AssertionError("duplicate recovery compilation succeeded")
        if "Invalid end-point for range" in duplicate_recovered.stdout:
            print(duplicate_recovered.stdout)
            raise AssertionError("endpoint grammar emitted a regex warning")
        if duplicate_recovered.stdout.count("already defined in this") < 1:
            print(duplicate_recovered.stdout)
            raise AssertionError("duplicate recovery missed a diagnostic")
        if "TENKZ-DUPLICATE-RECOVERED" not in duplicate_recovered.stdout:
            print(duplicate_recovered.stdout)
            raise AssertionError("duplicate recovery did not reach its sentinel")
        for marker in (
            "TENKZ-DUPLICATE-LATTICE-INK",
            "TENKZ-BAD-LATTICE-SLOT-INK",
            "TENKZ-BAD-LATTICE-SET-INK",
            "TENKZ-REJECTED-DECLARATION-INK",
            "TENKZ-TEST-BAD-LATTICE-SLOT-REGISTERED",
            "TENKZ-TEST-BAD-LATTICE-SET-REGISTERED",
            "TENKZ-TEST-BAD-LATTICE-KEY-REGISTERED",
            "TENKZ-TEST-BAD-LATTICE-EMPTY-REGISTERED",
        ):
            if marker in duplicate_recovered.stdout:
                raise AssertionError(
                    f"duplicate declaration leaked side effect {marker!r}"
                )
        for marker in (
            "TENKZ-VALID-LATTICE-INK",
            "TENKZ-VALID-NORTH-LABEL",
        ):
            if marker not in duplicate_recovered.stdout:
                raise AssertionError(
                    f"valid control missed render marker {marker!r}"
                )
        duplicate_events = (work / "duplicate-recovery.tnlog").read_text(
            encoding="utf-8"
        ).splitlines()
        lattice_regions = [
            line for line in duplicate_events
            if line.startswith("region|")
        ]
        if sum("|cells=1-1" in line for line in lattice_regions) != 2:
            raise AssertionError(
                "first lattice name was not preserved through duplicate: "
                f"{lattice_regions!r}"
            )
        if any("|cells=2-2" in line for line in lattice_regions):
            raise AssertionError(
                f"duplicate lattice region emitted {lattice_regions!r}"
            )
        if sum("|cells=1-2" in line for line in lattice_regions) != 3:
            raise AssertionError(
                f"valid lattice controls emitted {lattice_regions!r}"
            )
        if len(lattice_regions) != 5:
            raise AssertionError(
                f"invalid lattice declaration entered events {lattice_regions!r}"
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
