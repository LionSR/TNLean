#!/usr/bin/env python3
"""Regression checks for measured grid and free-tier enclosures."""

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
\newif\iftenkzTestSecondaryMain
\newif\iftenkzTestSelectedMain
\newcount\tenkzTestLatticeBodyRuns
\def\tenkzTestSecondaryFillLayer{}
\def\tenkzTestSelectedFillLayer{}
\newcommand*{\tenkzTestSecondaryLayer}{%
  \ifx\pgfonlayer@name\pgf@maintext
    \global\tenkzTestSecondaryMaintrue
  \else
    \xdef\tenkzTestSecondaryFillLayer{\pgfonlayer@name}%
  \fi}
\newcommand*{\tenkzTestSelectedLayer}{%
  \ifx\pgfonlayer@name\pgf@maintext
    \global\tenkzTestSelectedMaintrue
  \else
    \xdef\tenkzTestSelectedFillLayer{\pgfonlayer@name}%
  \fi}
\ExplSyntaxOn
% A named region with a deliberately tall external label must register the
% composite outline+label box, not only its outline node.
\cs_new_protected:Npn \tenkzTestTallRegion #1
  {
    \prop_get:NeNTF \g__tenkz_enclosure_prop
      { \the\tenkz@pictureid / #1 } \l_tmpa_tl
      {
        \path let \p1=(\l_tmpa_tl.north), \p2=(\l_tmpa_tl.south) in
          \pgfextra
            {
              \dim_set:Nn \l_tmpa_dim { \y1 - \y2 }
              \dim_compare:nNnT { \l_tmpa_dim } < {10mm}
                { \tex_errmessage:D { named~region~omitted~label~geometry } }
            };
      }
      { \tex_errmessage:D { named~region~was~not~registered } }
  }
\ExplSyntaxOff
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
\end{tenkzlattice}
\ifnum\tenkzTestLatticeBodyRuns=1\relax\else
  \errmessage{three-sheet lattice body did not execute exactly once}
\fi

% Oblique named atoms and named joins, including external label ink.
\begin{tenkzfree}
  \tikzset{group region/.append style={rounded corners=0pt}}
  \tnput[box, ports={south:virtual}]{u0}{(0,1)}{U_0}
  \tnput[box, ports={south:virtual}]{u1}{(2.4,1.4)}{U_1}
  \tnput[dot, ports={west:virtual,east:virtual},
         label pos=south]{p}{(1.1,-0.2)}{\varphi}
  \tnjoin[name=j0, route=vh]{u0.south}{p.west}
  \tnjoin[name=j1, route=hv]{u1.south}{p.east}
  \tnregion[group, name=P, label={$P$}, label pos=south]{p}
  \tnregion[slot=selected, outline, label={$R$}, label pos=north]
    {u0,u1,j0,j1,P}
\end{tenkzfree}

% Unlabelled boundary atoms are zero-ink endpoints but remain valid measured
% members.  The tall label probe makes nested-label coverage mechanical.
\begin{tenkzfree}
  \tnput[boundary]{left}{(0,0)}{}
  \tnput[boundary]{right}{(2,0)}{}
  \tikzset{
    region secondary/.append style={
      execute at begin node=\tenkzTestSecondaryLayer},
    region selected/.append style={
      execute at begin node=\tenkzTestSelectedLayer}}
  \tnregion[slot=secondary, name=inner,
    label={\rule{0pt}{12mm}$L$}, label pos=north]{left,right}
  \tenkzTestTallRegion{inner}
  \tnregion[slot=selected]{inner}
  \iftenkzTestSecondaryMain\else
    \errmessage{inner region outline was not drawn above region fills}
  \fi
  \iftenkzTestSelectedMain\else
    \errmessage{outer region outline was not drawn on the main layer}
  \fi
  \def\tenkzTestInnerLayer{tenkz-enclosure-fill-0}
  \def\tenkzTestOuterLayer{tenkz-enclosure-fill-1}
  \ifx\tenkzTestSecondaryFillLayer\tenkzTestInnerLayer\else
    \errmessage{inner region fill was not drawn at nesting depth zero}
  \fi
  \ifx\tenkzTestSelectedFillLayer\tenkzTestOuterLayer\else
    \errmessage{outer region fill was not drawn behind the inner fill}
  \fi
\end{tenkzfree}
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
    "unknown-member": (r"""
\begin{tenkzfree}
  \tnput[box]{a}{(0,0)}{A}
  \tnregion{missing}
\end{tenkzfree}
""", "Unknown enclosure member"),
    "duplicate-name": (r"""
\begin{tenkzfree}
  \tnput[box, ports={east:virtual}]{a}{(0,0)}{A}
  \tnput[box, ports={west:virtual}]{b}{(1,0)}{B}
  \tnjoin[name=a]{a.east}{b.west}
\end{tenkzfree}
""", "already defined in this"),
    "duplicate-lattice-name": (r"""
\begin{tenkzlattice}[rows=2, cols=2]
  \tnregion[name=R]{(1,1)}
  \tnregion[name=R]{(2,2)}
\end{tenkzlattice}
""", "already defined in this"),
    "unknown-named-join-route": (r"""
\begin{tenkzfree}
  \tnput[box, ports={east:virtual}]{a}{(0,0)}{A}
  \tnput[box, ports={west:virtual}]{b}{(1,0)}{B}
  \tnjoin[name=bad, route=sideways]{a.east}{b.west}
\end{tenkzfree}
""", "Unknown route 'sideways'"),
}


UNKNOWN_ROUTE_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\begin{tenkzfree}
  \tnput[box, ports={east:virtual}]{a}{(0,0)}{A}
  \tnput[box, ports={west:virtual}]{b}{(1,0)}{B}
  \tnjoin[name=bad, route=sideways]{a.east}{b.west}
  \tnjoin[name=good]{a.east}{b.west}
  \ExplSyntaxOn
  \tenkz_enclosure_if_registered:nT {bad}
    { \typeout{TENKZ-BAD-ROUTE-REGISTERED} }
  \tenkz_enclosure_if_registered:nF {good}
    { \typeout{TENKZ-GOOD-ROUTE-MISSING} }
  \ExplSyntaxOff
  \typeout{TENKZ-UNKNOWN-ROUTE-RECOVERED}
\end{tenkzfree}
\end{document}
"""


ENCLOSURE_RECOVERY = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\begin{tenkzfree}
  \tnput[box]{a}{(0,0)}{A}
  \tnregion[name=bad]{missing}
  \tnregion[name=good]{a}
  \ExplSyntaxOn
  \tenkz_enclosure_if_registered:nT {bad}
    { \typeout{TENKZ-BAD-REGION-REGISTERED} }
  \tenkz_enclosure_if_registered:nF {good}
    { \typeout{TENKZ-GOOD-REGION-MISSING} }
  \ExplSyntaxOff
  \typeout{TENKZ-UNKNOWN-MEMBER-RECOVERED}
\end{tenkzfree}
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
        if len(pictures) != 8:
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

        joins = [event for event in audit.events() if event.kind == "join"]
        if {event.attrs.get("name") for event in joins} != {"j0", "j1"}:
            raise AssertionError("named join records are incomplete")
        regions = [
            event for event in audit.events()
            if event.kind == "region" and "members" in event.attrs
        ]
        if {(event.attrs["slot"], event.attrs["members"]) for event in regions} != {
            ("group", "p"),
            ("selected", "u0,u1,j0,j1,P"),
            ("secondary", "left,right"),
            ("selected", "inner"),
        }:
            raise AssertionError("free-region records are incomplete")
        if {event.attrs.get("name") for event in regions} != {None, "P", "inner"}:
            raise AssertionError("free-region names are missing from the log")
        lattice_regions = [
            event for event in audit.events()
            if event.kind == "region" and "cells" in event.attrs
        ]
        if len(lattice_regions) != 1 or lattice_regions[0].attrs["cells"] != (
            "1-2,1-3,2-2,2-3"
        ):
            raise AssertionError("lattice public-region dispatch is incomplete")

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

        # Synthetic logs exercise the audit independently of TeX's own
        # fail-closed grammar, including forward references and cross-kind
        # duplicate names.
        audit_cases = {
            "malformed-event": """picture|id=1|lang=lattice
site|picture=1|cell=not-a-cell|mode=removed
""",
            "unknown-region-member": """picture|id=1|lang=free
region|picture=1|lang=free|slot=selected|members=later|outline=0
""",
            "duplicate-enclosure-name": """picture|id=1|lang=free
atom|picture=1|name=a|kind=box
region|picture=1|lang=free|slot=selected|members=a|outline=0|name=a
""",
        }
        for rule, log_source in audit_cases.items():
            log_path = work / f"audit-{rule}.tnlog"
            log_path.write_text(log_source, encoding="utf-8")
            bad_audit = Audit(log_path, None)
            bad_audit.parse_log()
            bad_audit.check_dialects()
            bad_audit.check_free_region_names()
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

        # TeX's nonstop recovery returns after \PackageError.  The invalid
        # named join must still fail closed: no enclosure registry entry and
        # no semantic join event may survive the diagnostic.
        recovered = compile_tex(
            engine, work, "unknown-route-recovery", UNKNOWN_ROUTE_RECOVERY,
            env, halt_on_error=False,
        )
        if recovered.returncode == 0:
            raise AssertionError("unknown route recovery compilation succeeded")
        if "Unknown route 'sideways'" not in recovered.stdout:
            print(recovered.stdout)
            raise AssertionError("unknown route recovery missed its diagnostic")
        if "TENKZ-UNKNOWN-ROUTE-RECOVERED" not in recovered.stdout:
            print(recovered.stdout)
            raise AssertionError("unknown route fixture did not exercise recovery")
        if "TENKZ-BAD-ROUTE-REGISTERED" in recovered.stdout:
            raise AssertionError("unknown route registered a named enclosure")
        if "TENKZ-GOOD-ROUTE-MISSING" in recovered.stdout:
            raise AssertionError("valid recovery control missed its enclosure")
        recovery_log = work / "unknown-route-recovery.tnlog"
        recovery_joins = [
            line
            for line in recovery_log.read_text(encoding="utf-8").splitlines()
            if line.startswith("join|")
        ]
        if any("|name=bad" in line for line in recovery_joins):
            raise AssertionError("unknown route emitted a semantic join event")
        if sum("|name=good" in line for line in recovery_joins) != 1:
            raise AssertionError(
                f"valid recovery control emitted {recovery_joins!r}"
            )

        # Shared enclosure resolution is a transaction boundary for both
        # free regions and measured box spans.  Under nonstop recovery an
        # unknown free member and an empty grid span must leave neither a
        # registry entry nor a semantic event, while later valid controls
        # in the same pictures still commit normally.
        enclosure_recovered = compile_tex(
            engine, work, "enclosure-recovery", ENCLOSURE_RECOVERY,
            env, halt_on_error=False,
        )
        if enclosure_recovered.returncode == 0:
            raise AssertionError("enclosure recovery compilation succeeded")
        for diagnostic in (
            "Unknown enclosure member 'missing'",
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
            "TENKZ-UNKNOWN-MEMBER-RECOVERED",
            "TENKZ-EMPTY-SPAN-RECOVERED",
        ):
            if marker not in enclosure_recovered.stdout:
                print(enclosure_recovered.stdout)
                raise AssertionError(
                    f"enclosure fixture did not reach marker {marker!r}"
                )
        if "TENKZ-BAD-REGION-REGISTERED" in enclosure_recovered.stdout:
            raise AssertionError("invalid free region entered the registry")
        if "TENKZ-GOOD-REGION-MISSING" in enclosure_recovered.stdout:
            raise AssertionError("valid free region missed the registry")
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
        region_events = [
            line for line in enclosure_events if line.startswith("region|")
        ]
        if any("|name=bad" in line for line in region_events):
            raise AssertionError("invalid free region emitted a semantic event")
        if sum("|name=good" in line for line in region_events) != 1:
            raise AssertionError(
                f"valid free-region control emitted {region_events!r}"
            )
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
