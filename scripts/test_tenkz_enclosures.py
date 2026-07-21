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

% The lattice body remains a live execute-once customization layer after the
% public region command moves to dialect dispatch.
\begin{tenkzlattice}[rows=2, cols=3, physical=up]
  \tikzset{region selected/.append style={rounded corners=1pt}}
  \pgfkeysifdefined{/tenkz/region/label/.@cmd}{}{%
    \errmessage{legacy lattice region family missing}}
  \tnregion[slot=selected, label={$Q$}]{(1-2,2-3)}
\end{tenkzlattice}

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
  \tnregion[group, name=inner,
    label={\rule{0pt}{12mm}$L$}, label pos=north]{left,right}
  \tenkzTestTallRegion{inner}
  \tnregion[slot=secondary, outline]{inner}
\end{tenkzfree}
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
}


def compile_tex(engine: str, work: Path, name: str, source: str,
                env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    tex = work / f"{name}.tex"
    tex.write_text(source, encoding="utf-8")
    return subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
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
        if len(pictures) != 7:
            summary = [
                (picture.ident, picture.lang,
                 [event.kind for event in picture.events])
                for picture in pictures
            ]
            raise AssertionError(f"expected 7 pictures, found {summary}")
        if canonical_hash(pictures[0]) != canonical_hash(pictures[1]):
            raise AssertionError("no-feature controls changed structural topology")

        spans = [event for event in audit.events() if event.kind == "span"]
        got_spans = {
            (event.attrs["row"], event.attrs["col"], event.attrs["length"],
             event.attrs["kind"])
            for event in spans
        }
        expected_spans = {
            ("1", "1", "3", "box"),
            ("2", "1", "2", "box"),
        }
        if not expected_spans <= got_spans or len(spans) != 3:
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
            ("group", "left,right"),
            ("secondary", "inner"),
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

        # Synthetic logs exercise the audit independently of TeX's own
        # fail-closed grammar, including forward references and cross-kind
        # duplicate names.
        audit_cases = {
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

    print("PASS: measured enclosure grammar, records, and failures are stable")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
