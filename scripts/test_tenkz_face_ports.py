#!/usr/bin/env python3
"""Regression checks for asymmetric tenkz face ports.

The test compiles small pictures and reads their `.tnlog` contraction
records.  It guards the two failures from issue 4249: inventing a second open
port on the centred face, and dropping the second contraction on the declared
two-port face.  It also fixes the compatibility meaning of `legs at=`, the
virtual arity of default and sparse splitting endpoints, and exact-slot
resolution for ordinary tall glyphs and physical contractions.
"""

from __future__ import annotations

import io
import os
import shutil
import subprocess
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

from tenkz_audit import Audit, Event, canonical_hash


ROOT = Path(__file__).resolve().parents[1]

SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\newcommand{\lowerlabelprobe}{\typeout{TENKZ-LOWER-MATCH-LABEL}j}
\newcount\tenkzmatchedlabelseen
\newcount\tenkzsurpluslabelseen
\newcount\tenkzplainlabelseen
\newcount\tenkzcenterlabelseen
\newcount\tenkzperiodicbondseen
\newcount\tenkzinteriorbondseen
\makeatletter
\ExplSyntaxOn
\bool_new:N \g__tenkz_test_none_face_label_bool
\cs_new_protected:Npn \tenkzNoneFaceLabelProbe
  { \bool_gset_true:N \g__tenkz_test_none_face_label_bool }
\cs_new_protected:Npn \tenkzNoneFaceLabelAssert
  {
    \bool_if:NT \g__tenkz_test_none_face_label_bool
      { \tex_errmessage:D { none~face~dropped~external~label~clearance } }
  }
\cs_new_eq:NN \__tenkz_test_sil_band: \tenkz_sil_band:
\cs_set_protected:Npn \tenkz_sil_band:
  {
    \bool_if:NT \g__tenkz_test_none_face_label_bool
      { \bool_gset_false:N \g__tenkz_test_none_face_label_bool }
    \__tenkz_test_sil_band:
  }
\ExplSyntaxOff
\makeatother
\begin{document}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at=center, down at={1,2}]{U^\dagger} & \\
  \tn{A} & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at={1,2}, down at=center]{U} & \\
  \tn[wide=2]{A} &
\end{tenkz}
\begin{tenkz}[physical=up, tensor style=box]
  \tn[pill, wide=2, legs at={1,2}]{U} &
\end{tenkz}
\begin{tenkz}[rows={ket:fused:nopair, wire:west none}]
  \tn[box]{B} & \tndots & \tn[box]{B} &
  \tnfuse[span=2, west at=center, east at={1,2}]{V}\\
  & & &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=3, up at=center, down at={1,2,3}]{W} & & \\
  \tn{A} & \tn{A} & \tn{A}
\end{tenkz}
\begin{tenkz}[physical=up, tensor style=box]
  \tn[pill, wide=2, legs at={1,2}, up at=center]{U} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}]
  \tnfuse[span=2]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V}\\
  &\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V} & \tn{A}\\
  & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, west at=center, east at={1,2}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, west at=center, east at={1,2}]{X} & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at=center, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at={1}, down at=center]{L} &
\end{tenkz}
\begin{tenkz}[physical=updown, trace=physical, tensor style=box]
  \tn[pill, wide=2, up at={1,2}, down at=center]{T} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnfuse[span=2, combined=west, west at={1,2}]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, physical=updown, up at=center, down at={1,2}]{B}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[down at={1}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, down at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, physical=up]{B}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, east at=center]{X} & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V} & & \tn{A}\\
  & & \tn{A}\\
  & & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{K} & \\
  \tn[pill, wide=2, up at={1,2}]{B} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1}, down={$i$}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, up={$j$,$k$}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[down at=center, down={$i$}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, up={$j$,$k$}]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire}, tensor style=box]
  \tn[west at=center, east at=center]{X}
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(physical,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{K} & \\
  \tn[pill, wide=2, up at={1,2}]{B} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,2)}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at={1}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tnskip & \tn{L}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={2}]{U} & \\
  \tnskip & \tn{L}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tnskip & \tn{U}\\
  \tn[pill, wide=2, up at={1,2}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  & \tnfuse[span=2, west at=center, east at={1,2}]{V}\\
  \tn{A} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnX[wires=2, west at=center, east at=center]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnfuse[span=2, west at={1,2}, east at=center]{V} & & \tn{A}\\
  & & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, west at={1,2}, east at={3}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={ket, wire}, tensor style=box]
  \tn[no legs, up at=center, down at=center]{A}\\
  \tnX[up at=center, down at=center]{X}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, west at={1,1}, east at={2,2}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, physical=up, no legs]{B}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, west at={2,1}, east at={2,1}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1),(1,2)}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1),(1,2)}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at={1,2}]{L} &
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(physical,1)}, tensor style=box]
  \tn[no legs]{K}\\
  \tn{B}
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(physical,1)}, tensor style=box]
  \tn{K}\\
  \tn[no legs]{B}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tn{L_1} & \tn{L_2}
\end{tenkz}
\begin{tenkz}[rows={wire}, tensor style=box]
  \tn[up at=center, down at=center]{A}
\end{tenkz}
\begin{tenkz}[rows={op}, tensor style=box]
  \tn[pill, wide=2, up at={1,1,3}, down at={2,2,0}]{A} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic, tensor style=box]
  \tn[wires=2, west at={1,2}, east at={1}]{A}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic, trace style=hooks, tensor style=box]
  \tn[wires=2, west at={1,2}, east at={1}]{A}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op}, tensor style=box]
  \tn[wide=2, up at={3}]{U} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, up={\lowerlabelprobe,$k$}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[no legs]{U}\\
  \tn[up at=center]{L}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic, tensor style=box]
  \tn[wires=2, west at=center, east at=center]{A}\\
  &
\end{tenkz}
\begingroup
\tikzset{tenkz combined stub/.append style={/utils/exec={%
  \global\advance\tenkzperiodicbondseen by 1\relax}}}
\begin{tenkz}[rows={wire, wire}, periodic, trace style=hooks, tensor style=box]
  \tn[wires=2, west at=center, east at=center]{A}\\
  &
\end{tenkz}
\endgroup
\ifnum\tenkzperiodicbondseen=0\else
  \errmessage{periodic hooks retained a separate centred-face stub}
\fi
\begin{tenkz}[rows={op, ket}, open={(1,2)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at={1}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1}]{U} & \\
  \tn[pill, wide=2, up at={1,2},
      up={\global\advance\tenkzmatchedlabelseen by 1\relax,
          \global\advance\tenkzsurpluslabelseen by 1\relax}]{L} &
\end{tenkz}
\ifnum\tenkzmatchedlabelseen=1\else
  \errmessage{matched opened lower label was not rendered exactly once}
\fi
\ifnum\tenkzsurpluslabelseen=1\else
  \errmessage{surplus lower label was not rendered exactly once}
\fi
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tnskip & \\
  \tn[pill, wide=2, no legs, up at={1,2}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[down at=center]{U} & \\
  \tn[pill, wide=2, up at={1,2},
      up={\global\advance\tenkzplainlabelseen by 1\relax,$k$}]{L} &
\end{tenkz}
\ifnum\tenkzplainlabelseen=1\else
  \errmessage{plain-to-wide opened lower label was not rendered exactly once}
\fi
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, no legs]{U} & \\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, tensor style=box]
  \tn[wires=2, combined=north]{A}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire}, tensor style=box]
  \tn[combined=west]{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, tensor style=box]
  \tn{A} & \tn[wires=2, west at=center]{X}\\
  \tn{A} &
\end{tenkz}
\begin{tenkz}[rows={wire}]
  \tn[label pos=bogus]{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic, tensor style=box]
  \tnfuse[span=2, west at=center, east at=center]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic, trace style=hooks, tensor style=box]
  \tnfuse[span=2, west at=center, east at=center]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1}]{U} & \\
  \tn[pill, wide=2, up at=center,
      up={\global\advance\tenkzcenterlabelseen by 1\relax}]{L} &
\end{tenkz}
\ifnum\tenkzcenterlabelseen=1\else
  \errmessage{wide-to-centered opened lower label was not rendered exactly once}
\fi
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={3}]{U} & \\
  \tn{L_1} & \tn{L_2}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={3}]{U} & \\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, no legs]{U} & \\
  \tn{L_1} & \tn{L_2}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  & \tn[pill, wide=2, no legs]{U} & \\
  \tn[pill, wide=2, up at=center]{L} & &
\end{tenkz}
\begin{tenkz}[physical=up, tensor style=box]
  \tn[pill, wide=2, up at=rows]{A} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  & \tn[pill, wide=2, down at={3}]{U} & \\
  \tn[pill, wide=2, up at=center]{L} & &
\end{tenkz}
\begin{tenkz}[rows={wire}, tensor style=box]
  \tn[west at={2}, east at=none]{A}
\end{tenkz}
\begingroup
\tikzset{tenkz combined stub/.append style={/utils/exec={%
  \global\advance\tenkzinteriorbondseen by 1\relax}}}
\begin{tenkz}[rows={wire, wire, wire}, periodic,
    trace style=hooks, tensor style=box]
  \tn{A}\\
  \tn[wires=2, west at=center, east at=center]{B}\\
  &
\end{tenkz}
\endgroup
\ifnum\tenkzinteriorbondseen=2\else
  \errmessage{periodic hooks suppressed an unconsumed interior centred face}
\fi
\begin{tenkz}[rows={wire, wire}, periodic,
    trace style=hooks, tensor style=box]
  \tn[wires=2, west at=center, east at=none]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic,
    trace style=racetrack, tensor style=box]
  \tn[wires=2, west at=center, east at=none]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic,
    trace style=hooks, tensor style=box]
  \tnfuse[span=2, west at=center, east at=none]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}, periodic,
    trace style=racetrack, tensor style=box]
  \tnfuse[span=2, west at=center, east at=none]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[wires=1, physical=down]{U}\\
  \tn{L}
\end{tenkz}
% An absent upper face suppresses only the leg.  Its north external bead
% label remains ink and must still reserve the ordinary label band.
\tenkzNoneFaceLabelProbe
\begin{tenkz}[physical=up]
  \tn[dot, up at=none, label pos=north]{A}\tnspan[brace above]{1}{probe}
\end{tenkz}
\tenkzNoneFaceLabelAssert
\end{document}
"""



def events_by_picture(audit: Audit) -> dict[int, list[Event]]:
    """Typed events per picture, read from the audit's own parse
    (`Audit.events`) instead of hand-splitting the `.tnlog` a second
    time; `require`/`forbid`/`paired_ports` below consume `Event.raw`/
    `.kind`/`.attrs` rather than re-parsing pipe-delimited fields."""
    return {pid: list(events) for pid, events in
            ((p, audit.events(p)) for p in audit.by_id)}


def require(events: list[Event], expected: str, message: str) -> None:
    if expected not in (e.raw for e in events):
        raise AssertionError(f"{message}: missing {expected!r}")


def forbid(events: list[Event], forbidden: str, message: str) -> None:
    if forbidden.endswith("|"):
        found = any(forbidden in event.raw for event in events)
    else:
        found = forbidden in (event.raw for event in events)
    if found:
        raise AssertionError(f"{message}: found {forbidden!r}")


def paired_ports(events: list[Event]) -> list[tuple[str, str]]:
    return sorted(
        (e.attrs["upper-port"], e.attrs["column"])
        for e in events if e.kind == "pairleg"
    )


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1
    with tempfile.TemporaryDirectory(prefix="tenkz_face_ports_") as tmp:
        work = Path(tmp)
        tex = work / "face-ports.tex"
        tex.write_text(SOURCE, encoding="utf-8")
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
            print("FAIL: face-port fixture did not compile")
            return 1
        # A cup is a contraction the picture asserts.  One row offers one end,
        # so no bend can be drawn, and a picture that drew nothing here would
        # deny the contraction without saying so.
        barren_cup = work / "barren-grid-cup.tex"
        barren_cup.write_text(
            r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[rows={ket}, east=cup]
  \tn{A}
\end{tenkz}
\end{document}
""",
            encoding="utf-8",
        )
        barren_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", barren_cup.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if barren_run.returncode == 0 or "east=cup bends no pair" not in (
            barren_run.stdout
        ):
            print(barren_run.stdout)
            print("FAIL: a grid cup that bends nothing passed in silence")
            return 1
        # The declared cup outranks the picture boundary: a sealed picture that
        # names a cup on one side draws that bend and seals the other side.
        sealed_cup = work / "sealed-grid-cup.tex"
        sealed_cup.write_text(
            r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[sandwich, boundary=none, east=cup]
  \tn{A}\\
  \tn*{A}
\end{tenkz}
\end{document}
""",
            encoding="utf-8",
        )
        sealed_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", sealed_cup.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if sealed_run.returncode:
            print(sealed_run.stdout)
            print("FAIL: a cup on a sealed picture did not compile")
            return 1
        sealed_events = (work / "sealed-grid-cup.tnlog").read_text(encoding="utf-8")
        if "cup|picture=1|side=east|top=1|bottom=2" not in sealed_events:
            print(sealed_events)
            print("FAIL: boundary=none swallowed the cup the picture declared")
            return 1
        audit = Audit(work / "face-ports.tnlog", None)
        audit.parse_log()
        audit.check_dialects()
        audit.check_pairleg_faceports()
        pictures = events_by_picture(audit)
        hooks_findings = [
            finding for finding in audit.findings if "hooks" in finding.msg
        ]
        pairleg_faceport_findings = [
            finding for finding in audit.findings
            if finding.rule == "pairleg-faceport-mismatch"
        ]
        dialect_findings = [
            finding for finding in audit.findings
            if finding.rule == "dialect-mismatch"
        ]
        topology_hashes = {
            picture.ident: canonical_hash(picture) for picture in audit.pictures
        }
        parsed_pictures = {picture.ident: picture for picture in audit.pictures}
        parsed_warnings = {
            picture.ident: [
                event.attrs.get("code", "")
                for event in picture.events
                if event.kind == "warning"
            ]
            for picture in audit.pictures
        }
        missing_picture_log = work / "missing-warning-picture.tnlog"
        missing_picture_log.write_text(
            "picture|id=1|lang=grid\nwarning|code=missing-owner\n",
            encoding="utf-8",
        )
        missing_picture_audit = Audit(missing_picture_log, None)
        missing_picture_audit.parse_log()
        missing_picture_guard = any(
            finding.rule == "malformed-event"
            and "lacks required picture=" in finding.msg
            for finding in missing_picture_audit.findings
        )
        pairleg_ports_log = work / "pairleg-upper-ports.tnlog"
        overlong_port = "9" * 5000
        pairleg_ports_log.write_text(
            "picture|id=1|lang=grid\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=0|column=1\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=-1|column=1\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=bogus|column=1\n"
            f"pairleg|picture=1|upper=1-1|lower=2-1|upper-port={overlong_port}|column=1\n",
            encoding="utf-8",
        )
        pairleg_ports_audit = Audit(pairleg_ports_log, None)
        pairleg_ports_audit.parse_log()
        malformed_upper_ports = [
            finding.msg
            for finding in pairleg_ports_audit.findings
            if finding.rule == "malformed-event" and "upper-port=" in finding.msg
        ]
        pairleg_faceports_log = work / "pairleg-faceports.tnlog"
        overlong_arity = "9" * 5000
        huge_arity = 1_000_000_000
        pairleg_faceports_log.write_text(
            "picture|id=1|lang=grid\n"
            "faceports|picture=1|cell=1-1|face=down|arity=1|at=center\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "pairleg|picture=1|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=2|lang=grid\n"
            "faceports|picture=2|cell=1-1|face=down|arity=2|at=1,2\n"
            "pairleg|picture=2|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "pairleg|picture=2|upper=1-1|lower=2-2|upper-port=2|column=2\n"
            "pairleg|picture=2|upper=1-1|lower=2-3|upper-port=3|column=3\n"
            "picture|id=3|lang=grid\n"
            "faceports|picture=3|cell=1-1|face=down|arity=2|at=1,3\n"
            "pairleg|picture=3|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "pairleg|picture=3|upper=1-1|lower=2-3|upper-port=3|column=3\n"
            "pairleg|picture=3|upper=1-1|lower=2-2|upper-port=2|column=2\n"
            "picture|id=4|lang=grid\n"
            "faceports|picture=4|cell=1-1|face=down|arity=0|at=none\n"
            "pairleg|picture=4|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "picture|id=5|lang=grid\n"
            "pairleg|picture=5|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "pairleg|picture=5|upper=1-2|lower=2-2|upper-port=2|column=2\n"
            "picture|id=6|lang=grid\n"
            "faceports|picture=6|cell=1-1|face=down|arity=3|at=rows\n"
            "pairleg|picture=6|upper=1-1|lower=2-3|upper-port=3|column=3\n"
            "pairleg|picture=6|upper=1-1|lower=2-4|upper-port=4|column=4\n"
            "picture|id=7|lang=grid\n"
            f"faceports|picture=7|cell=1-1|face=down|arity={overlong_arity}|at=rows\n"
            "pairleg|picture=7|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=8|lang=grid\n"
            f"faceports|picture=8|cell=1-1|face=down|arity={huge_arity}|at=rows\n"
            f"pairleg|picture=8|upper=1-1|lower=2-1|upper-port={huge_arity}|"
            "column=1\n"
            f"pairleg|picture=8|upper=1-1|lower=2-2|upper-port={huge_arity + 1}|"
            "column=2\n"
            "picture|id=9|lang=grid\n"
            "faceports|picture=9|cell=1-1|face=down|arity=1|at=1\n"
            "pairleg|picture=9|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "picture|id=10|lang=grid\n"
            "faceports|picture=10|cell=1-1|face=down|arity=1|at=rows\n"
            "pairleg|picture=10|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "pairleg|picture=10|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=11|lang=grid\n"
            "faceports|picture=11|cell=1-1|face=down|arity=1|at=1\n"
            "faceports|picture=11|cell=1-1|face=down|arity=1|at=2\n"
            "pairleg|picture=11|upper=1-1|lower=2-2|upper-port=2|column=2\n"
            "picture|id=12|lang=grid\n"
            "faceports|picture=12|cell=1-1|face=down|arity=1|at=1\n"
            "faceports|picture=12|cell=1-1|face=down|arity=1|at=1\n"
            "pairleg|picture=12|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=13|lang=grid\n"
            "faceports|picture=13|cell=1-1|face=down|arity=1|at=cetner\n"
            "pairleg|picture=13|upper=1-1|lower=2-1|upper-port=center|column=1\n"
            "picture|id=14|lang=grid\n"
            "faceports|picture=14|cell=1-1|face=down|arity=2|at=1;2\n"
            "pairleg|picture=14|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=15|lang=grid\n"
            "faceports|picture=15|cell=1-1|face=up|arity=1|at=1\n"
            "faceports|picture=15|cell=1-1|face=up|arity=1|at=2\n"
            "faceports|picture=15|cell=1-1|face=west|arity=1|at=center\n"
            "faceports|picture=15|cell=1-1|face=west|arity=0|at=none\n"
            "faceports|picture=15|cell=1-1|face=east|arity=1|at=1\n"
            "faceports|picture=15|cell=1-1|face=east|arity=1|at=2\n"
            "picture|id=16|lang=grid\n"
            "faceports|picture=16|cell=1-1|face=down|at=rows\n"
            "pairleg|picture=16|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=17|lang=grid\n"
            "faceports|picture=17|cell=1-1|face=down|arity=1\n"
            "pairleg|picture=17|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=18|lang=grid\n"
            "faceports|picture=18|cell=1-1|face=down|arity=-1|at=rows\n"
            "pairleg|picture=18|upper=1-1|lower=2-1|upper-port=1|column=1\n"
            "picture|id=19|lang=grid\n"
            "faceports|picture=19|cell=1-1|face=down|arity=1|at=1,2\n"
            "pairleg|picture=19|upper=1-1|lower=2-2|upper-port=2|column=2\n"
            "picture|id=20|lang=grid\n"
            "faceports|picture=20|cell=1-1|face=down|arity=0|at=center\n"
            "pairleg|picture=20|upper=1-1|lower=2-1|upper-port=center|column=1\n",
            encoding="utf-8",
        )
        pairleg_faceports_audit = Audit(pairleg_faceports_log, None)
        pairleg_faceports_audit.parse_log()
        pairleg_faceports_audit.check_pairleg_faceports()
        pairleg_faceport_mismatches = [
            finding for finding in pairleg_faceports_audit.findings
            if finding.rule == "pairleg-faceport-mismatch"
        ]
        conflicting_faceports = [
            finding for finding in pairleg_faceports_audit.findings
            if finding.rule == "conflicting-faceports"
        ]
        malformed_faceports_at = [
            finding.msg for finding in pairleg_faceports_audit.findings
            if finding.rule == "malformed-event"
            and "faceports cell=1-1 face=down has invalid at=" in finding.msg
        ]
        incomplete_faceports = [
            finding.msg for finding in pairleg_faceports_audit.findings
            if finding.rule == "malformed-event"
            and "faceports cell=1-1 face=down lacks required" in finding.msg
        ]
        inconsistent_faceport_arities = [
            finding.msg for finding in pairleg_faceports_audit.findings
            if finding.rule == "malformed-event"
            and "faceports cell=1-1 face=down declares arity=" in finding.msg
        ]
        malformed_rows_arities = [
            finding.msg
            for finding in pairleg_faceports_audit.findings
            if finding.rule == "malformed-event"
            and "faceports field arity=" in finding.msg
        ]
        warning_only_log = work / "warning-only.tnlog"
        warning_only_log.write_text(
            "picture|id=1|lang=grid\n"
            "warning|picture=1|code=deferred-feature\n"
            "boundary|picture=1|virtual-west=0|virtual-east=0|"
            "physical-up=0|physical-down=0\n",
            encoding="utf-8",
        )
        warning_only_audit = Audit(warning_only_log, None)
        with redirect_stdout(io.StringIO()):
            warning_only_status = warning_only_audit.run()

    if not missing_picture_guard:
        raise AssertionError("audit parser silently dropped a pictureless warning")
    if len(malformed_upper_ports) != 4 or not all(
        any(f"upper-port={value!r}" in msg for msg in malformed_upper_ports)
        for value in ("0", "-1", "bogus", overlong_port)
    ):
        raise AssertionError("audit accepted a non-contraction pairleg upper-port")
    expected_pairleg_mismatches = {
        (1, "upper-port='1'"),
        (2, "upper-port='3'"),
        (3, "upper-port='2'"),
        (4, "upper-port='center'"),
        (6, "upper-port='4'"),
        (8, f"upper-port='{huge_arity + 1}'"),
        (9, "upper-port='center'"),
        (10, "upper-port='1'"),
        (11, "upper-port='2'"),
    }
    actual_pairleg_mismatches = {
        (picture, port)
        for finding in pairleg_faceport_mismatches
        for picture, port in expected_pairleg_mismatches
        if f"picture {picture} " in finding.msg and port in finding.msg
    }
    if (len(pairleg_faceport_mismatches) != len(expected_pairleg_mismatches)
            or actual_pairleg_mismatches != expected_pairleg_mismatches):
        raise AssertionError(
            "pairleg face-port correlation missed a mismatch or rejected a declared/legacy slot"
        )
    expected_conflicts = {
        (11, "face=down"),
        (15, "face=up"),
        (15, "face=west"),
        (15, "face=east"),
    }
    actual_conflicts = {
        (picture, face)
        for finding in conflicting_faceports
        for picture, face in expected_conflicts
        if f"picture {picture} " in finding.msg and face in finding.msg
    }
    if (len(conflicting_faceports) != len(expected_conflicts)
            or actual_conflicts != expected_conflicts):
        raise AssertionError(
            "audit accepted a conflicting duplicate face declaration"
        )
    if len(malformed_faceports_at) != 2 or not all(
        any(f"invalid at={value!r}" in msg for msg in malformed_faceports_at)
        for value in ("cetner", "1;2")
    ):
        raise AssertionError(
            "audit silently skipped a malformed face declaration: "
            f"{malformed_faceports_at!r}"
        )
    if len(incomplete_faceports) != 2 or not all(
        any(required in msg for msg in incomplete_faceports)
        for required in ("required arity=", "required at=")
    ):
        raise AssertionError("audit silently skipped an incomplete face declaration")
    if len(inconsistent_faceport_arities) != 2 or not all(
        any(fragment in msg for msg in inconsistent_faceport_arities)
        for fragment in (
            "declares arity=1 but at='1,2' resolves to 2 port(s)",
            "declares arity=0 but at='center' resolves to 1 port(s)",
        )
    ):
        raise AssertionError("audit accepted an inconsistent face arity")
    if len(malformed_rows_arities) != 2 or not all(
        any(value in msg for msg in malformed_rows_arities)
        for value in (overlong_arity, "arity='-1'")
    ):
        raise AssertionError("audit accepted or crashed on an overlong rows arity")
    if warning_only_status != 1 or not any(
        finding.rule == "empty-picture" and finding.severity == "HARD"
        for finding in warning_only_audit.findings
    ):
        raise AssertionError("warning-only grid picture counted as mathematical content")
    if hooks_findings:
        raise AssertionError("audit rejected a grid hooks event")
    if pairleg_faceport_findings:
        raise AssertionError("audit rejected a rendered pairleg declared by its upper face")
    if dialect_findings:
        raise AssertionError(
            "audit rejected an emitted event in its declared dialect: "
            f"{[finding.msg for finding in dialect_findings]!r}"
        )
    inverse = pictures[1]
    require(
        inverse,
        "boundary|picture=1|virtual-west=1|virtual-east=1|physical-up=1|physical-down=0",
        "centred upper face acquired a spurious port",
    )
    if paired_ports(inverse) != [("1", "1"), ("2", "2")]:
        raise AssertionError("two-port lower face did not contract ports 1 and 2 distinctly")

    forward = pictures[2]
    if paired_ports(forward) != [("center", "1")]:
        raise AssertionError("centred lower face did not emit one contraction")

    legacy = pictures[3]
    require(legacy, "faceports|picture=3|cell=1-1|face=up|arity=2|at=1,2",
            "legacy upper-face arity changed")
    forbid(legacy, "faceports|picture=3|cell=1-1|face=down|arity=2|at=1,2",
           "legacy key emitted an inactive lower face")

    zipper = pictures[4]
    require(zipper, "faceports|picture=4|cell=1-4|face=west|arity=1|at=center",
            "zipper fused-face arity changed")
    require(zipper, "faceports|picture=4|cell=1-4|face=east|arity=2|at=1,2",
            "zipper split-face arity changed")
    require(
        zipper,
        "boundary|picture=4|virtual-west=1|virtual-east=2|physical-up=2|physical-down=0",
        "zipper boundary signature changed",
    )
    arity_three = pictures[5]
    require(arity_three,
            "faceports|picture=5|cell=1-1|face=down|arity=3|at=1,2,3",
            "three-port face arity changed")
    if paired_ports(arity_three) != [("1", "1"), ("2", "2"), ("3", "3")]:
        raise AssertionError("three-port face did not contract ports 1, 2, and 3 distinctly")
    override = pictures[6]
    require(override, "faceports|picture=6|cell=1-1|face=up|arity=1|at=center",
            "explicit face did not override legacy alias")
    forbid(override, "faceports|picture=6|cell=1-1|face=down|arity=2|at=1,2",
           "legacy alias emitted an inactive lower face")
    default_fuse = pictures[7]
    require(default_fuse, "faceports|picture=7|cell=1-1|face=west|arity=1|at=center",
            "bare fuse did not emit its centred face")
    require(default_fuse, "faceports|picture=7|cell=1-1|face=east|arity=2|at=rows",
            "bare fuse did not emit its separate span face")
    require(
        default_fuse,
        "boundary|picture=7|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "bare fuse boundary disagrees with its two face events",
    )
    sparse = pictures[8]
    require(sparse, "faceports|picture=8|cell=1-1|face=east|arity=2|at=1,3",
            "sparse face event lost its declared slots")
    require(
        sparse,
        "boundary|picture=8|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "sparse boundary did not count exactly its declared row slots",
    )
    sparse_pairing = pictures[9]
    require(sparse_pairing,
            "bond|picture=9|row=1|from=1|to=2|dir=none|role=none|species=none",
            "sparse face did not contract declared row slot 1")
    require(sparse_pairing,
            "bond|picture=9|row=3|from=1|to=2|dir=none|role=none|species=none",
            "sparse face did not contract declared row slot 3")
    forbid(sparse_pairing,
           "bond|picture=9|row=2|from=1|to=2|dir=none|role=none|species=none",
           "sparse face contracted undeclared row slot 2")
    require(
        sparse_pairing,
        "boundary|picture=9|virtual-west=2|virtual-east=3|physical-up=0|physical-down=0",
        "neighboring port opposite an omitted sparse slot disappeared",
    )
    tall = pictures[10]
    require(tall, "faceports|picture=10|cell=1-1|face=west|arity=1|at=center",
            "tall glyph lost its centred west face")
    require(tall, "faceports|picture=10|cell=1-1|face=east|arity=2|at=1,2",
            "tall glyph lost its separate east face")
    require(
        tall,
        "boundary|picture=10|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "tall glyph boundary disagrees with its declared faces",
    )
    tall_pairing = pictures[11]
    require(tall_pairing,
            "bond|picture=11|row=1|from=1|to=2|dir=none|role=none|species=none",
            "tall glyph did not contract east slot 1")
    require(tall_pairing,
            "bond|picture=11|row=2|from=1|to=2|dir=none|role=none|species=none",
            "tall glyph did not contract east slot 2")
    lower_sparse = pictures[12]
    if paired_ports(lower_sparse) != [("1", "1")]:
        raise AssertionError("wide contraction ignored the lower face's exact slots")
    require(
        lower_sparse,
        "boundary|picture=12|virtual-west=1|virtual-east=1|physical-up=1|physical-down=1",
        "unmatched upper port disappeared from the boundary signature",
    )
    asymmetric_trace = pictures[13]
    require(asymmetric_trace,
            "warning|picture=13|code=phtrace-face-ports|cell=1-1",
            "asymmetric physical trace was not rejected")
    if "phtrace-face-ports" not in parsed_warnings[13]:
        raise AssertionError("physical-trace warning was dropped by the audit parser")
    forbid(asymmetric_trace,
           "phtrace|picture=13|row=1|col=1",
           "asymmetric physical trace emitted a centre-only loop")
    require(
        asymmetric_trace,
        "boundary|picture=13|virtual-west=1|virtual-east=1|physical-up=2|physical-down=1",
        "rejected physical trace did not leave its declared faces open",
    )
    compatibility_conflict = pictures[14]
    require(compatibility_conflict,
            "faceports|picture=14|cell=1-1|face=west|arity=2|at=1,2",
            "explicit split face did not override combined=")
    require(compatibility_conflict,
            "faceports|picture=14|cell=1-1|face=east|arity=2|at=rows",
            "opposite implicit split face acquired the wrong arity")
    require(
        compatibility_conflict,
        "boundary|picture=14|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "combined= conflict left a hidden centred stub",
    )
    brick_faces = pictures[15]
    require(brick_faces,
            "faceports|picture=15|cell=1-1|face=up|arity=1|at=center",
            "tall brick lost its centred physical face")
    require(brick_faces,
            "faceports|picture=15|cell=1-1|face=down|arity=2|at=1,2",
            "tall brick lost its split physical face")
    require(
        brick_faces,
        "boundary|picture=15|virtual-west=2|virtual-east=2|physical-up=1|physical-down=2",
        "tall brick physical signature disagrees with its declared faces",
    )
    lower_surplus = pictures[16]
    require(
        lower_surplus,
        "faceports|picture=16|cell=1-1|face=down|arity=1|at=1",
        "explicit one-column face was not recorded as slot 1",
    )
    if paired_ports(lower_surplus) != [("1", "1")]:
        raise AssertionError(
            "explicit one-column face did not emit contraction slot 1"
        )
    require(
        lower_surplus,
        "boundary|picture=16|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "surplus lower-face port disappeared from the boundary signature",
    )
    default_brick = pictures[17]
    require(
        default_brick,
        "faceports|picture=17|cell=1-1|face=up|arity=2|at=rows",
        "default tall-brick face record disagrees with its two drawn ports",
    )
    require(
        default_brick,
        "boundary|picture=17|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "face-port support changed the default tall-brick arity",
    )
    default_virtual = pictures[18]
    require(default_virtual,
            "faceports|picture=18|cell=1-1|face=west|arity=2|at=rows",
            "default tall glyph did not record its west split face")
    require(default_virtual,
            "faceports|picture=18|cell=1-1|face=east|arity=2|at=rows",
            "default tall glyph did not record its east split face")
    centred_virtual = pictures[19]
    require(centred_virtual,
            "bond|picture=19|row=1|from=1|to=2|dir=none|role=none|species=none",
            "centred virtual face did not meet row 1")
    require(centred_virtual,
            "bond|picture=19|row=2|from=1|to=2|dir=none|role=none|species=none",
            "centred virtual face did not meet every row of its span")
    hole = pictures[20]
    forbid(hole,
           "bond|picture=20|row=2|from=1|to=2|dir=none|role=none|species=none",
           "sparse virtual face acquired a port in its omitted row")
    pair_trace = pictures[21]
    require(pair_trace,
            "warning|picture=21|code=pair-trace-face-ports|cell=1-1",
            "multi-port pair trace was not rejected")
    if "pair-trace-face-ports" not in parsed_warnings[21]:
        raise AssertionError("pair-trace warning was dropped by the audit parser")
    forbid(pair_trace,
           "pairtrace|picture=21|row=1|col=1",
           "multi-port pair trace emitted a misleading centre loop")
    if paired_ports(pair_trace) != [("1", "1"), ("2", "2")]:
        raise AssertionError("rejected pair trace did not retain both ordinary contractions")
    opened_wide = pictures[22]
    require(
        opened_wide,
        "boundary|picture=22|virtual-west=2|virtual-east=2|physical-up=3|physical-down=1",
        "opened wide interface omitted an unmatched lower-face port",
    )
    opened_plain = pictures[23]
    require(
        opened_plain,
        "boundary|picture=23|virtual-west=2|virtual-east=2|physical-up=3|physical-down=1",
        "opened centred interface omitted an unmatched lower-face port",
    )
    single_wire = pictures[24]
    require(single_wire,
            "faceports|picture=24|cell=1-1|face=west|arity=1|at=center",
            "single-wire centred west face was not recorded")
    require(single_wire,
            "faceports|picture=24|cell=1-1|face=east|arity=1|at=center",
            "single-wire centred east face was not recorded")
    if any(
        event.kind == "warning"
        and event.attrs.get("code") == "combined-wires"
        and event.attrs.get("cell") == "1-1"
        for event in parsed_pictures[24].events
    ):
        raise AssertionError("single-wire centred face was mistaken for combined=")
    physical_pair_trace = pictures[25]
    require(physical_pair_trace,
            "warning|picture=25|code=pair-trace-face-ports|cell=1-1",
            "multi-port physical-column trace was not rejected")
    forbid(physical_pair_trace,
           "pairtrace|picture=25|row=1|col=1",
           "multi-port physical-column trace emitted a centre loop")
    if paired_ports(physical_pair_trace) != [("1", "1"), ("2", "2")]:
        raise AssertionError(
            "rejected physical-column trace did not retain ordinary contractions"
        )
    sparse_open = pictures[26]
    require(
        sparse_open,
        "boundary|picture=26|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "opened sparse lower face changed its exact-slot signature",
    )
    partial_skip = pictures[27]
    require(
        partial_skip,
        "boundary|picture=27|virtual-west=2|virtual-east=2|physical-up=1|physical-down=1",
        "one skipped column counted the whole upper face",
    )
    sparse_skip = pictures[28]
    require(
        sparse_skip,
        "boundary|picture=28|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "a skipped column invented an absent sparse upper port",
    )
    lower_partial_skip = pictures[29]
    require(
        lower_partial_skip,
        "boundary|picture=29|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "one skipped column counted the whole lower face",
    )
    upper_split_lower_center = pictures[30]
    if paired_ports(upper_split_lower_center) != [("1", "1")]:
        raise AssertionError("a centred lower face consumed multiple upper indices")
    require(
        upper_split_lower_center,
        "boundary|picture=30|virtual-west=2|virtual-east=2|physical-up=1|physical-down=1",
        "an unmatched upper port disappeared beside a centred lower face",
    )
    continuation_center = pictures[31]
    require(
        continuation_center,
        "bond|picture=31|row=2|from=1|to=2|dir=none|role=none|species=none",
        "continuation-row bond did not meet the centred fusion face",
    )
    require(
        continuation_center,
        "boundary|picture=31|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "contracted centred fusion face was still counted as open",
    )
    two_centred_faces = pictures[32]
    require(
        two_centred_faces,
        "faceports|picture=32|cell=1-1|face=west|arity=1|at=center",
        "tall glyph lost its centred west face",
    )
    require(
        two_centred_faces,
        "faceports|picture=32|cell=1-1|face=east|arity=1|at=center",
        "tall glyph lost its independent centred east face",
    )
    require(
        two_centred_faces,
        "boundary|picture=32|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "two centred virtual faces did not contribute independently",
    )
    separate_upper_cells = pictures[33]
    if paired_ports(separate_upper_cells) != [("center", "1")]:
        raise AssertionError("separate upper glyphs consumed one centred lower index twice")
    require(
        separate_upper_cells,
        "boundary|picture=33|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "the surplus upper index beside a centred lower face disappeared",
    )
    distant_center = pictures[34]
    require(
        distant_center,
        "bond|picture=34|row=1|from=1|to=3|dir=none|role=none|species=none",
        "centred fusion face did not meet its distant row-1 neighbour",
    )
    require(
        distant_center,
        "boundary|picture=34|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "a distant bond left the centred fusion face counted as open",
    )
    invalid_slot = pictures[35]
    require(
        invalid_slot,
        "faceports|picture=35|cell=1-1|face=east|arity=0|at=none",
        "out-of-span virtual slot was not normalized away",
    )
    require(
        invalid_slot,
        "boundary|picture=35|virtual-west=2|virtual-east=0|physical-up=0|physical-down=0",
        "out-of-span virtual slot survived in the boundary signature",
    )
    suppressed_physical = pictures[36]
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=1-1|face=up|arity=1|at=center",
        "no-legs tensor emitted a physical upper face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=1-1|face=down|arity=1|at=center",
        "no-legs tensor emitted a physical lower face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=2-1|face=up|arity=1|at=center",
        "on-wire matrix emitted a physical upper face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=2-1|face=down|arity=1|at=center",
        "on-wire matrix emitted a physical lower face",
    )
    require(
        suppressed_physical,
        "boundary|picture=36|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "suppressed physical faces survived in the boundary signature",
    )
    opened_center = pictures[37]
    require(
        opened_center,
        "boundary|picture=37|virtual-west=2|virtual-east=2|physical-up=3|physical-down=2",
        "an opened centred lower face did not retain both interface stubs",
    )
    duplicate_slots = pictures[38]
    require(
        duplicate_slots,
        "faceports|picture=38|cell=1-1|face=west|arity=1|at=1",
        "duplicate west slots survived canonicalization",
    )
    require(
        duplicate_slots,
        "faceports|picture=38|cell=1-1|face=east|arity=1|at=2",
        "duplicate east slots survived canonicalization",
    )
    require(
        duplicate_slots,
        "boundary|picture=38|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "duplicate virtual slots inflated the boundary signature",
    )
    nolegs_brick = pictures[39]
    forbid(
        nolegs_brick,
        "faceports|picture=39|cell=1-1|face=up|arity=2|at=rows",
        "no-legs brick emitted a physical face",
    )
    require(
        nolegs_brick,
        "boundary|picture=39|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "no-legs brick retained physical ink in its signature",
    )
    if topology_hashes[40] != topology_hashes[41]:
        raise AssertionError("equivalent default and explicit face slots hashed differently")
    opened_center_twice = pictures[42]
    require(
        opened_center_twice,
        "boundary|picture=42|virtual-west=2|virtual-east=2|physical-up=3|physical-down=2",
        "opened centred lower face was counted once per upper column",
    )
    opened_split_twice = pictures[43]
    require(
        opened_split_twice,
        "boundary|picture=43|virtual-west=2|virtual-east=2|physical-up=4|physical-down=2",
        "opened split lower face was counted in full per upper column",
    )
    for picture_id in (44, 45):
        suppressed_trace = pictures[picture_id]
        require(
            suppressed_trace,
            f"warning|picture={picture_id}|code=pair-trace-face-ports|cell=1-1",
            "pair trace did not reject a suppressed physical face",
        )
        forbid(
            suppressed_trace,
            f"pairtrace|picture={picture_id}|row=1|col=1|site=1-1",
            "pair trace contracted a suppressed physical face",
        )
    require(
        pictures[44],
        "boundary|picture=44|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "lower port facing a suppressed upper face did not remain open",
    )
    require(
        pictures[45],
        "boundary|picture=45|virtual-west=2|virtual-east=2|physical-up=0|physical-down=1",
        "upper port facing a suppressed lower face did not remain open",
    )
    partial_wide_open = pictures[46]
    if paired_ports(partial_wide_open) != [("2", "2")]:
        raise AssertionError("wide open= affected a physical slot in another column")
    require(
        partial_wide_open,
        "boundary|picture=46|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "wide open= did not retain exactly the addressed upper and lower slots",
    )
    inactive_physical = pictures[47]
    forbid(
        inactive_physical,
        "faceports|picture=47|cell=1-1|face=up|arity=1|at=center",
        "wire-row tensor emitted an inactive upper face",
    )
    forbid(
        inactive_physical,
        "faceports|picture=47|cell=1-1|face=down|arity=1|at=center",
        "wire-row tensor emitted an inactive lower face",
    )
    require(
        inactive_physical,
        "boundary|picture=47|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "inactive physical keys changed the boundary signature",
    )
    normalized_physical = pictures[48]
    require(
        normalized_physical,
        "faceports|picture=48|cell=1-1|face=up|arity=1|at=1",
        "duplicate or out-of-span upper slots survived normalization",
    )
    require(
        normalized_physical,
        "faceports|picture=48|cell=1-1|face=down|arity=1|at=2",
        "duplicate or out-of-span lower slots survived normalization",
    )
    require(
        normalized_physical,
        "boundary|picture=48|virtual-west=1|virtual-east=1|physical-up=1|physical-down=1",
        "normalized physical slots disagree with the boundary signature",
    )
    sparse_periodic = pictures[49]
    require(
        sparse_periodic,
        "trace|picture=49|row=1|side=above",
        "periodic closure omitted the row with two endpoint ports",
    )
    forbid(
        sparse_periodic,
        "trace|picture=49|row=2|side=below",
        "periodic closure joined a row with a suppressed endpoint",
    )
    require(
        sparse_periodic,
        "warning|picture=49|code=periodic-face-ports|row=2",
        "sparse periodic endpoint was not reported",
    )
    if "periodic-face-ports" not in parsed_warnings[49]:
        raise AssertionError("periodic warning was dropped by the audit parser")
    require(
        sparse_periodic,
        "boundary|picture=49|virtual-west=1|virtual-east=0|physical-up=0|physical-down=0",
        "unmatched periodic endpoint did not remain open",
    )
    sparse_hooks = pictures[50]
    require(
        sparse_hooks,
        "hooks|picture=50|row=1|side=above",
        "hook closure omitted the row with two endpoint ports",
    )
    forbid(
        sparse_hooks,
        "hooks|picture=50|row=2|side=below",
        "hook closure joined a row with a suppressed endpoint",
    )
    require(
        sparse_hooks,
        "warning|picture=50|code=periodic-face-ports|row=2",
        "sparse hook endpoint was not reported",
    )
    require(
        sparse_hooks,
        "boundary|picture=50|virtual-west=1|virtual-east=0|physical-up=0|physical-down=0",
        "unmatched hook endpoint did not remain open",
    )
    invalid_physical = pictures[51]
    require(
        invalid_physical,
        "faceports|picture=51|cell=1-1|face=up|arity=0|at=none",
        "wholly out-of-range physical face was not rejected",
    )
    require(
        invalid_physical,
        "boundary|picture=51|virtual-west=1|virtual-east=1|physical-up=0|physical-down=1",
        "rejected physical face left ink in the boundary signature",
    )
    partial_wide_pair = pictures[52]
    if paired_ports(partial_wide_pair) != [("2", "2")]:
        raise AssertionError("opened wide owner failed to contract its other slot")
    require(
        partial_wide_pair,
        "boundary|picture=52|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "opened wide owner counted its contracted lower slot as open",
    )
    if "TENKZ-LOWER-MATCH-LABEL" not in run.stdout:
        raise AssertionError("opened matched lower slot dropped its aligned label")
    suppressed_upper = pictures[53]
    require(
        suppressed_upper,
        "faceports|picture=53|cell=2-1|face=up|arity=1|at=center",
        "lower face below a no-legs tensor was not recorded",
    )
    forbid(
        suppressed_upper,
        "pairleg|picture=53|",
        "lower face below a no-legs tensor was contracted",
    )
    require(
        suppressed_upper,
        "boundary|picture=53|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "lower face below a no-legs tensor did not remain open",
    )
    centered_periodic = pictures[54]
    require(
        centered_periodic,
        "trace|picture=54|row=1|side=above",
        "centered periodic face did not close once",
    )
    forbid(
        centered_periodic,
        "trace|picture=54|row=2|side=below",
        "centered periodic face closed once per spanned row",
    )
    require(
        centered_periodic,
        "boundary|picture=54|virtual-west=0|virtual-east=0|physical-up=0|physical-down=0",
        "centered periodic closure remained open in the boundary signature",
    )
    centered_hooks = pictures[55]
    require(
        centered_hooks,
        "hooks|picture=55|row=1|side=above",
        "centered periodic hooks did not close once",
    )
    forbid(
        centered_hooks,
        "hooks|picture=55|row=2|side=below",
        "centered periodic hooks closed once per spanned row",
    )
    require(
        centered_hooks,
        "boundary|picture=55|virtual-west=0|virtual-east=0|physical-up=0|physical-down=0",
        "centered periodic hooks remained open in the boundary signature",
    )
    opened_unmatched_wide = pictures[56]
    if paired_ports(opened_unmatched_wide) != [("1", "1")]:
        raise AssertionError("opened unmatched wide slot changed another contraction")
    require(
        opened_unmatched_wide,
        "boundary|picture=56|virtual-west=2|virtual-east=2|physical-up=1|physical-down=1",
        "opened unmatched wide slot was counted more than once",
    )
    require(
        pictures[57],
        "boundary|picture=57|virtual-west=2|virtual-east=2|physical-up=3|physical-down=1",
        "matched and surplus opened lower slots were not both counted",
    )
    require(
        pictures[58],
        "boundary|picture=58|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "a suppressed split lower face survived below an absent upper site",
    )
    wide_suppressed_upper = pictures[60]
    require(
        wide_suppressed_upper,
        "boundary|picture=60|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "wide no-legs owner reopened one centered lower port per column",
    )
    for picture_id, code, event in (
        (61, "combined-side",
         "warning|picture=61|code=combined-side|value=north"),
        (62, "combined-wires",
         "warning|picture=62|code=combined-wires|cell=1-1"),
        (63, "combined-attach",
         "warning|picture=63|code=combined-attach|row=1"),
        (64, "label-pos",
         "warning|picture=64|code=label-pos|pos=bogus"),
    ):
        require(pictures[picture_id], event,
                f"{code} warning lost picture ownership")
        if code not in parsed_warnings[picture_id]:
            raise AssertionError(f"{code} warning was dropped by the audit parser")
    fused_periodic = pictures[65]
    require(
        fused_periodic,
        "trace|picture=65|row=1|side=above",
        "centered fused periodic face did not close once",
    )
    forbid(
        fused_periodic,
        "trace|picture=65|row=2|side=below",
        "centered fused periodic face closed once per spanned row",
    )
    require(
        fused_periodic,
        "boundary|picture=65|virtual-west=0|virtual-east=0|physical-up=0|physical-down=0",
        "centered fused periodic closure remained open in the boundary signature",
    )
    fused_hooks = pictures[66]
    require(
        fused_hooks,
        "hooks|picture=66|row=1|side=above",
        "centered fused hooks did not close once",
    )
    forbid(
        fused_hooks,
        "hooks|picture=66|row=2|side=below",
        "centered fused hooks closed once per spanned row",
    )
    require(
        fused_hooks,
        "boundary|picture=66|virtual-west=0|virtual-east=0|physical-up=0|physical-down=0",
        "centered fused hooks remained open in the boundary signature",
    )
    require(
        pictures[67],
        "boundary|picture=67|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "opened centered lower label fixture changed its face topology",
    )
    empty_upper_two_lower = pictures[68]
    require(
        empty_upper_two_lower,
        "faceports|picture=68|cell=1-1|face=down|arity=0|at=none",
        "out-of-range upper face did not normalize to empty",
    )
    forbid(
        empty_upper_two_lower,
        "pairleg|picture=68|",
        "empty upper face contracted a lower physical index",
    )
    require(
        empty_upper_two_lower,
        "boundary|picture=68|virtual-west=2|virtual-east=2|physical-up=3|physical-down=0",
        "empty wide upper face did not open both ordinary lower owners",
    )
    require(
        pictures[69],
        "boundary|picture=69|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "empty wide upper face reopened a centered lower owner twice",
    )
    nolegs_upper_two_lower = pictures[70]
    forbid(
        nolegs_upper_two_lower,
        "pairleg|picture=70|",
        "wide no-legs upper owner contracted a lower physical index",
    )
    require(
        nolegs_upper_two_lower,
        "boundary|picture=70|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "wide no-legs upper owner did not open both ordinary lower owners",
    )
    shifted_centered_lower = pictures[71]
    forbid(
        shifted_centered_lower,
        "pairleg|picture=71|",
        "shifted centered lower owner was contracted through a suppressed face",
    )
    require(
        shifted_centered_lower,
        "boundary|picture=71|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "shifted centered lower owner was not reopened",
    )
    invalid_physical_rows = pictures[72]
    require(
        invalid_physical_rows,
        "warning|picture=72|code=physical-face-rows|cell=1-1",
        "invalid physical rows token was not reported",
    )
    require(
        invalid_physical_rows,
        "faceports|picture=72|cell=1-1|face=up|arity=0|at=none",
        "invalid physical rows token did not normalize to an empty face",
    )
    require(
        invalid_physical_rows,
        "boundary|picture=72|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "invalid physical rows token survived boundary accounting",
    )
    shifted_empty_upper = pictures[73]
    require(
        shifted_empty_upper,
        "boundary|picture=73|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "an empty shifted upper overlap did not open the centred lower owner",
    )
    invalid_one_row_virtual = pictures[74]
    require(
        invalid_one_row_virtual,
        "faceports|picture=74|cell=1-1|face=west|arity=0|at=none",
        "out-of-range one-row west face was not normalized to empty",
    )
    require(
        invalid_one_row_virtual,
        "faceports|picture=74|cell=1-1|face=east|arity=0|at=none",
        "explicitly empty one-row east face was not preserved",
    )
    require(
        invalid_one_row_virtual,
        "boundary|picture=74|virtual-west=0|virtual-east=0|physical-up=0|physical-down=0",
        "empty one-row virtual faces survived boundary accounting",
    )
    interior_centered = pictures[75]
    require(
        interior_centered,
        "hooks|picture=75|row=1|side=above",
        "interior centered fixture did not close its outer periodic row",
    )
    forbid(
        interior_centered,
        "hooks|picture=75|row=3|side=below",
        "interior centered fixture closed through a continuation row",
    )
    require(
        interior_centered,
        "boundary|picture=75|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "unconsumed interior centered faces changed boundary topology",
    )
    for picture, closure in ((76, "hooks"), (77, "trace"),
                             (78, "hooks"), (79, "trace")):
        mismatch = pictures[picture]
        require(
            mismatch,
            f"warning|picture={picture}|code=periodic-face-ports|row=1",
            f"picture {picture} did not report its unmatched periodic face",
        )
        forbid(
            mismatch,
            f"{closure}|picture={picture}|",
            f"picture {picture} closed a one-sided periodic face",
        )
        require(
            mismatch,
            f"boundary|picture={picture}|virtual-west=1|virtual-east=0|"
            "physical-up=0|physical-down=0",
            f"picture {picture} counted its unmatched centered face twice",
        )
    physical_rows_one = pictures[80]
    require(
        physical_rows_one,
        "faceports|picture=80|cell=1-1|face=down|arity=1|at=rows",
        "one-row physical face was not declared through rows",
    )
    require(
        physical_rows_one,
        "pairleg|picture=80|upper=1-1|lower=2-1|upper-port=center|column=1",
        "one-row physical face lost its unique centered contraction",
    )
    print("PASS: physical faces, compatibility aliases, and virtual face arity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
