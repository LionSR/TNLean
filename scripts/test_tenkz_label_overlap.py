#!/usr/bin/env python3
"""Regression check for measured label/glyph/wire overlap events."""

from __future__ import annotations

import io
import os
import re
import shutil
import subprocess
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

from tenkz_audit import Audit


ROOT = Path(__file__).resolve().parents[1]


def finding_picture_id(message: str) -> int:
    """Return the exact leading picture identifier from an audit finding."""
    match = re.match(r"^picture (-?\d+)\b", message)
    if match is None:
        raise AssertionError(f"overlap finding lacks a picture prefix: {message}")
    return int(match.group(1))


SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\makeatletter
\def\tenkzassertrelax#1{%
  \expandafter\ifx\csname #1\endcsname\relax\else
    \PackageError{tenkz test}{Snapshot state '#1' was not released}{}%
  \fi}
\def\tenkzassertsnapshotclean{%
  \edef\tenkztesttoken{\the\tenkz@glyphsnapuid}%
  \tenkzassertrelax{tenkz@pathxmin@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@pathxmax@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@pathymin@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@pathymax@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@outerx@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@outery@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@stroke@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@draw@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@fill@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@double@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@shade@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@fade@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@pathpicture@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@clip@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@join@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@dash@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@strokeopacity@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@fillopacity@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@textopacity@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@textwidth@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@textheight@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@textdepth@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@invalid@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@outercount@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@modecount@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@usecount@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@auditowner@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@snapshotdone@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@glypharcflag@\tenkztesttoken}%
  \tenkzassertrelax{tenkz@glypharc@\tenkztesttoken}}
\newcount\tenkztestouterhookcalls
\def\tenkztestcountouterhook{%
  \let\tenkztestrealouterhook\pgf@outer@adjust@hook
  \def\pgf@outer@adjust@hook{%
    \global\advance\tenkztestouterhookcalls by 1\relax
    \tenkztestrealouterhook}}
\makeatother
% Deliberately unsafe: the explicit separation overrides the measured label band.
\begin{tenkzcd}[maps, species={channel}, column sep=2mm]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{18mm}{0pt}\mathcal T}
\end{tenkzcd}

% Safe: production spacing is derived from the same materialized label box.
% Matrix passthrough may change the live object shape; measurement follows it.
\begingroup
\tikzset{tn label/.append style={
  fill=tenkzPaper, draw, line join=round, line width=2pt}}
\begin{tenkzcd}[maps, species={channel}, nodes={circle}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{18mm}{0pt}\mathcal T}
\end{tenkzcd}
\endgroup

% Shared style capture covers unnamed production labels in every core tier.
\begin{tenkzfree}
  \tnput[box]{a}{(0,0)}{A}
  \tnput[box]{b}{(20mm,0)}{}
  \tnjoin[label=f]{a.east}{b.west}
  \node[tn label, fill=tenkzPaper, draw, line join=round, line width=2pt]
    at (40mm,0) {$g$};
\end{tenkzfree}
\begin{tenkz}
  \tn{B} & \tn[box]{}
\end{tenkz}
\begin{tenkzlattice}[rows=1, cols=2]
  \tnsite[label=$C$]{(1,1)}
\end{tenkzlattice}
\begin{tenkz}
  \tn{} & \tn[pill]{} & \tnX{} & \tn[tri=l]{}
\end{tenkz}
% A final style override must change the emitted geometry too.  The small label
% sits inside the rectangle's corner but outside its inscribed circle.
\tikzset{tensor/.append style={
  rectangle, minimum width=10mm, minimum height=10mm}}
\begin{tenkzfree}
  \tnput{reshaped}{(0,0)}{}
  \node[tn label, inner sep=0pt] at (4.7mm,4.7mm)
    {\rule{0.3mm}{0.3mm}};
\end{tenkzfree}
% Final corner overrides must likewise win over the semantic skin defaults.
\tikzset{
  pill tensor/.append style={rounded corners=0pt},
  box tensor/.append style={rounded corners=1.5pt}}
\begin{tenkzfree}
  \tnput[pill]{sharp-pill}{(0,0)}{}
  \tnput[box]{rounded-box}{(20mm,0)}{}
\end{tenkzfree}
% A large outer separation is positioning whitespace, not glyph ink.
\begingroup
\tikzset{box tensor/.append style={
  minimum size=4pt, inner sep=0pt, outer sep=20pt}}
\begin{tenkzfree}
  \tnput[box]{outer-gap}{(0,0)}{}
  \node[tn label, inner sep=0pt] at (10pt,0) {\rule{1pt}{1pt}};
\end{tenkzfree}
\endgroup
% Every matrix object is audited once, even without an incident map, and live
% rounded-corner passthrough remains visible in the emitted shape.
\begin{tenkzcd}[
  maps, species={channel}, nodes={rectangle, rounded corners=2pt}
]
  A & B & C
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{f}
\end{tenkzcd}
\tenkzassertrelax{tenkz@glyphsnaptoken@tenkzmap-1-3}
% Empty resolved regions are legitimate no-ops and still emit audit data.
\begin{tenkzlattice}[rows=1, cols=1]
  \tnregion[name=R]{(1,1)}
  \tnregion{R - R}
\end{tenkzlattice}
% Visible glyph ink includes the live stroke, but not positioning margin.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=20pt, line width=4pt}}
\begin{tenkzfree}
  \tnput[box]{stroke-hit}{(0,0)}{}
  \node[tn label, inner sep=0pt, outer sep=0pt] at (3pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkzfree}
\begin{tenkzfree}
  \tnput[box]{margin-safe}{(0,0)}{}
  \node[tn label, inner sep=0pt, outer sep=0pt] at (10pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkzfree}
\endgroup
\tenkzassertsnapshotclean
% draw=none removes the stroke band from visible geometry.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=20pt, line width=4pt, draw=none}}
\begin{tenkzfree}
  \tnput[box]{undrawn}{(0,0)}{}
  \node[tn label, inner sep=0pt, outer sep=0pt] at (3pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkzfree}
\endgroup
% Transparent-label inner and outer separation are invisible whitespace.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=1pt, minimum height=1pt, inner sep=0pt,
  outer sep=0pt, draw=none}}
\begin{tenkzfree}
  \tnput[box]{label-margin-safe}{(4pt,0)}{}
  \node[tn label, inner sep=9pt, outer sep=8pt] at (0,0)
    {\rule{1pt}{1pt}};
\end{tenkzfree}
\endgroup
\tenkzassertsnapshotclean
% Circle anchors use max(outer xsep, outer ysep) on every axis.
\begingroup
\tikzset{tensor/.append style={circle, minimum width=4pt,
  minimum height=4pt, inner sep=0pt, outer xsep=2pt, outer ysep=5pt,
  line width=4pt}}
\begin{tenkzfree}
  \tnput{anisotropic-circle}{(0,0)}{}
\end{tenkzfree}
\endgroup
% A late line-width override is the width used by the audit snapshot.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=0pt, line width=4pt}}
\begin{tenkzfree}
  \tnput[box]{late-width}{(0,0)}{}
\end{tenkzfree}
\endgroup
% Ordinary coordinate rotation does not transform the node shape.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt}}
\begin{tenkzfree}
  \begin{scope}[rotate=45]
    \tnput[box]{untransformed-rotate}{(0,0)}{}
  \end{scope}
\end{tenkzfree}
\endgroup
% outer sep=auto must be evaluated at execute-end-node, not parsed literally.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=auto, line width=4pt,
  /utils/exec=\tenkztestcountouterhook}}
\begin{tenkzfree}
  \tnput[box]{auto-drawn}{(0,0)}{}
\end{tenkzfree}
\endgroup
\ifnum\tenkztestouterhookcalls=1\relax\else
  \PackageError{tenkz test}{Audited outer hook did not run exactly once}{}%
\fi
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=auto, line width=4pt, draw=none}}
\begin{tenkzfree}
  \tnput[box]{auto-undrawn}{(0,0)}{}
\end{tenkzfree}
\endgroup
\tenkzassertsnapshotclean
\end{document}
"""

AFFINE_GLYPHS = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\tikzset{
  tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  box tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  pill tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  canonical tensor/.append style={tenkz glyph basis={1,0,.5,.75}}}
\begin{tenkzfree}
  \tnput[dot]{dot}{(0,0)}{}
  \tnput[box]{box}{(2,0)}{}
  \tnput[pill]{pill}{(4,0)}{}
\end{tenkzfree}
\begingroup
\tikzset{tensor/.append style={outer sep=0pt}}
\begin{tenkzfree}
  \tnput[dot]{outer-zero}{(0,0)}{}
\end{tenkzfree}
\endgroup
\begingroup
\tikzset{tensor/.append style={outer sep=20pt}}
\begin{tenkzfree}
  \tnput[dot]{outer-large}{(0,0)}{}
\end{tenkzfree}
\endgroup
\begin{tenkz}
  \tn[tri=l]{}
\end{tenkz}
\makeatletter
\def\tenkzassertaffineclean#1{%
  \@for\tenkztestslot:=pathxmin,pathxmax,pathymin,pathymax\do{%
    \expandafter\ifx\csname tenkz@\tenkztestslot @#1\endcsname\relax\else
      \PackageError{tenkz test}{Affine path snapshot #1 was not released}{}%
    \fi}}
\tenkzassertaffineclean{1}
\tenkzassertaffineclean{2}
\tenkzassertaffineclean{3}
\tenkzassertaffineclean{4}
\tenkzassertaffineclean{5}
\tenkzassertaffineclean{6}
\makeatother
\end{document}
"""

INVALID_CORNERS = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\tikzset{box tensor/.append style={
  /utils/exec={\pgfsetcornersarced{\pgfpoint{2pt}{3pt}}}}}
\begin{tenkzfree}
  \tnput[box]{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
"""

ROUNDED_TRIANGLE = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{canonical tensor/.append style={rounded corners=1pt}}
\begin{tenkz}
  \tn[tri=l]{}
\end{tenkz}
\end{document}
"""

OVERSIZED_OUTER_SEP = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{box tensor/.append style={
  minimum size=4pt, inner sep=0pt, outer sep=20pt, rounded corners=6pt}}
\begin{tenkzfree}
  \tnput[box]{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
"""

INACTIVE_SNAPSHOT = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\makeatletter
\begin{tikzpicture}
  \node[tree junction] at (0,0) {};
\end{tikzpicture}
\ifnum\tenkz@glyphsnapuid=0\relax\else
  \PackageError{tenkz}{Inactive glyph audit allocated a snapshot token}{}
\fi
\makeatother
\end{document}
"""

TRANSFORMED_RECT = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{box tensor/.append style={rotate=45, transform shape}}
\begin{tenkzfree}
  \tnput[box]{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
"""

TRANSFORMED_CIRCLE = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{tensor/.append style={xscale=2, transform shape}}
\begin{tenkzfree}
  \tnput{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
"""

TRANSFORMED_TRIANGLE = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{canonical tensor/.append style={rotate=30, transform shape}}
\begin{tenkz}
  \tn[tri=l]{}
\end{tenkz}
\end{document}
"""

TRANSFORMED_LABEL = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkzfree}
  \node[tn label, rotate=45, transform shape] at (0,0) {$f$};
\end{tenkzfree}
\end{document}
"""

DRAW_ONLY_GLYPH = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{box tensor/.append style={fill=none}}
\begin{tenkzfree}
  \tnput[box]{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
"""

NONRECTANGLE_LABEL = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkzfree}
  \node[tn label, circle] at (0,0) {$f$};
\end{tenkzfree}
\end{document}
"""

NONAUDITED_CUSTOMIZATION = r"""
\documentclass{article}
\usepackage{tenkz}
\usetikzlibrary{fadings}
\begin{document}
\begin{tikzpicture}
  \node[draw, fill=blue, line join=miter, dashed, double,
    draw opacity=0, fill opacity=0, path fading=west] at (0,0) {control};
\end{tikzpicture}
\end{document}
"""

NESTED_END_HOOK = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\newif\ifinhook
\tikzset{box tensor/.append style={execute at end node={%
  \ifinhook\else\global\inhooktrue
  \tikz[baseline] \node[tn label] (inner-audit) {inner};%
  \global\inhookfalse\fi}}}
\begin{tenkzfree}
  \tnput[box]{outer}{(0,0)}{}
\end{tenkzfree}
\makeatletter
\def\tenkzassertrelax#1{%
  \expandafter\ifx\csname #1\endcsname\relax\else
    \PackageError{tenkz test}{Audit ownership state '#1' was not released}{}%
  \fi}
\ifx\tenkz@auditinstallowner\relax\else
  \PackageError{tenkz test}{Per-node audit claimant leaked its scope}{}%
\fi
\tenkzassertrelax{tenkz@audittoken@outer}
\tenkzassertrelax{tenkz@audittoken@inner-audit}
\tenkzassertrelax{tenkz@auditowner@1}
\tenkzassertrelax{tenkz@snapshotdone@1}
\tenkzassertrelax{tenkz@auditowner@2}
\tenkzassertrelax{tenkz@snapshotdone@2}
\makeatother
\end{document}
"""


def customized_glyph(options: str, preamble: str = "") -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
%s
\begin{document}
\tikzset{box tensor/.append style={%s}}
\begin{tenkzfree}
  \tnput[box]{bad}{(0,0)}{}
\end{tenkzfree}
\end{document}
""" % (preamble, options)


def customized_label(options: str, preamble: str = "") -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
%s
\begin{document}
\begin{tenkzfree}
  \node[tn label, %s] at (0,0) {$f$};
\end{tenkzfree}
\end{document}
""" % (preamble, options)


def audit_status(path: Path) -> tuple[int, Audit]:
    audit = Audit(path, None)
    with redirect_stdout(io.StringIO()):
        status = audit.run()
    return status, audit


def main() -> int:
    if (finding_picture_id("picture 1 label bbox id=1 intersects rect glyph") != 1
            or finding_picture_id(
                "picture 12 label bbox id=1 intersects rect glyph") != 12):
        raise AssertionError("picture-id parser aliases picture 1 and picture 12")
    engine = shutil.which("xelatex")
    if engine is None:
        print("SKIP: xelatex not found")
        return 0

    with tempfile.TemporaryDirectory(prefix="tenkz-label-overlap-") as tmp:
        work = Path(tmp)
        tex = work / "label-overlap.tex"
        tex.write_text(SOURCE, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get("TEXINPUTS", "")
        try:
            run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
                cwd=work,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
        except subprocess.TimeoutExpired as exc:
            print(exc.stdout or "")
            print("FAIL: label-overlap fixture timed out after 120 seconds")
            return 1
        if run.returncode:
            print(run.stdout)
            print("FAIL: label-overlap fixture did not compile")
            return 1

        audit = Audit(work / "label-overlap.tnlog", tex)
        with redirect_stdout(io.StringIO()):
            status = audit.run()
        if status != 1:
            raise AssertionError("audit accepted the deliberately overlapping fixture")

        overlaps = [finding for finding in audit.findings
                    if finding.rule == "label-overlap"]
        label_events = [event for event in audit.events()
                        if event.kind == "bbox"
                        and event.attrs.get("class") == "label"]
        if any(not {"shape", "radius"} <= event.attrs.keys()
               for event in label_events):
            raise AssertionError("a measured label omitted exact shape fields")
        overlap_pictures = {finding_picture_id(finding.msg) for finding in overlaps}
        if overlap_pictures != {1, 7, 12}:
            raise AssertionError(
                "overlap findings missed an unsafe picture: "
                + "; ".join(finding.msg for finding in overlaps)
            )

        empty_regions = [
            event for event in audit.events(11)
            if event.kind == "region" and event.attrs.get("cells") == ""
        ]
        if len(empty_regions) != 1 or any(
                finding.rule == "malformed-event"
                and "region field cells=''" in finding.msg
                for finding in audit.findings):
            raise AssertionError("audit rejected a live empty resolved region")

        for picture_id in (1, 2):
            bbox_classes = {
                event.attrs.get("class") for event in audit.events(picture_id)
                if event.kind == "bbox"
            }
            geometry_kinds = {event.kind for event in audit.events(picture_id)}
            if (bbox_classes != {"label"}
                    or not {"glyph-geometry", "wire-geometry"} <= geometry_kinds):
                raise AssertionError(
                    f"picture {picture_id} emitted incomplete geometry: "
                    f"bbox={bbox_classes}, kinds={geometry_kinds}"
                )
        map_shapes = {
            event.attrs.get("shape") for event in audit.events(2)
            if event.kind == "glyph-geometry"
        }
        if map_shapes != {"circle"}:
            raise AssertionError(
                f"typed-map object restyle emitted stale geometry: {map_shapes}"
            )
        map_glyphs = [event for event in audit.events(2)
                      if event.kind == "glyph-geometry"]
        if len(map_glyphs) != 2:
            raise AssertionError(
                f"typed-map objects were not audited exactly once: {len(map_glyphs)}"
            )
        map_wires = [event for event in audit.events(2)
                     if event.kind == "wire-geometry"]
        if len(map_wires) != 1:
            raise AssertionError(
                f"typed-map emitted invalid exact wire geometry: {len(map_wires)}"
            )
        map_labels = [event for event in audit.events(2)
                      if event.kind == "bbox"
                      and event.attrs.get("class") == "label"]
        if (len(map_labels) != 1
                or map_labels[0].attrs.get("shape") != "roundrect"
                or abs(int(map_labels[0].attrs.get("radius", "0"))
                       - 65536) > 1):
            raise AssertionError(
                "typed-map stored label lost its exact shape: "
                + repr([event.attrs for event in map_labels])
            )
        wire_heights = [int(event.attrs["outer"]) for event in map_wires]
        if any(height >= 65536 for height in wire_heights):
            raise AssertionError(
                f"typed-map wire bbox followed an offset label: {wire_heights}sp"
            )
        for picture_id in (3, 4, 5):
            events = audit.events(picture_id)
            uses = sum(event.kind == "label-use" for event in events)
            labels = sum(event.kind == "bbox"
                         and event.attrs.get("class") == "label"
                         for event in events)
            if uses == 0 or uses != labels:
                raise AssertionError(
                    f"picture {picture_id} did not capture label coverage: "
                    f"uses={uses}, labels={labels}"
                )
        free_labels = [event for event in audit.events(3)
                       if event.kind == "bbox"
                       and event.attrs.get("class") == "label"]
        free_shapes = {event.attrs.get("shape") for event in free_labels}
        if free_shapes != {"rect", "roundrect"}:
            raise AssertionError(
                f"drawn/default labels emitted stale shapes: {free_shapes}"
            )
        drawn_labels = [event for event in free_labels
                        if event.attrs.get("shape") == "roundrect"]
        if (len(drawn_labels) != 1
                or abs(int(drawn_labels[0].attrs["radius"]) - 65536) > 1):
            raise AssertionError(
                "drawn sharp label did not emit its half-stroke radius"
            )

        missing = work / "missing-label-bbox.tnlog"
        missing.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "label-use|picture=1\n",
            encoding="utf-8",
        )
        missing_status, missing_audit = audit_status(missing)
        if missing_status != 1 or not any(
                finding.rule == "bbox-coverage"
                for finding in missing_audit.findings):
            raise AssertionError("audit accepted an unmeasured library label use")

        shapes = {
            event.attrs.get("shape") for event in audit.events(6)
            if event.kind == "glyph-geometry"
        }
        if shapes != {"circle", "roundrect", "triangle"}:
            raise AssertionError(f"core shape fixture emitted {shapes}")
        triangle_geometry = [
            event for event in audit.events(6)
            if event.kind == "glyph-geometry"
            and event.attrs.get("shape") == "triangle"
        ]
        if (len(triangle_geometry) != 1
                or int(triangle_geometry[0].attrs["stroke"]) <= 0):
            raise AssertionError(
                "live triangle fixture lost its nonzero visible stroke"
            )

        reshaped = {
            event.attrs.get("shape") for event in audit.events(7)
            if event.kind == "glyph-geometry"
        }
        if reshaped != {"roundrect"}:
            raise AssertionError(
                f"final rectangle override emitted stale geometry: {reshaped}"
            )

        corner_events = [
            event for event in audit.events(8)
            if event.kind == "glyph-geometry"
        ]
        corner_shapes = [event.attrs.get("shape") for event in corner_events]
        if corner_shapes != ["roundrect", "roundrect"]:
            raise AssertionError(
                f"final corner overrides emitted stale geometry: {corner_shapes}"
            )
        if abs(int(corner_events[0].attrs["radius"])
               - round(0.275 * 65536)) > 1:
            raise AssertionError("sharp pill omitted its visible stroke radius")
        if abs(int(corner_events[1].attrs["radius"])
               - round(1.775 * 65536)) > 1:
            raise AssertionError("rounded box did not emit its live corner radius")

        outer_gap = [event for event in audit.events(9)
                     if event.kind == "glyph-geometry"]
        if len(outer_gap) != 1:
            raise AssertionError("outer-separation fixture lost glyph geometry")
        if (int(outer_gap[0].attrs["xmax"])
                - int(outer_gap[0].attrs["xmin"])) >= round(10 * 65536):
            raise AssertionError("glyph geometry retained invisible outer separation")

        rounded_map = [event for event in audit.events(10)
                       if event.kind == "glyph-geometry"]
        if len(rounded_map) != 3:
            raise AssertionError(
                "typed-map object census omitted or duplicated a cell: "
                f"{len(rounded_map)}"
            )
        if ({event.attrs.get("shape") for event in rounded_map} != {"roundrect"}
                or any(abs(int(event.attrs["radius"])
                           - round(2 * 65536)) > 1
                       for event in rounded_map)):
            raise AssertionError(
                "typed-map rounded-corner passthrough was not preserved: "
                + repr([(event.attrs.get("shape"), event.attrs.get("radius"))
                        for event in rounded_map])
            )

        expected_widths = {
            12: 8, 13: 8, 14: 4, 16: 8, 17: 8, 19: 8, 20: 4,
        }
        for picture_id, expected_pt in expected_widths.items():
            geometry = [event for event in audit.events(picture_id)
                        if event.kind == "glyph-geometry"]
            if len(geometry) != 1:
                raise AssertionError(
                    f"picture {picture_id} lost exact glyph geometry"
                )
            width = int(geometry[0].attrs["xmax"]) - int(geometry[0].attrs["xmin"])
            if abs(width - round(expected_pt * 65536)) > 2:
                raise AssertionError(
                    f"picture {picture_id} emitted width {width}sp, "
                    f"expected {expected_pt}pt: {geometry[0].attrs}"
                )

        label_boxes = [event for event in audit.events(15)
                       if event.kind == "bbox"
                       and event.attrs.get("class") == "label"]
        if len(label_boxes) != 1:
            raise AssertionError("label outer-separation fixture lost its bbox")
        label_width = (int(label_boxes[0].attrs["xmax"])
                       - int(label_boxes[0].attrs["xmin"]))
        if label_width >= round(2 * 65536):
            raise AssertionError("label bbox retained invisible outer separation")

        rotate_control = [event for event in audit.events(18)
                          if event.kind == "glyph-geometry"]
        if (len(rotate_control) != 1
                or rotate_control[0].attrs.get("shape") != "roundrect"):
            raise AssertionError("ordinary node rotation was rejected as transformed")

        affine = work / "affine-glyphs.tex"
        affine.write_text(AFFINE_GLYPHS, encoding="utf-8")
        affine_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", affine.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if affine_run.returncode:
            print(affine_run.stdout)
            raise AssertionError("affine glyph fixture did not compile")
        affine_status, affine_audit = audit_status(work / "affine-glyphs.tnlog")
        if affine_status != 0:
            raise AssertionError(
                "audit rejected explicitly tagged affine glyphs: "
                + "; ".join(finding.msg for finding in affine_audit.findings)
            )
        affine_geometry = [
            event for event in affine_audit.events()
            if event.kind == "glyph-geometry"
        ]
        if len(affine_geometry) != 6:
            raise AssertionError(
                f"affine fixture emitted {len(affine_geometry)} glyphs"
            )
        if any(
                event.attrs.get("shape") != "rect"
                or event.attrs.get("radius") != "0"
                or any(event.attrs.get(field) != "0"
                       for field in ("x1", "y1", "x2", "y2", "x3", "y3"))
                for event in affine_geometry):
            raise AssertionError(
                "affine glyphs did not use conservative rectangular hulls: "
                + repr([event.attrs for event in affine_geometry])
            )
        extents = [
            (int(event.attrs["xmax"]) - int(event.attrs["xmin"]),
             int(event.attrs["ymax"]) - int(event.attrs["ymin"]))
            for event in affine_geometry
        ]
        if extents[-3] != extents[-2]:
            raise AssertionError(
                f"affine glyph hull retained outer separation: {extents[-3:-1]}"
            )
        if extents[0][0] == extents[0][1]:
            raise AssertionError("affine dot fixture did not exercise anisotropy")

        invalid = work / "invalid-corners.tex"
        invalid.write_text(INVALID_CORNERS, encoding="utf-8")
        invalid_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", invalid.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if invalid_run.returncode == 0 or "unequal corner radii" not in invalid_run.stdout:
            raise AssertionError("audit accepted a non-isotropic rounded rectangle")

        for filename, source, diagnostic in (
            ("rounded-triangle.tex", ROUNDED_TRIANGLE, "has rounded corners"),
            ("oversized-outer-sep.tex", OVERSIZED_OUTER_SEP,
             "radius exceeds half its"),
            ("transformed-rect.tex", TRANSFORMED_RECT,
             "unsupported affine"),
            ("transformed-circle.tex", TRANSFORMED_CIRCLE,
             "unsupported affine"),
            ("transformed-triangle.tex", TRANSFORMED_TRIANGLE,
             "unsupported affine"),
            ("transformed-label.tex", TRANSFORMED_LABEL,
             "unsupported affine"),
            ("draw-only-glyph.tex", DRAW_ONLY_GLYPH, "has no filled shape"),
            ("pathless-glyph.tex", customized_glyph("coordinate"),
             "has no captured path state"),
            ("nonrectangle-label.tex", NONRECTANGLE_LABEL,
             "unsupported live shape"),
            ("rounded-label.tex", customized_label(
                "fill=tenkzPaper, rounded corners=1pt"),
             "has rounded corners"),
            ("miter-glyph.tex", customized_glyph("line join=miter"),
             "non-round line join"),
            ("bevel-glyph.tex", customized_glyph("line join=bevel"),
             "non-round line join"),
            ("miter-label.tex", customized_label(
                "fill=tenkzPaper, draw, line join=miter"),
             "non-round line join"),
            ("double-glyph.tex", customized_glyph("double"),
             "double stroke"),
            ("double-distance-glyph.tex",
             customized_glyph("double distance=2pt"), "double stroke"),
            ("double-label.tex", customized_label(
                "fill=tenkzPaper, draw, double"),
             "double stroke"),
            ("dashed-glyph.tex", customized_glyph("dashed"),
             "dashed stroke"),
            ("dashed-label.tex", customized_label(
                "fill=tenkzPaper, draw, dashed"),
             "dashed stroke"),
            ("zero-draw-glyph.tex", customized_glyph("draw opacity=0"),
             "zero draw opacity"),
            ("zero-draw-label.tex",
             customized_label("fill=tenkzPaper, draw, draw opacity=0"),
             "zero draw opacity"),
            ("zero-fill-glyph.tex", customized_glyph("fill opacity=0"),
             "zero fill opacity"),
            ("zero-fill-label.tex", customized_label(
                "fill=tenkzPaper, fill opacity=0"),
             "zero fill opacity"),
            ("outline-label.tex", customized_label("fill=none, draw"),
             "has an outline"),
            ("zero-text-label.tex", customized_label("text opacity=0"),
             "zero text opacity"),
            ("shade-glyph.tex", customized_glyph("shade"),
             "uses shading"),
            ("fading-glyph.tex",
             customized_glyph("path fading=west", "\\usetikzlibrary{fadings}"),
             "uses fading"),
            ("path-picture-glyph.tex",
             customized_glyph("path picture={\\fill (0,0) circle[radius=1pt];}"),
             "uses a path picture"),
        ):
            failure = work / filename
            failure.write_text(source, encoding="utf-8")
            failure_run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error", failure.name],
                cwd=work,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
            if failure_run.returncode == 0 or diagnostic not in failure_run.stdout:
                raise AssertionError(
                    f"audit accepted {filename}: {failure_run.stdout[-1000:]}"
                )

        inactive = work / "inactive-snapshot.tex"
        inactive.write_text(INACTIVE_SNAPSHOT, encoding="utf-8")
        inactive_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", inactive.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if inactive_run.returncode:
            raise AssertionError(
                "inactive audited glyph leaked snapshot state: "
                + inactive_run.stdout[-1000:]
            )

        nonaudited = work / "nonaudited-customization.tex"
        nonaudited.write_text(NONAUDITED_CUSTOMIZATION, encoding="utf-8")
        nonaudited_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             nonaudited.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if nonaudited_run.returncode:
            raise AssertionError(
                "non-audited TikZ customization was not transparent: "
                + nonaudited_run.stdout[-1000:]
            )

        nested = work / "nested-end-hook.tex"
        nested.write_text(NESTED_END_HOOK, encoding="utf-8")
        nested_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", nested.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if nested_run.returncode:
            raise AssertionError(
                "nested audited execute-end hook corrupted the pending stack: "
                + nested_run.stdout[-1000:]
            )
        nested_log = (work / "nested-end-hook.tnlog").read_text(encoding="utf-8")
        if (nested_log.count("label-use|") != 1
                or nested_log.count("class=label|") != 1
                or nested_log.count("glyph-geometry|") != 1):
            raise AssertionError(
                "nested audited execute-end hook lost or duplicated geometry: "
                + nested_log
            )

        exact = work / "exact-shapes.tnlog"
        exact.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|xmin=8|xmax=10|ymin=8|ymax=10|"
            "shape=rect|radius=0\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "glyph-geometry|picture=1|owner=1|shape=circle|xmin=-10|xmax=10|"
            "ymin=-10|ymax=10|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=2|shape=roundrect\n"
            "glyph-geometry|picture=1|owner=2|shape=roundrect|xmin=20|xmax=40|"
            "ymin=20|ymax=40|radius=8|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=3|shape=triangle\n"
            "glyph-geometry|picture=1|owner=3|shape=triangle|xmin=50|xmax=70|"
            "ymin=0|ymax=20|radius=0|stroke=0|"
            "x1=70|y1=10|x2=50|y2=20|x3=50|y3=0\n",
            encoding="utf-8",
        )
        exact_status, exact_audit = audit_status(exact)
        if exact_status != 0:
            raise AssertionError(
                "exact geometry rejected bbox-only corner near misses: "
                + "; ".join(finding.msg for finding in exact_audit.findings)
            )

        def write_triangle_stroke_fixture(
                name: str, bounds: tuple[int, int, int, int]) -> Path:
            fixture = work / name
            xmin, xmax, ymin, ymax = bounds
            fixture.write_text(
                "picture|id=1|lang=free\n"
                "atom|picture=1|name=a|kind=dot\n"
                "label-use|picture=1\n"
                f"bbox|picture=1|class=label|id=1|xmin={xmin}|xmax={xmax}|"
                f"ymin={ymin}|ymax={ymax}|shape=rect|radius=0\n"
                "ink-use|picture=1|class=glyph|id=1|shape=triangle\n"
                "glyph-geometry|picture=1|owner=1|shape=triangle|"
                "xmin=-2|xmax=12|ymin=-12|ymax=12|radius=0|stroke=2|"
                "x1=0|y1=0|x2=10|y2=10|x3=10|y3=-10\n",
                encoding="utf-8",
            )
            return fixture

        for name, bounds in (
            ("triangle-edge-stroke.tnlog", (11, 12, -1, 1)),
            ("triangle-vertex-stroke.tnlog", (-2, -1, -1, 1)),
        ):
            triangle_status, triangle_audit = audit_status(
                write_triangle_stroke_fixture(name, bounds)
            )
            if triangle_status != 1 or not any(
                    finding.rule == "label-overlap"
                    for finding in triangle_audit.findings):
                raise AssertionError(
                    f"audit missed exact triangle stroke overlap in {name}"
                )

        tangent_status, tangent_audit = audit_status(
            write_triangle_stroke_fixture(
                "triangle-stroke-tangent.tnlog", (-4, -2, -1, 1)
            )
        )
        if tangent_status != 0:
            raise AssertionError(
                "triangle stroke tangency was rejected: "
                + "; ".join(finding.msg for finding in tangent_audit.findings)
            )

        def write_round_label_glyph_fixture(name: str, edge: int) -> Path:
            fixture = work / name
            fixture.write_text(
                "picture|id=1|lang=free\n"
                "atom|picture=1|name=a|kind=dot\n"
                "label-use|picture=1\n"
                "bbox|picture=1|class=label|id=1|owner=0|"
                "xmin=0|xmax=100|ymin=0|ymax=100|"
                "shape=roundrect|radius=40\n"
                "ink-use|picture=1|class=glyph|id=1|shape=rect\n"
                "glyph-geometry|picture=1|owner=1|shape=rect|"
                f"xmin=-10|xmax={edge}|ymin=-10|ymax={edge}|"
                "radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n",
                encoding="utf-8",
            )
            return fixture

        near_status, near_audit = audit_status(
            write_round_label_glyph_fixture("round-label-near-miss.tnlog", 10)
        )
        if near_status != 0:
            raise AssertionError(
                "round-label corner near miss was rejected: "
                + "; ".join(finding.msg for finding in near_audit.findings)
            )
        inward_status, inward_audit = audit_status(
            write_round_label_glyph_fixture("round-label-overlap.tnlog", 12)
        )
        if inward_status != 1 or not any(
                finding.rule == "label-overlap"
                for finding in inward_audit.findings):
            raise AssertionError("audit missed round-label corner overlap")

        round_branches = work / "round-label-glyph-branches.tnlog"
        round_branches.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=0|xmax=100|ymin=0|ymax=100|"
            "shape=roundrect|radius=40\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "glyph-geometry|picture=1|owner=1|shape=circle|"
            "xmin=40|xmax=60|ymin=40|ymax=60|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=2|shape=roundrect\n"
            "glyph-geometry|picture=1|owner=2|shape=roundrect|"
            "xmin=45|xmax=65|ymin=45|ymax=65|radius=5|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=3|shape=triangle\n"
            "glyph-geometry|picture=1|owner=3|shape=triangle|"
            "xmin=40|xmax=60|ymin=40|ymax=60|radius=0|stroke=1|"
            "x1=40|y1=40|x2=60|y2=50|x3=40|y3=60\n",
            encoding="utf-8",
        )
        branches_status, branches_audit = audit_status(round_branches)
        branch_shapes = {
            shape for shape in ("circle", "roundrect", "triangle")
            if any(f"intersects {shape} glyph" in finding.msg
                   for finding in branches_audit.findings)
        }
        if branches_status != 1 or branch_shapes != {
                "circle", "roundrect", "triangle"}:
            raise AssertionError(
                f"round-label glyph branches were not exercised: {branch_shapes}"
            )

        anchor_prefix = (
            "picture|id=1|lang=lattice\n"
            "lattice|picture=1|rows=1|cols=1\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "glyph-geometry|picture=1|owner=1|shape=circle|"
            "xmin=40|xmax=60|ymin=40|ymax=60|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=45|xmax=65|ymin=45|ymax=65|shape=rect|radius=0\n"
        )
        valid_anchor = work / "lattice-label-anchor-site.tnlog"
        valid_anchor.write_text(
            anchor_prefix
            + "label-anchor-site|picture=1|label=1|x=50|y=50\n",
            encoding="utf-8",
        )
        valid_anchor_status, valid_anchor_audit = audit_status(valid_anchor)
        if valid_anchor_status != 0:
            raise AssertionError(
                "declared lattice corner-label adjacency was rejected: "
                + "; ".join(
                    finding.msg for finding in valid_anchor_audit.findings
                )
            )

        wrong_anchor = work / "lattice-label-wrong-anchor-site.tnlog"
        wrong_anchor.write_text(
            anchor_prefix
            + "label-anchor-site|picture=1|label=1|x=51|y=50\n",
            encoding="utf-8",
        )
        wrong_anchor_status, wrong_anchor_audit = audit_status(wrong_anchor)
        if wrong_anchor_status != 1 or not any(
                finding.rule == "malformed-event"
                and "matches no circle glyph center" in finding.msg
                for finding in wrong_anchor_audit.findings):
            raise AssertionError("audit accepted a nonexistent label anchor site")

        wrong_dialect = work / "free-label-anchor-site.tnlog"
        wrong_dialect.write_text(
            anchor_prefix.replace("lang=lattice", "lang=free", 1)
            + "label-anchor-site|picture=1|label=1|x=50|y=50\n",
            encoding="utf-8",
        )
        wrong_dialect_status, wrong_dialect_audit = audit_status(wrong_dialect)
        if wrong_dialect_status != 1 or not any(
                finding.rule == "dialect-mismatch"
                and "valid only in a lattice picture" in finding.msg
                for finding in wrong_dialect_audit.findings):
            raise AssertionError("audit accepted a non-lattice label anchor site")

        def write_cut_wire_fixture(
                name: str, query: tuple[int, int, int, int], inner: int = 0,
                y: int = 10, outer: int = 20,
        ) -> Path:
            fixture = work / name
            qxmin, qxmax, qymin, qymax = query
            fixture.write_text(
                "picture|id=1|lang=free\n"
                "atom|picture=1|name=a|kind=dot\n"
                "label-use|picture=1\n"
                "bbox|picture=1|class=label|id=1|owner=0|"
                "xmin=20|xmax=80|ymin=0|ymax=60|"
                "shape=roundrect|radius=20\n"
                "label-use|picture=1\n"
                "bbox|picture=1|class=label|id=2|owner=0|"
                f"xmin={qxmin}|xmax={qxmax}|ymin={qymin}|ymax={qymax}|"
                "shape=rect|radius=0\n"
                "ink-use|picture=1|class=wire|id=1\n"
                "wire-geometry|picture=1|owner=1|shape=rect-minus-label|"
                f"xmin=0|xmax=100|y={y}|outer={outer}|inner={inner}|"
                "cut-shape=roundrect|cut-xmin=20|cut-xmax=80|"
                "cut-ymin=0|cut-ymax=60|cut-radius=20|cut-id=1\n",
                encoding="utf-8",
            )
            return fixture

        crescent_status, crescent_audit = audit_status(
            write_cut_wire_fixture("wire-corner-crescent.tnlog", (21, 25, 1, 5))
        )
        if crescent_status != 1 or not any(
                "visible typed-map wire" in finding.msg
                for finding in crescent_audit.findings):
            raise AssertionError("audit missed visible rounded-corner wire ink")
        covered_status, covered_audit = audit_status(
            write_cut_wire_fixture("wire-covered-by-label.tnlog", (35, 45, 5, 15))
        )
        covered_overlaps = [finding for finding in covered_audit.findings
                            if finding.rule == "label-overlap"]
        if (covered_status != 1 or len(covered_overlaps) != 1
                or "intersects label bbox" not in covered_overlaps[0].msg
                or "visible typed-map wire" in covered_overlaps[0].msg):
            raise AssertionError(
                "covered query did not suppress cascading wire diagnostics"
            )
        tangent_status, tangent_audit = audit_status(
            write_cut_wire_fixture("wire-strict-tangent.tnlog", (0, 10, 20, 25))
        )
        if tangent_status != 0:
            raise AssertionError(
                "wire or cut tangency was rejected: "
                + "; ".join(finding.msg for finding in tangent_audit.findings)
            )
        odd_overlap_status, odd_overlap_audit = audit_status(
            write_cut_wire_fixture(
                "odd-sp-wire-overlap.tnlog", (5, 10, 18022, 18023),
                y=0, outer=36045,
            )
        )
        if odd_overlap_status != 1 or not any(
                "visible typed-map wire" in finding.msg
                for finding in odd_overlap_audit.findings):
            raise AssertionError("audit lost an odd-width half-sp overlap")
        odd_disjoint_status, odd_disjoint_audit = audit_status(
            write_cut_wire_fixture(
                "odd-sp-wire-disjoint.tnlog", (5, 10, 18023, 18024),
                y=0, outer=36045,
            )
        )
        if odd_disjoint_status != 0:
            raise AssertionError(
                "audit invented overlap beyond an odd-width half-sp boundary: "
                + "; ".join(
                    finding.msg for finding in odd_disjoint_audit.findings
                )
            )
        gap_status, gap_audit = audit_status(
            write_cut_wire_fixture(
                "fused-wire-gap.tnlog", (5, 10, 6, 14), inner=10
            )
        )
        if gap_status != 0:
            raise AssertionError(
                "audit treated the fused paper gap as wire ink: "
                + "; ".join(finding.msg for finding in gap_audit.findings)
            )
        solid_center_status, solid_center_audit = audit_status(
            write_cut_wire_fixture(
                "colored-or-translucent-inner.tnlog", (5, 10, 6, 14), inner=0
            )
        )
        if solid_center_status != 1 or not any(
                "visible typed-map wire" in finding.msg
                for finding in solid_center_audit.findings):
            raise AssertionError(
                "audit treated a visible inner band as an empty fused gap"
            )
        rail_status, rail_audit = audit_status(
            write_cut_wire_fixture(
                "fused-wire-rail.tnlog", (5, 10, 1, 4), inner=10
            )
        )
        if rail_status != 1 or not any(
                "visible typed-map wire" in finding.msg
                for finding in rail_audit.findings):
            raise AssertionError("audit missed a fused typed-map rail overlap")

        malformed_wire_prefix = (
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=20|xmax=80|ymin=0|ymax=60|"
            "shape=roundrect|radius=20\n"
        )
        malformed_wire_event = (
            "ink-use|picture=1|class=wire|id=1\n"
            "wire-geometry|picture=1|owner=1|shape=rect-minus-label|"
            "xmin=0|xmax=100|y=10|outer=20|inner=0|"
            "cut-shape=roundrect|cut-xmin=20|cut-xmax=80|"
            "cut-ymin=0|cut-ymax=60|cut-radius=20"
        )

        def assert_malformed_wire(
                filename: str, body: str, diagnostic: str) -> None:
            fixture = work / filename
            fixture.write_text(body, encoding="utf-8")
            status, malformed_audit = audit_status(fixture)
            if status != 1 or not any(
                    finding.rule == "malformed-event"
                    and diagnostic in finding.msg
                    for finding in malformed_audit.findings):
                raise AssertionError(
                    f"audit missed malformed wire case {filename}: "
                    + "; ".join(
                        finding.msg for finding in malformed_audit.findings
                    )
                )

        assert_malformed_wire(
            "wire-missing-cut-id.tnlog",
            malformed_wire_prefix + malformed_wire_event + "\n",
            "lacks required field(s): cut-id",
        )
        assert_malformed_wire(
            "wire-duplicate-cut-id.tnlog",
            malformed_wire_prefix
            + "label-use|picture=1\n"
            + "bbox|picture=1|class=label|id=1|owner=0|"
            + "xmin=20|xmax=80|ymin=0|ymax=60|"
            + "shape=roundrect|radius=20\n"
            + malformed_wire_event + "|cut-id=1\n",
            "references non-unique cut label bbox id=1",
        )
        assert_malformed_wire(
            "wire-dangling-cut-id.tnlog",
            malformed_wire_prefix + malformed_wire_event + "|cut-id=99\n",
            "references missing cut label bbox id=99",
        )
        assert_malformed_wire(
            "wire-mismatched-cut-id.tnlog",
            malformed_wire_prefix
            + malformed_wire_event.replace("cut-xmin=20", "cut-xmin=21")
            + "|cut-id=1\n",
            "cut geometry disagrees with label bbox id=1",
        )
        assert_malformed_wire(
            "wire-negative-inner.tnlog",
            malformed_wire_prefix
            + malformed_wire_event.replace("inner=0", "inner=-1")
            + "|cut-id=1\n",
            "wire-geometry field inner='-1' fails validation",
        )
        assert_malformed_wire(
            "wire-degenerate-inner.tnlog",
            malformed_wire_prefix
            + malformed_wire_event.replace("inner=0", "inner=20")
            + "|cut-id=1\n",
            "inner gap=20 is not smaller than outer width=20",
        )

        oversized_roundrect = work / "oversized-roundrect.tnlog"
        oversized_roundrect.write_text(
            "picture|id=1|lang=free\n"
            "ink-use|picture=1|class=glyph|id=1|shape=roundrect\n"
            "glyph-geometry|picture=1|owner=1|shape=roundrect|"
            "xmin=0|xmax=10|ymin=0|ymax=10|radius=6|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n",
            encoding="utf-8",
        )
        oversized_status, oversized_audit = audit_status(oversized_roundrect)
        if oversized_status != 1 or not any(
                finding.rule == "malformed-event"
                and "exceeds half" in finding.msg
                for finding in oversized_audit.findings):
            raise AssertionError("audit clamped malformed roundrect geometry")

        nonsquare_circle = work / "nonsquare-circle.tnlog"
        nonsquare_circle.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "glyph-geometry|picture=1|owner=1|shape=circle|"
            "xmin=0|xmax=10|ymin=0|ymax=12|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n",
            encoding="utf-8",
        )
        circle_status, circle_audit = audit_status(nonsquare_circle)
        if circle_status != 1 or not any(
                finding.rule == "malformed-event"
                and "ellipses are unsupported" in finding.msg
                for finding in circle_audit.findings):
            raise AssertionError("audit accepted a nonsquare circle geometry")

        empty_region = work / "empty-region.tnlog"
        empty_region.write_text(
            "picture|id=1|lang=lattice\n"
            "region|picture=1|slot=selected|cells=\n",
            encoding="utf-8",
        )
        empty_region_status, empty_region_audit = audit_status(empty_region)
        if empty_region_status != 0:
            raise AssertionError(
                "audit rejected a synthetic empty resolved region: "
                + "; ".join(
                    finding.msg for finding in empty_region_audit.findings
                )
            )

        malformed_region = work / "malformed-region.tnlog"
        malformed_region.write_text(
            "picture|id=1|lang=lattice\n"
            "region|picture=1|slot=selected|cells=1-1,bad\n",
            encoding="utf-8",
        )
        malformed_region_status, malformed_region_audit = audit_status(
            malformed_region
        )
        if malformed_region_status != 1 or not any(
                finding.rule == "malformed-event"
                for finding in malformed_region_audit.findings):
            raise AssertionError("audit weakened non-empty region validation")

        missing_ink = work / "missing-ink-geometry.tnlog"
        missing_ink.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "ink-use|picture=1|class=wire|id=2\n",
            encoding="utf-8",
        )
        missing_ink_status, missing_ink_audit = audit_status(missing_ink)
        if missing_ink_status != 1 or sum(
                finding.rule == "bbox-coverage"
                for finding in missing_ink_audit.findings) != 2:
            raise AssertionError("audit accepted unmeasured glyph/wire owners")

        duplicate_geometry = work / "duplicate-ink-geometry.tnlog"
        duplicate_geometry.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "ink-use|picture=1|class=glyph|id=1|shape=rect\n"
            "glyph-geometry|picture=1|owner=1|shape=rect|"
            "xmin=0|xmax=10|ymin=0|ymax=10|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "glyph-geometry|picture=1|owner=1|shape=rect|"
            "xmin=0|xmax=10|ymin=0|ymax=10|radius=0|stroke=0|"
            "x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n",
            encoding="utf-8",
        )
        duplicate_status, duplicate_audit = audit_status(duplicate_geometry)
        if duplicate_status != 1 or not any(
                finding.rule == "bbox-coverage"
                and "produced 2 matching geometries" in finding.msg
                for finding in duplicate_audit.findings):
            raise AssertionError("audit accepted duplicate owner geometry")

        missing_class = work / "missing-ink-class.tnlog"
        missing_class.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "ink-use|picture=1|id=1\n"
            "bbox|picture=1|class=wire|id=1|owner=1|"
            "xmin=0|xmax=1|ymin=0|ymax=1\n",
            encoding="utf-8",
        )
        missing_class_status, missing_class_audit = audit_status(missing_class)
        if missing_class_status != 1 or not any(
                finding.rule == "malformed-event"
                for finding in missing_class_audit.findings):
            raise AssertionError("audit accepted an ink-use without class")

        glyph_bbox = work / "glyph-bbox.tnlog"
        glyph_bbox.write_text(
            "picture|id=1|lang=free\n"
            "bbox|picture=1|class=glyph|id=1|owner=1|"
            "xmin=0|xmax=1|ymin=0|ymax=1\n",
            encoding="utf-8",
        )
        glyph_bbox_status, glyph_bbox_audit = audit_status(glyph_bbox)
        if glyph_bbox_status != 1 or not any(
                finding.rule == "malformed-event"
                and "class=glyph" in finding.msg
                for finding in glyph_bbox_audit.findings):
            raise AssertionError("audit accepted obsolete glyph bbox geometry")

        grid_source = (ROOT / "tex/tenkz/tenkz-grid.code.tex").read_text(
            encoding="utf-8")
        for function in ("tenkz_draw_lower_label:N", "tenkz_pair_wide_leg:nn",
                         "tenkz_brick_face:nnnNn"):
            start = grid_source.index(f"\\cs_new_protected:Npn \\{function}")
            excerpt = grid_source[start:start + 7000]
            if "\\node[tn~label" not in excerpt and \
               "\\__tenkz_render_labelnode:nnn" not in excerpt:
                raise AssertionError(f"{function} bypasses the audited label style")

        core_source = (ROOT / "tex/tenkz/tenkz-core.code.tex").read_text(
            encoding="utf-8")
        for style in ("tensor", "box tensor", "pill tensor", "on-wire matrix",
                      "canonical tensor", "tree junction"):
            start = core_source.index(f"  {style}/.style=")
            if "tenkz audited glyph=" not in core_source[start:start + 180]:
                raise AssertionError(f"core glyph skin {style} lacks geometry")

    print("PASS: sibling-node overlap geometry and coverage invariants hold")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
