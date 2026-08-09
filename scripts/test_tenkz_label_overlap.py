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
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
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
% Shared style capture covers unnamed production labels and raw audited
% nodes on the local audited canvas.
\begin{tenkztestcanvas}
  \node[box tensor] (a) at (0,0) {$A$};
  \node[box tensor] (b) at (20mm,0) {};
  \node[tn label] at (10mm,0) {$f$};
  \node[tn label, fill=tenkzPaper, draw, line join=round, line width=2pt]
    at (40mm,0) {$g$};
\end{tenkztestcanvas}
\begin{tenkz}
  \tn{B} & \tn[skin=box]{}
\end{tenkz}
\begin{tenkz}
  \tn{} & \tn[skin=pill]{} & \tn[skin=ring]{} & \tn[skin=tri]{}
\end{tenkz}
% A final style override must change the emitted geometry too.  The small label
% sits inside the rectangle's corner but outside its inscribed circle.
\tikzset{tensor/.append style={
  rectangle, minimum width=10mm, minimum height=10mm}}
\begin{tenkztestcanvas}
  \node[tensor] (reshaped) at (0,0) {};
  \node[tn label, inner sep=0pt] at (4.7mm,4.7mm)
    {\rule{0.3mm}{0.3mm}};
\end{tenkztestcanvas}
% Final corner overrides must likewise win over the semantic skin defaults.
\tikzset{
  pill tensor/.append style={rounded corners=0pt},
  box tensor/.append style={rounded corners=1.5pt}}
\begin{tenkztestcanvas}
  \node[pill tensor] (sharp-pill) at (0,0) {};
  \node[box tensor] (rounded-box) at (20mm,0) {};
\end{tenkztestcanvas}
% A large outer separation is positioning whitespace, not glyph ink.
\begingroup
\tikzset{box tensor/.append style={
  minimum size=4pt, inner sep=0pt, outer sep=20pt}}
\begin{tenkztestcanvas}
  \node[box tensor] (outer-gap) at (0,0) {};
  \node[tn label, inner sep=0pt] at (10pt,0) {\rule{1pt}{1pt}};
\end{tenkztestcanvas}
\endgroup
% Visible glyph ink includes the live stroke, but not positioning margin.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=20pt, line width=4pt}}
\begin{tenkztestcanvas}
  \node[box tensor] (stroke-hit) at (0,0) {};
  \node[tn label, inner sep=0pt, outer sep=0pt] at (3pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkztestcanvas}
\begin{tenkztestcanvas}
  \node[box tensor] (margin-safe) at (0,0) {};
  \node[tn label, inner sep=0pt, outer sep=0pt] at (10pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkztestcanvas}
\endgroup
\tenkzassertsnapshotclean
% draw=none removes the stroke band from visible geometry.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=20pt, line width=4pt, draw=none}}
\begin{tenkztestcanvas}
  \node[box tensor] (undrawn) at (0,0) {};
  \node[tn label, inner sep=0pt, outer sep=0pt] at (3pt,0)
    {\rule{0.2pt}{0.2pt}};
\end{tenkztestcanvas}
\endgroup
% Transparent-label inner and outer separation are invisible whitespace.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=1pt, minimum height=1pt, inner sep=0pt,
  outer sep=0pt, draw=none}}
\begin{tenkztestcanvas}
  \node[box tensor] (label-margin-safe) at (4pt,0) {};
  \node[tn label, inner sep=9pt, outer sep=8pt] at (0,0)
    {\rule{1pt}{1pt}};
\end{tenkztestcanvas}
\endgroup
\tenkzassertsnapshotclean
% Circle anchors use max(outer xsep, outer ysep) on every axis.
\begingroup
\tikzset{tensor/.append style={circle, minimum width=4pt,
  minimum height=4pt, inner sep=0pt, outer xsep=2pt, outer ysep=5pt,
  line width=4pt}}
\begin{tenkztestcanvas}
  \node[tensor] (anisotropic-circle) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
% A late line-width override is the width used by the audit snapshot.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=0pt, line width=4pt}}
\begin{tenkztestcanvas}
  \node[box tensor] (late-width) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
% Ordinary coordinate rotation does not transform the node shape.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt}}
\begin{tenkztestcanvas}
  \begin{scope}[rotate=45]
    \node[box tensor] (untransformed-rotate) at (0,0) {};
  \end{scope}
\end{tenkztestcanvas}
\endgroup
% outer sep=auto must be evaluated at execute-end-node, not parsed literally.
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=auto, line width=4pt,
  /utils/exec=\tenkztestcountouterhook}}
\begin{tenkztestcanvas}
  \node[box tensor] (auto-drawn) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
\ifnum\tenkztestouterhookcalls=1\relax\else
  \PackageError{tenkz test}{Audited outer hook did not run exactly once}{}%
\fi
\begingroup
\tikzset{box tensor/.append style={rectangle, rounded corners=0pt,
  minimum width=4pt, minimum height=4pt, inner sep=0pt,
  outer sep=auto, line width=4pt, draw=none}}
\begin{tenkztestcanvas}
  \node[box tensor] (auto-undrawn) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
\tenkzassertsnapshotclean
\end{document}
"""

AFFINE_GLYPHS = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\pagestyle{empty}
\begin{document}
\tikzset{
  tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  box tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  pill tensor/.append style={tenkz glyph basis={1,0,.5,.75}},
  canonical tensor/.append style={tenkz glyph basis={1,0,.5,.75}}}
\begin{tenkztestcanvas}
  \node[tensor] (dot) at (0,0) {};
  \node[box tensor] (box) at (2,0) {};
  \node[pill tensor] (pill) at (4,0) {};
\end{tenkztestcanvas}
\begingroup
\tikzset{tensor/.append style={outer sep=0pt}}
\begin{tenkztestcanvas}
  \node[tensor] (outer-zero) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
\begingroup
\tikzset{tensor/.append style={outer sep=20pt}}
\begin{tenkztestcanvas}
  \node[tensor] (outer-large) at (0,0) {};
\end{tenkztestcanvas}
\endgroup
\begin{tenkz}
  \tn[skin=tri]{}
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
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\pagestyle{empty}
\begin{document}
\tikzset{box tensor/.append style={
  /utils/exec={\pgfsetcornersarced{\pgfpoint{2pt}{3pt}}}}}
\begin{tenkztestcanvas}
  \node[box tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
"""

ROUNDED_TRIANGLE = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{canonical tensor/.append style={rounded corners=1pt}}
\begin{tenkz}
  \tn[skin=tri]{}
\end{tenkz}
\end{document}
"""

OVERSIZED_OUTER_SEP = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{box tensor/.append style={
  minimum size=4pt, inner sep=0pt, outer sep=20pt, rounded corners=6pt}}
\begin{tenkztestcanvas}
  \node[box tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
"""

INACTIVE_SNAPSHOT = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
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
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{box tensor/.append style={rotate=45, transform shape}}
\begin{tenkztestcanvas}
  \node[box tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
"""

TRANSFORMED_CIRCLE = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{tensor/.append style={xscale=2, transform shape}}
\begin{tenkztestcanvas}
  \node[tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
"""

TRANSFORMED_TRIANGLE = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{canonical tensor/.append style={rotate=30, transform shape}}
\begin{tenkz}
  \tn[skin=tri]{}
\end{tenkz}
\end{document}
"""

TRANSFORMED_LABEL = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\begin{tenkztestcanvas}
  \node[tn label, rotate=45, transform shape] at (0,0) {$f$};
\end{tenkztestcanvas}
\end{document}
"""

DRAW_ONLY_GLYPH = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\tikzset{box tensor/.append style={fill=none}}
\begin{tenkztestcanvas}
  \node[box tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
"""

NONRECTANGLE_LABEL = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\begin{tenkztestcanvas}
  \node[tn label, circle] at (0,0) {$f$};
\end{tenkztestcanvas}
\end{document}
"""

NONAUDITED_CUSTOMIZATION = r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
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
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
\begin{document}
\newif\ifinhook
\tikzset{box tensor/.append style={execute at end node={%
  \ifinhook\else\global\inhooktrue
  \tikz[baseline] \node[tn label] (inner-audit) {inner};%
  \global\inhookfalse\fi}}}
\begin{tenkztestcanvas}
  \node[box tensor] (outer) at (0,0) {};
\end{tenkztestcanvas}
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
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
%s
\begin{document}
\tikzset{box tensor/.append style={%s}}
\begin{tenkztestcanvas}
  \node[box tensor] (bad) at (0,0) {};
\end{tenkztestcanvas}
\end{document}
""" % (preamble, options)


def customized_label(options: str, preamble: str = "") -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
\makeatletter
\newenvironment{tenkztestcanvas}
  {\global\advance\tenkz@pictureid by 1\relax\tenkz@auditpicturetrue\def\tenkz@auditpictureid{\the\tenkz@pictureid}\tenkz@event{picture|id=\the\tenkz@pictureid|lang=kernel}\tenkz@event{atom|picture=\the\tenkz@pictureid|cell=1-1|kind=dot}\tenkz@event{kernel-boundary|picture=\the\tenkz@pictureid|signature=}\begin{tikzpicture}[tenkz every picture]}
  {\end{tikzpicture}}
\makeatother
%s
\begin{document}
\begin{tenkztestcanvas}
  \node[tn label, %s] at (0,0) {$f$};
\end{tenkztestcanvas}
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
        if overlap_pictures != {2, 5}:
            raise AssertionError(
                "overlap findings missed an unsafe picture: "
                + "; ".join(finding.msg for finding in overlaps)
            )

        for picture_id in (1, "k1"):
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
        free_labels = [event for event in audit.events(1)
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
            "label-use|picture=1\n",
            encoding="utf-8",
        )
        missing_status, missing_audit = audit_status(missing)
        if missing_status != 1 or not any(
                finding.rule == "bbox-coverage"
                for finding in missing_audit.findings):
            raise AssertionError("audit accepted an unmeasured library label use")

        shapes = {
            event.attrs.get("shape") for event in audit.events("k2")
            if event.kind == "glyph-geometry"
        }
        if shapes != {"circle", "roundrect", "triangle"}:
            raise AssertionError(f"core shape fixture emitted {shapes}")
        triangle_geometry = [
            event for event in audit.events("k2")
            if event.kind == "glyph-geometry"
            and event.attrs.get("shape") == "triangle"
        ]
        if (len(triangle_geometry) != 1
                or int(triangle_geometry[0].attrs["stroke"]) <= 0):
            raise AssertionError(
                "live triangle fixture lost its nonzero visible stroke"
            )

        reshaped = {
            event.attrs.get("shape") for event in audit.events(2)
            if event.kind == "glyph-geometry"
        }
        if reshaped != {"roundrect"}:
            raise AssertionError(
                f"final rectangle override emitted stale geometry: {reshaped}"
            )

        corner_events = [
            event for event in audit.events(3)
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

        outer_gap = [event for event in audit.events(4)
                     if event.kind == "glyph-geometry"]
        if len(outer_gap) != 1:
            raise AssertionError("outer-separation fixture lost glyph geometry")
        if (int(outer_gap[0].attrs["xmax"])
                - int(outer_gap[0].attrs["xmin"])) >= round(10 * 65536):
            raise AssertionError("glyph geometry retained invisible outer separation")

        expected_widths = {
            5: 8, 6: 8, 7: 4, 9: 8, 10: 8, 12: 8, 13: 4,
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

        label_boxes = [event for event in audit.events(8)
                       if event.kind == "bbox"
                       and event.attrs.get("class") == "label"]
        if len(label_boxes) != 1:
            raise AssertionError("label outer-separation fixture lost its bbox")
        label_width = (int(label_boxes[0].attrs["xmax"])
                       - int(label_boxes[0].attrs["xmin"]))
        if label_width >= round(2 * 65536):
            raise AssertionError("label bbox retained invisible outer separation")

        rotate_control = [event for event in audit.events(11)
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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
                "picture|id=1|lang=kernel\n"
                "atom|picture=1|cell=1-1|kind=dot\n"
                "kernel-boundary|picture=1|signature=\n"
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
                "picture|id=1|lang=kernel\n"
                "atom|picture=1|cell=1-1|kind=dot\n"
                "kernel-boundary|picture=1|signature=\n"
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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

        def write_cut_wire_fixture(
                name: str, query: tuple[int, int, int, int], inner: int = 0,
                y: int = 10, outer: int = 20,
        ) -> Path:
            fixture = work / name
            qxmin, qxmax, qymin, qymax = query
            fixture.write_text(
                "picture|id=1|lang=kernel\n"
                "atom|picture=1|cell=1-1|kind=dot\n"
                "kernel-boundary|picture=1|signature=\n"
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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
            "picture|id=1|lang=kernel\n"
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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

        missing_ink = work / "missing-ink-geometry.tnlog"
        missing_ink.write_text(
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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
            "picture|id=1|lang=kernel\n"
            "atom|picture=1|cell=1-1|kind=dot\n"
            "kernel-boundary|picture=1|signature=\n"
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

        # A traced row's closure publishes its own contour (#5719).  The
        # rail that shipped in the print blueprint began one wrap reach out
        # from the row's west end, and no measured gate could see it, because
        # a wire carries no measured box.  These four logs seed both the
        # pre-fix ink and the ink that replaces it.
        def closure_log(name: str, rail: str, labels: str = "") -> Path:
            path = work / name
            path.write_text(
                "picture|id=1|lang=kernel\n"
                "atom|picture=1|cell=1-1|kind=dot\n"
                "kernel-boundary|picture=1|signature=\n"
                + rail + labels,
                encoding="utf-8",
            )
            return path

        detached = closure_log(
            "closure-detached.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-700000|"
            "points=-600000,0;-600000,-800000;2600000,-800000;2600000,0\n",
        )
        detached_status, detached_audit = audit_status(detached)
        detached_findings = [finding for finding in detached_audit.findings
                             if finding.rule == "closure-detached"]
        if detached_status != 1 or len(detached_findings) != 2:
            raise AssertionError(
                "audit accepted a closure drawn clear of the row it closes"
            )
        if not all("9.16pt short" in finding.msg
                   for finding in detached_findings):
            raise AssertionError(
                "the detached closure finding did not measure the gap: "
                + "; ".join(finding.msg for finding in detached_findings)
            )

        joined_rail = (
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-700000|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n"
        )
        joined = closure_log("closure-joined.tnlog", joined_rail)
        joined_status, joined_audit = audit_status(joined)
        if joined_status != 0 or joined_audit.findings:
            raise AssertionError(
                "audit rejected a closure that meets both of its row's ends"
            )

        # A joined rail can still run through the row it closes (#5766).  The
        # return that shipped after the closure was joined stood a fixed reach
        # from the row line, shorter than the open indices the row hangs on
        # that side, so each of them ended on the wire that contracts the row.
        # The record names the standoff those indices demand; a rail shallower
        # than it is reported with both distances.
        crossed = closure_log(
            "closure-crossed.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-1700000|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n",
        )
        crossed_status, crossed_audit = audit_status(crossed)
        crossed_findings = [finding for finding in crossed_audit.findings
                            if finding.rule == "closure-crossed"]
        if crossed_status != 1 or len(crossed_findings) != 1:
            raise AssertionError(
                "audit accepted a closure passing inside the open indices of "
                "the row it closes"
            )
        crossed_msg = crossed_findings[0].msg
        if ("12.21pt outside row 1 over part of it" not in crossed_msg
                or "need 25.94pt" not in crossed_msg):
            raise AssertionError(
                "the crossed-closure finding did not measure both distances: "
                + crossed_findings[0].msg
            )

        # The reading is over the row's own middle.  A rail that dips to its
        # standoff at one corner and runs back beside the row for the rest of
        # its length has cleared nothing, and a farthest-point reading would
        # call it clear.
        dipped = closure_log(
            "closure-dipped.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,-800000;-500000,-100000;"
            "2600000,-100000;2600000,0;2000000,0\n",
        )
        dipped_status, dipped_audit = audit_status(dipped)
        if dipped_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in dipped_audit.findings):
            raise AssertionError(
                "audit read a closure's farthest corner as its clearance"
            )

        # A rail exactly at its standoff is clear: the daylight the standoff
        # already carries is what separates the indices from the return.
        flush_status, flush_audit = audit_status(closure_log(
            "closure-flush.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n",
        ))
        if flush_status != 0 or flush_audit.findings:
            raise AssertionError(
                "audit rejected a closure standing exactly at its standoff"
            )

        # The standoff is signed by the side the return runs, so a rail
        # routed the whole distance on the wrong side is not clear of
        # anything -- in a multi-row picture it has gone through the row it
        # should have stood outside.
        flipped_status, flipped_audit = audit_status(closure_log(
            "closure-flipped.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,800000;2600000,800000;"
            "2600000,0;2000000,0\n",
        ))
        if flipped_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in flipped_audit.findings):
            raise AssertionError(
                "audit read a return routed on the wrong side as clear"
            )

        # A one-column row's two virtual ends resolve to one coordinate.  Its
        # row line is the level of that end and its span is that column, so
        # the covering is of a single column rather than of nothing.
        def single_column(name: str, run: int) -> Path:
            return closure_log(
                name,
                "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
                "west=0,0|east=0,0|stroke=0|clear=-800000|"
                f"points=0,0;-600000,0;-600000,{run};600000,{run};"
                "600000,0;0,0\n",
            )

        column_status, column_audit = audit_status(
            single_column("closure-one-column.tnlog", -800000)
        )
        if column_status != 0 or column_audit.findings:
            raise AssertionError(
                "audit rejected a one-column closure standing at its standoff"
            )
        shallow_status, shallow_audit = audit_status(
            single_column("closure-one-column-shallow.tnlog", -100000)
        )
        if shallow_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in shallow_audit.findings):
            raise AssertionError(
                "audit passed over a one-column closure inside its standoff"
            )

        # A zero standoff carries no side and no distance, so it is not a
        # standoff either.  It reads as a malformed value rather than as a
        # rail with nothing to clear.
        zero_status, zero_audit = audit_status(closure_log(
            "closure-zero-standoff.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=0|"
            "points=0,0;2000000,0\n",
        ))
        if zero_status != 1 or not any(
                finding.rule == "malformed-event"
                for finding in zero_audit.findings):
            raise AssertionError(
                "audit accepted a closure whose standoff was zero"
            )

        # A rail that runs the row at its standoff and then doubles back
        # inside it has put ink across the indices on the way home.
        back_status, back_audit = audit_status(closure_log(
            "closure-doubled-back.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,-100000;-600000,-100000;-600000,0;2000000,0\n",
        ))
        if back_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in back_audit.findings):
            raise AssertionError(
                "audit read a rail that doubled back inside its standoff "
                "as clear"
            )

        # A vertical detour toward the row at an interior column meets the
        # span at one x, like a lead does, but it is ink across the indices
        # rather than a wire leaving a virtual end.
        notch_status, notch_audit = audit_status(closure_log(
            "closure-interior-notch.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,-800000;1000000,-800000;"
            "1000000,-100000;1000000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n",
        ))
        if notch_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in notch_audit.findings):
            raise AssertionError(
                "audit exempted a vertical detour inside the row's own span"
            )

        # A one-column row's every stretch meets its span at that column, so
        # only the two leads are exempt there too: a second pass across the
        # same column is ink across the index, not a wire leaving an end.
        repeat_status, repeat_audit = audit_status(closure_log(
            "closure-one-column-repeat.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=0,0|stroke=0|clear=-800000|"
            "points=0,0;-600000,0;-600000,-800000;600000,-800000;"
            "600000,-100000;-600000,-100000;-600000,0;0,0\n",
        ))
        if repeat_status != 1 or not any(
                finding.rule == "closure-crossed"
                for finding in repeat_audit.findings):
            raise AssertionError(
                "audit exempted a second shallow pass over a one-column row"
            )

        # `arc` is the only word for a closure with no row line.  A flat rail
        # that named any other would take the rule out of its own reading.
        word_status, word_audit = audit_status(closure_log(
            "closure-word-standoff.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=none|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n",
        ))
        if word_status != 1 or not any(
                finding.rule == "malformed-event"
                for finding in word_audit.findings):
            raise AssertionError(
                "audit accepted a flat closure naming no standoff"
            )

        # A stream written before the standoff field existed is still a
        # stream: the field arrived on an existing kind, and section 7 of
        # TNLOG.md holds a reader to accepting both spellings.  The archived
        # record reads clean, and the standoff rule asks nothing of it.
        archived_status, archived_audit = audit_status(closure_log(
            "closure-archived.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n",
        ))
        if archived_status != 0 or archived_audit.findings:
            raise AssertionError(
                "audit rejected a closure record written before the standoff "
                "field existed: "
                + "; ".join(finding.msg for finding in archived_audit.findings)
            )

        # A ring's sector stands off no row line, so it names no standoff and
        # the rule has nothing to read.  Its ends are its two stations.
        arc_status, arc_audit = audit_status(closure_log(
            "closure-arc.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=arc|"
            "points=0,0;1000000,-100000;2000000,0\n",
        ))
        if arc_status != 0 or arc_audit.findings:
            raise AssertionError(
                "audit demanded a row-line standoff of a frame arc"
            )

        # The site name that stood on the return: a box straddling the rail's
        # own run, which is exactly where a label band shallower than the
        # trace reach put every name under a traced row.
        on_rail = closure_log(
            "closure-label-on-rail.tnlog",
            joined_rail,
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=400000|xmax=800000|ymin=-900000|ymax=-700000|"
            "shape=rect|radius=0\n",
        )
        on_rail_status, on_rail_audit = audit_status(on_rail)
        if on_rail_status != 1 or not any(
                finding.rule == "label-overlap"
                and "closure wrap-1 of row 1" in finding.msg
                for finding in on_rail_audit.findings):
            raise AssertionError(
                "audit accepted a label lying across a traced row's closure"
            )

        stepped = closure_log(
            "closure-label-stepped.tnlog",
            joined_rail,
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=400000|xmax=800000|ymin=-1200000|ymax=-1000000|"
            "shape=rect|radius=0\n",
        )
        stepped_status, stepped_audit = audit_status(stepped)
        if stepped_status != 0 or stepped_audit.findings:
            raise AssertionError(
                "audit rejected a label stepped clear of the closure"
            )

        malformed_rail = closure_log(
            "closure-malformed.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=-700000|points=0,0\n",
        )
        malformed_status, malformed_audit = audit_status(malformed_rail)
        if malformed_status != 1 or not any(
                finding.rule == "malformed-event"
                for finding in malformed_audit.findings):
            raise AssertionError("audit accepted a one-point closure contour")

        # A rail is a wire of nonzero width, and the record carries the half
        # stroke it is drawn with.  A name clearing the centreline by a
        # hundredth of a point stands on the ink either side of it.
        stroked_rail = (
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=18023|clear=-700000|"
            "points=0,0;-600000,0;-600000,-800000;2600000,-800000;"
            "2600000,0;2000000,0\n"
        )

        def stroked_log(name: str, ymin: int, ymax: int) -> Path:
            return closure_log(
                name, stroked_rail,
                "label-use|picture=1\n"
                "bbox|picture=1|class=label|id=1|owner=0|"
                f"xmin=400000|xmax=800000|ymin={ymin}|ymax={ymax}|"
                "shape=rect|radius=0\n",
            )

        on_stroke_status, on_stroke_audit = audit_status(
            stroked_log("closure-label-on-stroke.tnlog", -790000, -700000)
        )
        if on_stroke_status != 1 or not any(
                finding.rule == "label-overlap"
                and "closure wrap-1 of row 1" in finding.msg
                for finding in on_stroke_audit.findings):
            raise AssertionError(
                "audit read the closure as a centreline of no width"
            )

        off_stroke_status, off_stroke_audit = audit_status(
            stroked_log("closure-label-off-stroke.tnlog", -770000, -700000)
        )
        if off_stroke_status != 0 or off_stroke_audit.findings:
            raise AssertionError(
                "audit rejected a label standing clear of the closure stroke"
            )

        # A rounded name meets the rail on a corner arc alone: neither of the
        # two rectangles the round box decomposes into is touched, so only a
        # corner circle can report it.  `_roundrect_parts` hands those circles
        # back in doubled coordinates, and doubling them a second time put
        # every such corner four times its own reach away.
        corner_status, corner_audit = audit_status(closure_log(
            "closure-label-round-corner.tnlog",
            "closure-rail|picture=1|name=wrap-1|row=1|side=west-east|"
            "west=0,0|east=2000000,0|stroke=0|clear=400000|"
            "points=0,0;0,500000;400000,200000;2000000,0\n",
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|owner=0|"
            "xmin=0|xmax=1000000|ymin=250000|ymax=1250000|"
            "shape=roundrect|radius=400000\n",
        ))
        if corner_status != 1 or not any(
                finding.rule == "label-overlap"
                and "closure wrap-1 of row 1" in finding.msg
                for finding in corner_audit.findings):
            raise AssertionError(
                "audit accepted a closure clipping a rounded name's corner"
            )

        # A rail leaves the row's virtual end, which stands at the end site's
        # own centre, so its first stretch runs under that site's glyph.  A
        # name inscribed in and covered by that glyph is painted over the
        # rail; a name another glyph owns is not.
        def inscribed_log(name: str, label_owner: int) -> Path:
            return closure_log(
                name, stroked_rail,
                "ink-use|picture=1|class=glyph|id=1|shape=rect\n"
                "label-use|picture=1\n"
                "glyph-geometry|picture=1|owner=1|shape=rect|"
                "xmin=-700000|xmax=700000|ymin=-240000|ymax=240000|"
                "radius=0|stroke=18023|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
                f"bbox|picture=1|class=label|id=1|owner={label_owner}|"
                "xmin=-200000|xmax=200000|ymin=-160000|ymax=160000|"
                "shape=rect|radius=0\n",
            )

        covered_status, covered_audit = audit_status(
            inscribed_log("closure-label-inscribed.tnlog", 1)
        )
        if covered_status != 0 or covered_audit.findings:
            raise AssertionError(
                "audit reported a rail hidden under the glyph whose name it "
                "was measured against: "
                + "; ".join(finding.msg for finding in covered_audit.findings)
            )

        sibling_status, sibling_audit = audit_status(
            inscribed_log("closure-label-sibling.tnlog", 2)
        )
        if sibling_status != 1 or not any(
                finding.rule == "label-overlap"
                and "closure wrap-1 of row 1" in finding.msg
                for finding in sibling_audit.findings):
            raise AssertionError(
                "the covered-glyph exemption reached a name the glyph does "
                "not own"
            )

        glyph_bbox = work / "glyph-bbox.tnlog"
        glyph_bbox.write_text(
            "picture|id=1|lang=kernel\n"
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
