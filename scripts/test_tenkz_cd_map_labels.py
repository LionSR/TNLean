#!/usr/bin/env python3
"""Regression checks for measured typed-map label bands."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\makeatletter
\newdimen\tenkzTestFloor
\newdimen\tenkzTestDaylight
\newdimen\tenkzTestOverride
\newcount\tenkzStatefulCalls
\tenkzStatefulCalls=0
\newcommand\tenkzStatefulLabel{%
  \global\advance\tenkzStatefulCalls by 1
  \ifnum\tenkzStatefulCalls=1
    \rule{24mm}{0pt}f%
  \else
    \rule{48mm}{0pt}f%
  \fi}
\begin{document}
\tenkzTestFloor=\tenkz@r@mapgap\tenkz@pitch
\tenkzTestDaylight=\tenkz@r@daylight\tenkz@pitch
\tenkzTestOverride=2mm
\typeout{TENKZ-FLOOR-SP=\number\tenkzTestFloor}
\typeout{TENKZ-DAYLIGHT-SP=\number\tenkzTestDaylight}
\typeout{TENKZ-OVERRIDE-SP=\number\tenkzTestOverride}
\makeatother

% Name the production label node and observe its live anchors immediately
% after the production path is drawn.  The wrapper changes no geometry.
\makeatletter
\ExplSyntaxOn
\int_new:N \g__tenkztest_map_int
\cs_new_eq:NN \tenkztest_map_path:nnn \tenkz_cd_map_path:nnn
\cs_set_protected:Npn \tenkz_cd_map_path:nnn #1#2#3
  {
    \int_gincr:N \g__tenkztest_map_int
    \tenkztest_map_path:nnn {#1}{#2}{#3}
    \path let
      \p1=(tenkzmap-\int_use:N\l__tenkzcd_fromrow_int-
        \int_use:N\l__tenkzcd_fromcol_int.base~east),
      \p2=(tenkz-map-label-\the\tenkz@pictureid-#3.west),
      \p3=(tenkz-map-label-\the\tenkz@pictureid-#3.east),
      \p4=(tenkzmap-\int_use:N\l__tenkzcd_torow_int-
        \int_use:N\l__tenkzcd_tocol_int.base~west)
    in \pgfextra
      {
        \typeout{TENKZ-MAP-\int_use:N\g__tenkztest_map_int-
          LEFT-SP=\number\dimexpr\x2-\x1\relax}
        \typeout{TENKZ-MAP-\int_use:N\g__tenkztest_map_int-
          BAND-SP=\number\dimexpr\x3-\x2\relax}
        \typeout{TENKZ-MAP-\int_use:N\g__tenkztest_map_int-
          RIGHT-SP=\number\dimexpr\x4-\x3\relax}
        \typeout{TENKZ-MAP-\int_use:N\g__tenkztest_map_int-
          GAP-SP=\number\dimexpr\x4-\x1\relax}
      };
  }
\ExplSyntaxOff
\makeatother

% An explicit, deliberately unsafe column separation remains authoritative.
\begin{tenkzcd}[maps, species={channel}, column sep=2mm]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{f}
\end{tenkzcd}

% A negative thin space leaves a nonempty, sub-floor label band and thus
% exercises the historical mapgap floor without changing visible geometry.
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{\!}
\end{tenkzcd}

% The rule makes this regression independent of font metrics; the genuine
% mathematical name following it still exercises superscripted label ink.
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{24mm}{0pt}\mathcal T_{\mathrm{seed}}^{(k,l,h)}}
\end{tenkzcd}

% Matrix passthrough keys cannot mutate the explicit tn-label skin used by
% the deferred map-name node.
\begin{tenkzcd}[
  maps,
  species={channel},
  tn label/.append style={inner sep=10pt}
]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{f}
\end{tenkzcd}

% Stateful label material must execute exactly once and the same boxed
% material must determine both measured spacing and production geometry.
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\tenkzStatefulLabel}
\end{tenkzcd}
\typeout{TENKZ-STATEFUL-FINAL-CALLS=\the\tenkzStatefulCalls}

% A globally appended label font must govern both materialization and the
% deferred node.  Compare its live band with an independently styled node.
\makeatletter
\begingroup
\tikzset{tn label/.append style={font=\tiny}}
\setbox0=\hbox{%
  \begin{tikzpicture}[baseline]
    \node[tn label, fill=tenkzPaper, outer sep=0pt]
      {$\tenkz@labelsize WWWW$};
  \end{tikzpicture}}
\typeout{TENKZ-FONT-BAND-SP=\number\wd0}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{WWWW}
\end{tenkzcd}
\endgroup
\makeatother
\end{document}
"""
GROUPED_SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  {\tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{24mm}{0pt}\mathcal T_{\mathrm{seed}}^{(k,l,h)}}}
\end{tenkzcd}
\end{document}
"""
MISASSOCIATED_SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \iffalse
    \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{skipped}
  \fi
  {\tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{hidden}}
\end{tenkzcd}
\end{document}
"""


def customized_typed_map_label(options: str) -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{tn label/.append style={%s}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{f}
\end{tenkzcd}
\end{document}
""" % options


TYPED_MAP_VISIBLE_GEOMETRY = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begingroup
\tikzset{tn label/.append style={
  inner sep=0pt, outer sep=8pt, draw=none}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{10pt}{4pt}}
\end{tenkzcd}
\endgroup
\begingroup
\tikzset{tn label/.append style={
  inner sep=0pt, outer sep=8pt, fill=tenkzPaper,
  draw, line join=round, line width=4pt}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{10pt}{4pt}}
\end{tenkzcd}
\endgroup
\begingroup
\tikzset{tenkz every picture/.append style={rotate=180},
  tn label/.append style={
    inner sep=0pt, outer sep=8pt, fill=tenkzPaper,
    draw, line join=round, line width=4pt}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{10pt}{4pt}}
\end{tenkzcd}
\endgroup
\end{document}
"""

TYPED_MAP_WIRE_WIDTHS = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begingroup
\tikzset{
  tn label/.append style={
    fill=tenkzPaper, draw, line join=round, line width=10pt},
  bond/.append style={line width=1pt},
  operator bond/.append style={line width=4pt}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, role=operator]{f}
\end{tenkzcd}
\endgroup
\tnset{species={channel}}
\begingroup
\tikzset{
  tn label/.append style={
    fill=tenkzPaper, draw, line join=round, line width=10pt},
  fused bond/.append style={line width=1pt, double distance=1pt},
  species channel bond/.append style={line width=2pt, double distance=3pt}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, fused, species=channel]{g}
\end{tenkzcd}
\endgroup
\begingroup
\tikzset{
  fused bond/.append style={double=blue},
  species channel bond/.append style={line width=2pt, double distance=3pt}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, fused, species=channel]{h}
\end{tenkzcd}
\endgroup
\begingroup
\tikzset{
  fused bond/.append style={draw opacity=.5},
  species channel bond/.append style={line width=2pt, double distance=3pt}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, fused, species=channel]{k}
\end{tenkzcd}
\endgroup
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{m}
\end{tenkzcd}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, fused, species=channel]{n}
\end{tenkzcd}
\makeatletter
\ExplSyntaxOn
\int_compare:nNnF {\g__tenkzcd_mapdrawuses_int} = {0}
  {\PackageError{tenkz test}{Map draw-use state leaked}{}}
\int_compare:nNnF {\g__tenkzcd_mapinvalid_int} = {0}
  {\PackageError{tenkz test}{Map invalid-state leaked}{}}
\dim_compare:nNnF {\g__tenkzcd_mapwire_outer_dim} = {0pt}
  {\PackageError{tenkz test}{Map width state leaked}{}}
\dim_compare:nNnF {\g__tenkzcd_mapwire_inner_dim} = {0pt}
  {\PackageError{tenkz test}{Map inner-width state leaked}{}}
\tl_set:Nx \l_tmpa_tl {\tenkz@liveblendmode}
\tl_if_eq:NnF \l_tmpa_tl {normal}
  {\PackageError{tenkz test}{Blend-mode state leaked}{}}
\bool_if:NT \g__tenkzcd_mapcaptureactive_bool
  {\PackageError{tenkz test}{Map capture marker leaked}{}}
\cs_if_eq:NNF \tenkz_cd_saved_map_usepath:n \scan_stop:
  {\PackageError{tenkz test}{Map path wrapper state leaked}{}}
\cs_if_eq:NNF \tenkz_cd_saved_map_sync: \scan_stop:
  {\PackageError{tenkz test}{Map transform wrapper state leaked}{}}
\ExplSyntaxOff
\makeatother
\end{document}
"""


def customized_typed_map_path(options: str) -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
\usetikzlibrary{fadings}
\begin{document}
\tikzset{operator bond/.append style={%s}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, role=operator]{f}
\end{tenkzcd}
\end{document}
""" % options


def customized_typed_map_picture(
        picture_options: str, map_options: str = ""
) -> str:
    return r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\tikzset{
  tenkz every picture/.append style={%s},
  operator bond/.append style={%s}}
\begin{tenkzcd}[maps]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, role=operator]{f}
\end{tenkzcd}
\end{document}
""" % (picture_options, map_options)

NESTED_TYPED_MAP_OWNERSHIP = r"""
\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkzcd}[maps, species={channel}]
  \tnpic[inline]{\tn[box]{A} & \tn[box]{B}} &
  \tnpic[inline]{\tn[box]{C} & \tn[box]{D}} \\
  \tnpic[inline]{\tn[box]{E} & \tn[box]{F}} &
  \tnpic[inline]{\tn[box]{G} & \tn[box]{H}}
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{f}
  \tnarrow[from={(2,1)}, to={(2,2)}, species=channel]{g}
\end{tenkzcd}
\makeatletter
\def\tenkzassertrelax#1{%
  \expandafter\ifx\csname #1\endcsname\relax\else
    \PackageError{tenkz test}{Audit ownership state '#1' was not released}{}%
  \fi}
\ifx\tenkz@auditinstallowner\relax\else
  \PackageError{tenkz test}{Per-node audit claimant leaked its scope}{}%
\fi
\tenkzassertrelax{tenkz@audittoken@tenkzmap-1-1}
\tenkzassertrelax{tenkz@audittoken@tenkzmap-1-2}
\tenkzassertrelax{tenkz@audittoken@tenkzmap-2-1}
\tenkzassertrelax{tenkz@audittoken@tenkzmap-2-2}
\def\tenkzassertpictureclean#1{%
  \tenkzassertrelax{tenkz@audittoken@tz#1-1-1}%
  \tenkzassertrelax{tenkz@audittoken@tz#1-1-2}%
  \tenkzassertrelax{tenkz@audittoken@tzbw#1}%
  \tenkzassertrelax{tenkz@audittoken@tzbe#1}%
  \tenkzassertrelax{tenkz@glyphsnaptoken@tzbw#1}%
  \tenkzassertrelax{tenkz@glyphsnaptoken@tzbe#1}}
\tenkzassertpictureclean{2}
\tenkzassertpictureclean{3}
\tenkzassertpictureclean{4}
\tenkzassertpictureclean{5}
\newcount\tenkztesttoken
\tenkztesttoken=1
\loop
  \edef\tenkztesttokenname{\the\tenkztesttoken}%
  \tenkzassertrelax{tenkz@auditowner@\tenkztesttokenname}%
  \tenkzassertrelax{tenkz@snapshotdone@\tenkztesttokenname}%
  \tenkzassertrelax{tenkz@glypharcflag@\tenkztesttokenname}%
  \tenkzassertrelax{tenkz@glypharc@\tenkztesttokenname}%
  \ifnum\tenkztesttoken<\tenkz@glyphsnapuid
    \advance\tenkztesttoken by 1
\repeat
\makeatother
\end{document}
"""


SCALAR = re.compile(r"TENKZ-(FLOOR|DAYLIGHT|OVERRIDE)-SP=(-?[0-9]+)")
MAP_VALUE = re.compile(
    r"TENKZ-MAP-([1-6])-(LEFT|BAND|RIGHT|GAP)-SP=(-?[0-9]+)"
)
STATEFUL_CALLS = re.compile(r"TENKZ-STATEFUL-FINAL-CALLS=([0-9]+)")
FONT_BAND = re.compile(r"TENKZ-FONT-BAND-SP=([0-9]+)")


def close(actual: int, expected: int, tolerance: int = 2) -> bool:
    return abs(actual - expected) <= tolerance


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1

    with tempfile.TemporaryDirectory(prefix="tenkz-cd-map-labels-") as tmp:
        work = Path(tmp)
        tex = work / "typed-map-label-bands.tex"
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
            timeout=120,
        )
        if run.returncode:
            print(run.stdout)
            print("FAIL: typed-map label-band fixture did not compile")
            return 1

        grouped_tex = work / "grouped-typed-map-label.tex"
        grouped_tex.write_text(GROUPED_SOURCE, encoding="utf-8")
        grouped_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", grouped_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if grouped_run.returncode == 0:
            raise AssertionError("grouped typed-map declaration compiled silently")
        if "Typed-map declarations must be literal" not in grouped_run.stdout:
            print(grouped_run.stdout)
            raise AssertionError("grouped declaration failed without the grammar error")

        misassociated_tex = work / "misassociated-typed-map-label.tex"
        misassociated_tex.write_text(MISASSOCIATED_SOURCE, encoding="utf-8")
        misassociated_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", misassociated_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if misassociated_run.returncode == 0:
            raise AssertionError("misassociated typed-map declaration compiled silently")
        if "Typed-map declarations must be literal" not in misassociated_run.stdout:
            print(misassociated_run.stdout)
            raise AssertionError(
                "misassociated declaration failed without the grammar error"
            )

        for filename, options, diagnostic in (
            ("miter-typed-map-label.tex", "draw, line join=miter",
             "non-round line join"),
            ("round-typed-map-label.tex", "circle",
             "unsupported live shape"),
            ("transparent-typed-map-label.tex", "fill opacity=0",
             "zero fill opacity"),
            ("translucent-typed-map-label.tex", "fill opacity=.5",
             "background is not opaque"),
            ("zero-text-typed-map-label.tex", "text opacity=0",
             "zero text opacity"),
        ):
            failure_tex = work / filename
            failure_tex.write_text(
                customized_typed_map_label(options), encoding="utf-8"
            )
            failure_run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error",
                 failure_tex.name],
                cwd=work,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
            if failure_run.returncode == 0 or diagnostic not in failure_run.stdout:
                raise AssertionError(
                    f"typed-map label accepted {options!r}: "
                    + failure_run.stdout[-1000:]
                )

        for filename, options, diagnostic in (
            ("dashed-typed-map-path.tex", "dashed", "has a dashed stroke"),
            ("blend-typed-map-path.tex", "blend mode=multiply",
             "has a non-normal blend mode"),
            ("transparent-typed-map-path.tex", "draw opacity=0",
             "has zero draw opacity"),
            ("translated-typed-map-path.tex",
             "transform canvas={yshift=10pt}", "path-local transform"),
            ("rotated-typed-map-path.tex", "rotate=15", "path-local transform"),
            ("shortened-typed-map-path.tex", "shorten <=2pt",
             "has nonzero shortening"),
            ("end-shortened-typed-map-path.tex", "shorten >=2pt",
             "has nonzero shortening"),
            ("round-cap-typed-map-path.tex", "line cap=round",
             "changes the line cap"),
            ("rect-cap-typed-map-path.tex", "line cap=rect",
             "changes the line cap"),
            ("decorated-typed-map-path.tex", "decorate", "has a decoration"),
            ("preaction-typed-map-path.tex", "preaction={draw=red}",
             "live draw uses"),
            ("postaction-typed-map-path.tex", "postaction={draw=red}",
             "live draw uses"),
            ("inserted-typed-map-path.tex",
             "insert path={(0,1cm)--(1cm,1cm)}",
             "is not one horizontal line"),
            ("rounded-typed-map-path.tex", "rounded corners=2pt",
             "is not one horizontal line"),
            ("arrowed-typed-map-path.tex", "->", "has arrow tips"),
            ("zero-width-typed-map-path.tex", "line width=0pt",
             "has nonpositive live width"),
            ("negative-width-typed-map-path.tex", "line width=-1pt",
             "has nonpositive live width"),
            ("clipped-typed-map-path.tex", "clip",
             "Extra options not allowed for clipping"),
            ("path-faded-typed-map-path.tex", "path fading=east",
             "has path fading"),
            ("scope-faded-typed-map-path.tex", "scope fading=east",
             "has scope fading"),
            ("pictured-typed-map-path.tex", "path picture={\\fill (0,0) circle (1pt);}",
             "has a path picture"),
        ):
            failure_tex = work / filename
            failure_tex.write_text(
                customized_typed_map_path(options), encoding="utf-8"
            )
            failure_run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error",
                 failure_tex.name],
                cwd=work,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=120,
            )
            if failure_run.returncode == 0 or diagnostic not in failure_run.stdout:
                raise AssertionError(
                    f"typed-map path accepted {options!r}: "
                    + failure_run.stdout[-1000:]
                )

        inherited_blend_tex = work / "inherited-blend-typed-map-path.tex"
        inherited_blend_tex.write_text(
            customized_typed_map_picture("blend mode=multiply"),
            encoding="utf-8",
        )
        inherited_blend_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             inherited_blend_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if (inherited_blend_run.returncode == 0
                or "has a non-normal blend mode"
                not in inherited_blend_run.stdout):
            raise AssertionError(
                "typed-map path accepted inherited multiply blending: "
                + inherited_blend_run.stdout[-1000:]
            )

        restored_blend_tex = work / "restored-blend-typed-map-path.tex"
        restored_blend_tex.write_text(
            customized_typed_map_picture(
                "blend mode=multiply", "blend mode=normal"
            ),
            encoding="utf-8",
        )
        restored_blend_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             restored_blend_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if restored_blend_run.returncode:
            raise AssertionError(
                "later map style failed to restore normal blending: "
                + restored_blend_run.stdout[-1000:]
            )

        control_tex = work / "restyled-typed-map-path.tex"
        control_tex.write_text(
            customized_typed_map_path(
                "draw=blue, line width=2pt, line cap=butt"
            ),
            encoding="utf-8",
        )
        control_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             control_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if control_run.returncode:
            raise AssertionError(
                "typed-map path rejected supported append restyling: "
                + control_run.stdout[-1000:]
            )

        geometry_tex = work / "typed-map-visible-geometry.tex"
        geometry_tex.write_text(TYPED_MAP_VISIBLE_GEOMETRY, encoding="utf-8")
        geometry_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             geometry_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if geometry_run.returncode:
            raise AssertionError(
                "typed-map visible-geometry fixture did not compile: "
                + geometry_run.stdout[-1000:]
            )
        geometry_log = (work / "typed-map-visible-geometry.tnlog").read_text(
            encoding="utf-8"
        )
        visible_bounds: dict[int, tuple[int, int]] = {}
        wire_geometry: dict[int, dict[str, str]] = {}
        for line in geometry_log.splitlines():
            if not (line.startswith("bbox|")
                    or line.startswith("wire-geometry|")):
                continue
            fields = dict(field.split("=", 1) for field in line.split("|")[1:])
            picture = int(fields["picture"])
            if line.startswith("bbox|") and fields["class"] == "label":
                bounds = (int(fields["xmin"]), int(fields["xmax"]))
                if picture in visible_bounds:
                    raise AssertionError(
                        f"typed-map picture {picture} emitted duplicate label bboxes"
                    )
                visible_bounds[picture] = bounds
            elif line.startswith("wire-geometry|"):
                if picture in wire_geometry:
                    raise AssertionError(
                        f"typed-map picture {picture} emitted duplicate wire geometry"
                    )
                wire_geometry[picture] = fields
        for picture in (1, 2, 3):
            if geometry_log.count(f"label-use|picture={picture}") != 1:
                raise AssertionError(
                    f"typed-map picture {picture} lost or duplicated label-use"
                )
        expected_widths = {1: 10 * 65536, 2: 14 * 65536, 3: 14 * 65536}
        visible_widths = {
            picture: xmax - xmin
            for picture, (xmin, xmax) in visible_bounds.items()
        }
        if visible_bounds.keys() != expected_widths.keys() or any(
                not close(visible_widths[picture], expected)
                for picture, expected in expected_widths.items()):
            raise AssertionError(
                "typed-map bboxes retained outer sep or omitted round stroke: "
                f"actual={visible_widths}, expected={expected_widths}"
            )
        if wire_geometry.keys() != visible_bounds.keys():
            raise AssertionError(
                f"typed-map wire geometry census is incomplete: {wire_geometry}"
            )
        for picture, label_bounds in visible_bounds.items():
            wire = wire_geometry[picture]
            cut_bounds = (int(wire["cut-xmin"]), int(wire["cut-xmax"]))
            if (wire.get("shape") != "rect-minus-label"
                    or cut_bounds != label_bounds):
                raise AssertionError(
                    f"typed-map picture {picture} lost exact label subtraction: "
                    f"{wire}"
                )
        rect_wire = wire_geometry[1]
        outer_width = int(rect_wire["xmax"]) - int(rect_wire["xmin"])
        outer_height = int(rect_wire["outer"])
        center_y = int(rect_wire["y"])
        wire_ymin = Fraction(2 * center_y - outer_height, 2)
        wire_ymax = Fraction(2 * center_y + outer_height, 2)
        cut_width = max(
            0,
            min(int(rect_wire["xmax"]), int(rect_wire["cut-xmax"]))
            - max(int(rect_wire["xmin"]), int(rect_wire["cut-xmin"])),
        )
        cut_height = max(
            0,
            min(wire_ymax, int(rect_wire["cut-ymax"]))
            - max(wire_ymin, int(rect_wire["cut-ymin"])),
        )
        visible_area = outer_width * outer_height - cut_width * cut_height
        left_right_area = (outer_width - cut_width) * outer_height
        if (rect_wire.get("cut-shape") != "rect"
                or visible_area <= left_right_area):
            raise AssertionError(
                "rect label subtraction dropped the partially visible middle band"
            )
        for picture in (2, 3):
            if (wire_geometry[picture].get("cut-shape") != "roundrect"
                    or int(wire_geometry[picture]["cut-radius"]) <= 0):
                raise AssertionError(
                    f"round label cut lost exact curved support: "
                    f"{wire_geometry[picture]}"
                )

        widths_tex = work / "typed-map-wire-widths.tex"
        widths_tex.write_text(TYPED_MAP_WIRE_WIDTHS, encoding="utf-8")
        widths_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error",
             widths_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if widths_run.returncode:
            raise AssertionError(
                "typed-map live-width fixture did not compile: "
                + widths_run.stdout[-1000:]
            )
        widths_log = (work / "typed-map-wire-widths.tnlog").read_text(
            encoding="utf-8"
        )
        wire_heights: dict[int, set[int]] = {
            picture: set() for picture in range(1, 7)
        }
        wire_inners: dict[int, set[int]] = {
            picture: set() for picture in range(1, 7)
        }
        label_radii: dict[int, set[int]] = {
            picture: set() for picture in range(1, 7)
        }
        for line in widths_log.splitlines():
            if not (line.startswith("bbox|")
                    or line.startswith("wire-geometry|")):
                continue
            fields = dict(field.split("=", 1) for field in line.split("|")[1:])
            picture = int(fields["picture"])
            if line.startswith("wire-geometry|") and picture in wire_heights:
                wire_heights[picture].add(
                    int(fields["outer"])
                )
                wire_inners[picture].add(int(fields["inner"]))
            elif (line.startswith("bbox|") and fields["class"] == "label"
                  and picture in label_radii):
                label_radii[picture].add(int(fields["radius"]))
        expected_heights = {
            1: 4 * 65536,
            2: 7 * 65536,
            3: 7 * 65536,
            4: 7 * 65536,
        }
        if any(len(wire_heights[picture]) != 1
               or not close(next(iter(wire_heights[picture])), expected)
               for picture, expected in expected_heights.items()):
            raise AssertionError(
                "typed-map wire bboxes ignored live role/species style order: "
                f"{wire_heights}"
            )
        exact_default_widths = {5: 36045, 6: 144180}
        if any(wire_heights[picture] != {expected}
               for picture, expected in exact_default_widths.items()):
            raise AssertionError(
                "default typed-map widths lost odd-sp exactness: "
                f"{wire_heights}"
            )
        expected_inners = {1: 0, 2: 3 * 65536, 3: 0, 4: 0}
        if any(wire_inners[picture] != {expected}
               for picture, expected in expected_inners.items()):
            raise AssertionError(
                "typed-map wire geometry lost its live inner gap: "
                f"{wire_inners}"
            )
        exact_default_inners = {5: 0, 6: 72090}
        if any(wire_inners[picture] != {expected}
               for picture, expected in exact_default_inners.items()):
            raise AssertionError(
                "default fused typed-map inner gap lost exact width: "
                f"{wire_inners}"
            )
        fused_outer = next(iter(wire_heights[2]))
        fused_inner = next(iter(wire_inners[2]))
        if not close((fused_outer - fused_inner) // 2, 2 * 65536):
            raise AssertionError(
                "fused typed-map rails are not two exact 2pt bands: "
                f"outer={fused_outer}, inner={fused_inner}"
            )
        if (label_radii[1] != {5 * 65536}
                or label_radii[2] != {5 * 65536}):
            raise AssertionError(
                "drawn typed-map label control lost its independent stroke: "
                f"{label_radii}"
            )

        nested_tex = work / "nested-typed-map-ownership.tex"
        nested_tex.write_text(NESTED_TYPED_MAP_OWNERSHIP, encoding="utf-8")
        nested_run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", nested_tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=120,
        )
        if nested_run.returncode:
            raise AssertionError(
                "nested typed-map ownership fixture did not compile: "
                + nested_run.stdout[-1000:]
            )
        nested_log = (work / "nested-typed-map-ownership.tnlog").read_text(
            encoding="utf-8"
        )
        outer_glyphs = [
            line for line in nested_log.splitlines()
            if line.startswith("glyph-geometry|picture=1|")
        ]
        if len(outer_glyphs) != 4 or any("|shape=rect|" not in line
                                         for line in outer_glyphs):
            raise AssertionError(
                "nested typed-map cells did not retain four owned rectangles: "
                + repr(outer_glyphs)
            )

    scalars = {name: int(value) for name, value in SCALAR.findall(run.stdout)}
    maps = {index: {} for index in range(1, 7)}
    for index, name, value in MAP_VALUE.findall(run.stdout):
        maps[int(index)][name] = int(value)
    if scalars.keys() != {"FLOOR", "DAYLIGHT", "OVERRIDE"}:
        raise AssertionError(f"missing typed-map scalar measurements: {scalars}")
    if any(row.keys() != {"LEFT", "BAND", "RIGHT", "GAP"}
           for row in maps.values()):
        raise AssertionError(f"missing live typed-map anchor measurements: {maps}")
    stateful_calls = STATEFUL_CALLS.findall(run.stdout)
    if stateful_calls != ["1"]:
        raise AssertionError(
            f"stateful typed-map label executed {stateful_calls!r}, expected once"
        )
    font_bands = FONT_BAND.findall(run.stdout)
    if len(font_bands) != 1:
        raise AssertionError(f"missing styled label-band reference: {font_bands}")

    # Map 1 deliberately exercises an unsafe explicit override; every
    # automatically resolved map must retain daylight on both sides.
    for index in (3, 4, 5, 6):
        row = maps[index]
        for side in ("LEFT", "RIGHT"):
            if row[side] + 2 < scalars["DAYLIGHT"]:
                raise AssertionError(
                    f"map {index} {side.lower()} clearance {row[side]}sp "
                    f"is below daylight {scalars['DAYLIGHT']}sp"
                )
    if not close(maps[1]["GAP"], scalars["OVERRIDE"]):
        raise AssertionError(
            "explicit column sep did not remain authoritative: "
            f"actual={maps[1]['GAP']}sp expected={scalars['OVERRIDE']}sp"
        )
    if not close(maps[2]["GAP"], scalars["FLOOR"]):
        raise AssertionError(
            "sub-floor label changed the historical mapgap geometry: "
            f"actual={maps[2]['GAP']}sp expected={scalars['FLOOR']}sp"
        )
    expected_wide = maps[3]["BAND"] + 2 * scalars["DAYLIGHT"]
    if not close(maps[3]["GAP"], expected_wide):
        raise AssertionError(
            "wide map gap is not its live label band plus two daylights: "
            f"actual={maps[3]['GAP']}sp expected={expected_wide}sp"
        )
    expected_styled = max(
        scalars["FLOOR"], maps[4]["BAND"] + 2 * scalars["DAYLIGHT"]
    )
    if not close(maps[4]["GAP"], expected_styled):
        raise AssertionError(
            "matrix passthrough style leaked into the deferred map label: "
            f"actual={maps[4]['GAP']}sp expected={expected_styled}sp"
        )
    expected_stateful = maps[5]["BAND"] + 2 * scalars["DAYLIGHT"]
    if not close(maps[5]["GAP"], expected_stateful):
        raise AssertionError(
            "stateful map measured band differs from its production band: "
            f"actual={maps[5]['GAP']}sp expected={expected_stateful}sp"
        )
    if not close(maps[6]["BAND"], int(font_bands[0])):
        raise AssertionError(
            "appended tn-label font did not govern the materialized band: "
            f"actual={maps[6]['BAND']}sp expected={font_bands[0]}sp"
        )
    print(
        "PASS: typed-map labels materialize once with the effective font, bind "
        "to literal declarations, retain explicit/floor geometry, and clear "
        "adjacent objects by daylight"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
