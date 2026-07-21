#!/usr/bin/env python3
"""Regression checks for measured typed-map label bands."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
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
\cs_set_protected:Npn \tenkz_cd_map_path:nnn #1#2#3
  {
    \int_gincr:N \g__tenkztest_map_int
    \draw[#1]
      (tenkzmap-\int_use:N\l__tenkzcd_fromrow_int-
        \int_use:N\l__tenkzcd_fromcol_int.base~east) --
      node[inner~sep=0pt, outer~sep=0pt, #2]
        (tenkz-map-label-\the\tenkz@pictureid-#3)
        {
          \exp_args:Nc \box_use:N
            { l__tenkzcd_map_label_#3_box }
        }
      (tenkzmap-\int_use:N\l__tenkzcd_torow_int-
        \int_use:N\l__tenkzcd_tocol_int.base~west);
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
  inner sep=0pt, outer sep=8pt, draw, line join=round, line width=4pt}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{10pt}{4pt}}
\end{tenkzcd}
\endgroup
\begingroup
\tikzset{tenkz every picture/.append style={rotate=180},
  tn label/.append style={
    inner sep=0pt, outer sep=8pt, draw, line join=round, line width=4pt}}
\begin{tenkzcd}[maps, species={channel}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{10pt}{4pt}}
\end{tenkzcd}
\endgroup
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
        wire_bounds: dict[int, list[tuple[int, int]]] = {1: [], 2: [], 3: []}
        for line in geometry_log.splitlines():
            if not line.startswith("bbox|"):
                continue
            fields = dict(field.split("=", 1) for field in line.split("|")[1:])
            picture = int(fields["picture"])
            bounds = (int(fields["xmin"]), int(fields["xmax"]))
            if fields["class"] == "label":
                if picture in visible_bounds:
                    raise AssertionError(
                        f"typed-map picture {picture} emitted duplicate label bboxes"
                    )
                visible_bounds[picture] = bounds
            elif fields["class"] == "wire" and picture in wire_bounds:
                wire_bounds[picture].append(bounds)
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
        for picture, label_bounds in visible_bounds.items():
            segments = sorted(wire_bounds[picture])
            if len(segments) != 2:
                raise AssertionError(
                    f"typed-map picture {picture} used full-wire fallback: "
                    f"{segments}"
                )
            endpoints = [endpoint for segment in segments for endpoint in segment]
            boundary_matches = {
                boundary for boundary in label_bounds
                if any(close(endpoint, boundary) for endpoint in endpoints)
            }
            segment_matches = [
                {
                    boundary for boundary in label_bounds
                    if any(close(endpoint, boundary) for endpoint in segment)
                }
                for segment in segments
            ]
            if (boundary_matches != set(label_bounds)
                    or any(len(matches) != 1 for matches in segment_matches)):
                raise AssertionError(
                    f"typed-map picture {picture} wire cuts disagree with "
                    f"visible label {label_bounds}: {segments}"
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
