#!/usr/bin/env python3
"""Regression check for measured label/glyph/wire overlap events."""

from __future__ import annotations

import io
import os
import shutil
import subprocess
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

from tenkz_audit import Audit


ROOT = Path(__file__).resolve().parents[1]
SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
% Deliberately unsafe: the explicit separation overrides the measured label band.
\begin{tenkzcd}[maps, species={channel}, column sep=2mm]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{18mm}{0pt}\mathcal T}
\end{tenkzcd}

% Safe: production spacing is derived from the same materialized label box.
% Matrix passthrough may change the live object shape; measurement follows it.
\begin{tenkzcd}[maps, species={channel}, nodes={circle}]
  A & B
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]
    {\rule{18mm}{0pt}\mathcal T}
\end{tenkzcd}

% Shared style capture covers unnamed production labels in every core tier.
\begin{tenkzfree}
  \tnput[box]{a}{(0,0)}{A}
  \tnput[box]{b}{(20mm,0)}{}
  \tnjoin[label=f]{a.east}{b.west}
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


def audit_status(path: Path) -> tuple[int, Audit]:
    audit = Audit(path, None)
    with redirect_stdout(io.StringIO()):
        status = audit.run()
    return status, audit


def main() -> int:
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
        overlap_pictures = {
            picture_id for picture_id in (1, 7)
            if any(f"picture {picture_id}" in finding.msg for finding in overlaps)
        }
        if overlap_pictures != {1, 7}:
            raise AssertionError(
                "overlap findings missed an unsafe picture: "
                + "; ".join(finding.msg for finding in overlaps)
            )
        if any(f"picture {picture_id}" in finding.msg
               for finding in overlaps for picture_id in (2, 3, 4, 5, 6)):
            raise AssertionError("audit rejected a safely spaced fixture")

        for picture_id in (1, 2):
            bbox_classes = {
                event.attrs.get("class") for event in audit.events(picture_id)
                if event.kind == "bbox"
            }
            geometry_kinds = {event.kind for event in audit.events(picture_id)}
            if bbox_classes != {"label", "wire"} or "glyph-geometry" not in geometry_kinds:
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

        reshaped = {
            event.attrs.get("shape") for event in audit.events(7)
            if event.kind == "glyph-geometry"
        }
        if reshaped != {"rect"}:
            raise AssertionError(
                f"final rectangle override emitted stale geometry: {reshaped}"
            )

        corner_events = [
            event for event in audit.events(8)
            if event.kind == "glyph-geometry"
        ]
        corner_shapes = [event.attrs.get("shape") for event in corner_events]
        if corner_shapes != ["rect", "roundrect"]:
            raise AssertionError(
                f"final corner overrides emitted stale geometry: {corner_shapes}"
            )
        if corner_events[0].attrs.get("radius") != "0":
            raise AssertionError("sharp pill retained its declared corner radius")
        if corner_events[1].attrs.get("radius") != str(round(1.5 * 65536)):
            raise AssertionError("rounded box did not emit its live corner radius")

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

        exact = work / "exact-shapes.tnlog"
        exact.write_text(
            "picture|id=1|lang=free\n"
            "atom|picture=1|name=a|kind=dot\n"
            "label-use|picture=1\n"
            "bbox|picture=1|class=label|id=1|xmin=8|xmax=10|ymin=8|ymax=10\n"
            "ink-use|picture=1|class=glyph|id=1|shape=circle\n"
            "glyph-geometry|picture=1|owner=1|shape=circle|xmin=-10|xmax=10|"
            "ymin=-10|ymax=10|radius=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=2|shape=roundrect\n"
            "glyph-geometry|picture=1|owner=2|shape=roundrect|xmin=20|xmax=40|"
            "ymin=20|ymax=40|radius=8|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0\n"
            "ink-use|picture=1|class=glyph|id=3|shape=triangle\n"
            "glyph-geometry|picture=1|owner=3|shape=triangle|xmin=50|xmax=70|"
            "ymin=0|ymax=20|radius=0|x1=70|y1=10|x2=50|y2=20|x3=50|y3=0\n",
            encoding="utf-8",
        )
        exact_status, exact_audit = audit_status(exact)
        if exact_status != 0:
            raise AssertionError(
                "exact geometry rejected bbox-only corner near misses: "
                + "; ".join(finding.msg for finding in exact_audit.findings)
            )

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
            if "\\node[tn~label" not in excerpt:
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
