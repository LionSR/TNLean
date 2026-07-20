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
\begin{tenkzcd}[maps, species={channel}]
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
\end{document}
"""


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
        if not overlaps or not all("picture 1" in finding.msg for finding in overlaps):
            raise AssertionError(
                "overlap finding was not confined to the unsafe picture: "
                + "; ".join(finding.msg for finding in overlaps)
            )
        if any(f"picture {picture_id}" in finding.msg
               for finding in overlaps for picture_id in (2, 3, 4, 5)):
            raise AssertionError("audit rejected a safely spaced fixture")

        for picture_id in (1, 2):
            classes = {
                event.attrs.get("class")
                for event in audit.events(picture_id)
                if event.kind == "bbox"
            }
            if classes != {"label", "glyph", "wire"}:
                raise AssertionError(
                    f"picture {picture_id} emitted incomplete bbox classes: {classes}"
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
        missing_audit = Audit(missing, None)
        with redirect_stdout(io.StringIO()):
            missing_status = missing_audit.run()
        if missing_status != 1 or not any(
                finding.rule == "bbox-coverage"
                for finding in missing_audit.findings):
            raise AssertionError("audit accepted an unmeasured library label use")

    print("PASS: measured overlap rejects unsafe and accepts safe typed-map labels")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
