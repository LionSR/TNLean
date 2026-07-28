#!/usr/bin/env python3
"""Focused semantic-audit regressions for kernel event streams."""

from __future__ import annotations

import tempfile
from pathlib import Path

from tenkz_audit import Audit


GOOD_LOG = """\
picture|id=k1|lang=kernel
wire|id=wire-1|from=addr-1|kind=string|name=a|to=addr-2
wire|id=wire-2|cross=under at crossing of a and b|from=addr-3|kind=string|name=b|to=addr-4
wire|id=wire-3|from=addr-5|host=atom-1|kind=pairing|name=skin-atom-1-1|origin=skin|route=arc|species=shift|to=addr-6
mark|id=mark-3|form=label
kernel-boundary|signature=open:e, open:w
string|id=a|kind=open|pts=2
string|id=b|kind=open|pts=2
string|id=c|kind=wind|pts=2
string|id=d|kind=around|pts=2
stringcross|under=b|over=a|hits=1
check|relation=1|result=equal|signature=open:e, open:w
"""


def audit_log(log: str, source: str | None = None) -> Audit:
    with tempfile.TemporaryDirectory(prefix="tenkz_kernel_audit_") as tmp:
        work = Path(tmp)
        log_path = work / "fixture.tnlog"
        log_path.write_text(log, encoding="utf-8")
        tex_path = None
        if source is not None:
            tex_path = work / "fixture.tex"
            tex_path.write_text(source, encoding="utf-8")
        audit = Audit(log_path, tex_path)
        audit.parse_log()
        audit.link_tex()
        audit.check_empty_pictures()
        audit.check_dialects()
        audit.check_kernel_crossings()
        audit.check_kernel_checks()
        audit.check_bbox_coverage()
        audit.check_label_overlaps()
        audit.check_equation_boundaries()
        return audit


def main() -> int:
    good = audit_log(GOOD_LOG)
    assert not good.findings, good.findings
    assert [event.kind for event in good.pictures[0].content()] == [
        "wire",
        "wire",
        "wire",
        "mark",
        "string",
        "string",
        "string",
        "string",
        "stringcross",
    ]
    assert good.pictures[0].kernel_boundary() == ("open:e", "open:w")

    missed = audit_log(
        GOOD_LOG.replace(
            "stringcross|under=b|over=a|hits=1",
            "stringcross|under=a|over=b|hits=0",
        )
    )
    missed_rules = [finding.rule for finding in missed.findings]
    assert missed_rules.count("kernel-crossing") >= 2, missed.findings

    empty = audit_log(
        "picture|id=k1|lang=kernel\nkernel-boundary|signature=\n"
    )
    assert "empty-picture" in [finding.rule for finding in empty.findings]

    equation_source = (
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n"
        "$\\;=\\;$\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
    )
    equation_log = """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=open:w
picture|id=k2|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=phys:up
"""
    equation = audit_log(equation_log, equation_source)
    assert "eq-boundary-mismatch" in [
        finding.rule for finding in equation.findings
    ]

    overlap_log = """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=
label-use|picture=k1
bbox|picture=k1|class=label|id=1|owner=0|xmin=0|xmax=10|ymin=0|ymax=10|shape=rect|radius=0
ink-use|picture=k1|class=glyph|id=1|shape=rect
glyph-geometry|picture=k1|owner=1|shape=rect|xmin=5|xmax=15|ymin=5|ymax=15|radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0
"""
    overlap = audit_log(overlap_log)
    assert "label-overlap" in [finding.rule for finding in overlap.findings]

    print("tenkz-kernel-audit: parser, crossings, boundaries, and geometry passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
