#!/usr/bin/env python3
"""Focused semantic-audit regressions for kernel event streams."""

from __future__ import annotations

import tempfile
from pathlib import Path

from tenkz_audit import Audit, same_equation


GOOD_LOG = """\
picture|id=k1|lang=kernel|scope=1
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
check|scope=1|relation=1|result=equal|signature=open:e, open:w
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
    assert not same_equation(r"\def\foo{a=b}")
    assert not same_equation(r"\text{a=b}")
    assert same_equation(r"\;=\;\delta_{i,j}\;")

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

    pairing_cross = audit_log(
        """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn|name=host
wire|id=wire-2|cross=under at crossing of self and probe|from=addr-1|host=atom-1|kind=pairing|name=skin-atom-1-1|origin=skin|to=addr-2
wire|id=wire-3|from=addr-3|kind=string|name=probe|to=addr-4
kernel-boundary|signature=
string|id=probe|kind=open|pts=2
stringcross|under=skin-atom-1-1|over=probe|hits=1
"""
    )
    assert not pairing_cross.findings, pairing_cross.findings

    pairing_operand = audit_log(
        """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn|name=host
wire|id=wire-2|from=addr-1|host=atom-1|kind=pairing|name=skin-atom-1-1|origin=skin|to=addr-2
wire|id=wire-3|cross=over at crossing of self and pairing 1 of host|from=addr-3|kind=string|to=addr-4
kernel-boundary|signature=
string|id=wire-3|kind=open|pts=2
stringcross|under=skin-atom-1-1|over=wire-3|hits=1
"""
    )
    assert not pairing_operand.findings, pairing_operand.findings

    inherited_pairing_log = """\
picture|id=k1|lang=kernel
wire|id=wire-1|from=addr-1|host=atom-1|kind=pairing|name=skin-atom-1-1|origin=skin|to=addr-2
wire|id=wire-2|from=addr-3|host=atom-1|kind=pairing|name=skin-atom-1-2|origin=skin|to=addr-4
kernel-boundary|signature=
stringcross|under=skin-atom-1-1|over=skin-atom-1-2|hits=1
"""
    inherited_pairing_cross = audit_log(inherited_pairing_log)
    assert not inherited_pairing_cross.findings, inherited_pairing_cross.findings
    reversed_pairing_cross = audit_log(
        inherited_pairing_log.replace(
            "under=skin-atom-1-1|over=skin-atom-1-2",
            "under=skin-atom-1-2|over=skin-atom-1-1",
        )
    )
    assert "kernel-crossing" in [
        finding.rule for finding in reversed_pairing_cross.findings
    ]

    unrelated_pairing_cross = audit_log(
        """\
picture|id=k1|lang=kernel
wire|id=wire-1|from=addr-1|host=atom-1|kind=pairing|name=skin-atom-1-1|origin=skin|to=addr-2
wire|id=wire-2|from=addr-3|host=atom-2|kind=pairing|name=skin-atom-2-1|origin=skin|to=addr-4
kernel-boundary|signature=
stringcross|under=skin-atom-1-1|over=skin-atom-2-1|hits=1
"""
    )
    assert "kernel-crossing" in [
        finding.rule for finding in unrelated_pairing_cross.findings
    ]

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
    equation_mismatches = [
        finding for finding in equation.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(equation_mismatches) == 1, equation.findings
    assert equation_mismatches[0].severity == "HARD", equation_mismatches

    matching_physical_equation = audit_log(
        equation_log.replace(
            "kernel-boundary|signature=open:w",
            "kernel-boundary|signature=phys:up",
        ),
        equation_source,
    )
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in matching_physical_equation.findings
    ]

    rotated_open_equation = audit_log(
        equation_log.replace("open:w", "edge:n").replace("phys:up", "edge:e"),
        equation_source,
    )
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in rotated_open_equation.findings
    ]

    mixed_virtual_equation = audit_log(
        equation_log.replace("phys:up", "edge:e"),
        equation_source,
    )
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in mixed_virtual_equation.findings
    ]

    weighted_open_equation = audit_log(
        equation_log.replace("open:w", "open:w:double").replace(
            "phys:up", "open:e:single"
        ),
        equation_source,
    )
    weighted_mismatches = [
        finding for finding in weighted_open_equation.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(weighted_mismatches) == 1, weighted_open_equation.findings
    assert weighted_mismatches[0].severity == "HARD", weighted_mismatches

    equivalent_bundle_equation = audit_log(
        equation_log.replace("open:w", "edge:n:bundle=3").replace(
            "phys:up", "edge:e:bundle = 3"
        ),
        equation_source,
    )
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in equivalent_bundle_equation.findings
    ]

    different_bundle_equation = audit_log(
        equation_log.replace("open:w", "edge:n:bundle=3").replace(
            "phys:up", "edge:e:bundle = 4"
        ),
        equation_source,
    )
    assert "eq-boundary-mismatch" in [
        finding.rule for finding in different_bundle_equation.findings
    ]

    checked_equation_source = (
        "\\begin{tenkzeq}[check={signature, modulo=bundles}]\n"
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n"
        "=\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkzeq}\n"
    )
    checked_equation_log = (
        equation_log.replace("|lang=kernel", "|lang=kernel|scope=1")
        .replace("open:w", "edge:w:bundle=3")
        .replace("phys:up", "open:e")
        + "check|scope=1|relation=1|result=equal|modulo=bundles|signature=edge:e\n"
    )
    checked_equation = audit_log(checked_equation_log, checked_equation_source)
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in checked_equation.findings
    ]

    opted_out_equation = audit_log(
        "check|scope=1|relation=1|result=off|reason=documented\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}",
            "check={signature, off={1: documented}}",
        ),
    )
    assert "eq-boundary-mismatch" not in [
        finding.rule for finding in opted_out_equation.findings
    ]

    undeclared_opt_out = audit_log(
        "check|scope=1|relation=1|result=off|reason=stale\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}", "check={signature}"
        ),
    )
    assert "eq-boundary-mismatch" in [
        finding.rule for finding in undeclared_opt_out.findings
    ]

    surplus_opt_out = audit_log(
        "check|scope=1|relation=1|result=off|reason=documented\n"
        "check|scope=1|relation=2|result=equal|signature=\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}",
            "check={signature, off={1: documented}}",
        ),
    )
    assert "eq-boundary-mismatch" in [
        finding.rule for finding in surplus_opt_out.findings
    ]

    duplicate_opt_out = audit_log(
        "check|scope=1|relation=1|result=off|reason=documented\n"
        "check|scope=1|relation=1|result=equal|signature=\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}",
            "check={signature, off={1: documented}}",
        ),
    )
    assert "eq-boundary-mismatch" in [
        finding.rule for finding in duplicate_opt_out.findings
    ]

    duplicate_scope = audit_log(
        "check|scope=1|scope=9|relation=1|result=equal|signature=\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}", "check={signature}"
        ),
    )
    duplicate_scope_rules = [finding.rule for finding in duplicate_scope.findings]
    assert "malformed-event" in duplicate_scope_rules
    assert "eq-boundary-mismatch" in duplicate_scope_rules

    missing_result = audit_log(
        "check|scope=1|relation=1\n"
        + equation_log.replace("|lang=kernel", "|lang=kernel|scope=1"),
        checked_equation_source.replace(
            "check={signature, modulo=bundles}", "check={signature}"
        ),
    )
    missing_result_rules = [finding.rule for finding in missing_result.findings]
    assert "malformed-event" in missing_result_rules
    assert "eq-boundary-mismatch" in missing_result_rules
    assert not next(
        event for event in missing_result.log_events if event.kind == "check"
    ).valid

    duplicate_result = audit_log(
        "check|scope=1|relation=1|result=mismatch|result=equal\n"
    )
    duplicate_result_rules = [
        finding.rule for finding in duplicate_result.findings
    ]
    assert "malformed-event" in duplicate_result_rules
    assert "kernel-check" not in duplicate_result_rules

    invalid_picture_scope = audit_log(
        equation_log.replace(
            "picture|id=k1|lang=kernel",
            "picture|id=k1|lang=kernel|scope=9",
        ).replace(
            "picture|id=k2|lang=kernel",
            "picture|id=k1|lang=kernel|scope=1|scope=9\n"
            "picture|id=k2|lang=kernel|scope=1",
        )
        + "check|scope=1|relation=1|result=equal|signature=\n",
        checked_equation_source.replace(
            "check={signature, modulo=bundles}", "check={signature}"
        ),
    )
    invalid_picture_rules = [
        finding.rule for finding in invalid_picture_scope.findings
    ]
    assert "malformed-event" in invalid_picture_rules
    assert "eq-boundary-mismatch" in invalid_picture_rules

    checkless_equation_source = (
        "\\begin{tenkzeq}[size=m]\n"
        + equation_source
        + "\\end{tenkzeq}\n"
    )
    checked_mismatch_source = checked_equation_source.replace(
        "check={signature, modulo=bundles}", "check={signature}"
    )
    matching_equation_log = equation_log.replace(
        "|lang=kernel", "|lang=kernel|scope=1"
    ).replace("phys:up", "open:e")
    second_equation_log = (
        equation_log.replace("k1", "k3").replace("k2", "k4")
        .replace("|lang=kernel", "|lang=kernel|scope=2")
    )
    mixed_equations = audit_log(
        matching_equation_log
        + "check|scope=1|relation=1|result=equal|signature=open:e, open:w\n"
        + second_equation_log
        + "check|scope=2|relation=1|result=mismatch|reason=boundary\n",
        checkless_equation_source + checked_mismatch_source,
    )
    mixed_boundary_mismatches = [
        finding for finding in mixed_equations.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(mixed_boundary_mismatches) == 1, mixed_equations.findings

    checked_off_source = checked_mismatch_source.replace(
        "check={signature}", "check={signature, off={1: documented}}"
    )
    two_checked_equations_source = checked_mismatch_source + checked_off_source
    first_scoped_mismatch = equation_log.replace(
        "|lang=kernel", "|lang=kernel|scope=1"
    )
    second_scoped_mismatch = second_equation_log
    malformed_then_valid = audit_log(
        first_scoped_mismatch
        + "check|scope=1|result=malformed|reason=relation-count"
        "|panels=2|relations=2\n"
        + "check|scope=1|relation=1|result=equal|signature=open:w\n"
        + "check|scope=2|relation=1|result=off|reason=documented\n"
        + second_scoped_mismatch,
        two_checked_equations_source,
    )
    malformed_boundary_mismatches = [
        finding for finding in malformed_then_valid.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(malformed_boundary_mismatches) == 1, malformed_then_valid.findings
    assert "pictures k1 and k2" in malformed_boundary_mismatches[0].msg
    assert "kernel-check" in [
        finding.rule for finding in malformed_then_valid.findings
    ]

    truncated_then_valid = audit_log(
        first_scoped_mismatch
        + "check|scope=2|relation=1|result=off|reason=documented\n"
        + second_scoped_mismatch,
        two_checked_equations_source,
    )
    truncated_boundary_mismatches = [
        finding for finding in truncated_then_valid.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(truncated_boundary_mismatches) == 1, truncated_then_valid.findings
    assert "pictures k1 and k2" in truncated_boundary_mismatches[0].msg

    brace_nested_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n"
        "\\text{a=b}\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkzeq}\n"
    )
    nested_then_valid = audit_log(
        matching_equation_log
        + "check|scope=1|relation=1|result=equal|signature=open:e, open:w\n"
        + second_scoped_mismatch
        + "check|scope=2|relation=1|result=mismatch|reason=boundary\n",
        brace_nested_source + checked_mismatch_source,
    )
    nested_boundary_mismatches = [
        finding for finding in nested_then_valid.findings
        if finding.rule == "eq-boundary-mismatch"
    ]
    assert len(nested_boundary_mismatches) == 1, nested_then_valid.findings
    assert "pictures k3 and k4" in nested_boundary_mismatches[0].msg

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

    inscribed_label_log = """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=
label-use|picture=k1
bbox|picture=k1|class=label|id=1|owner=0|xmin=20|xmax=22|ymin=20|ymax=22|shape=rect|radius=0
label-use|picture=k1
bbox|picture=k1|class=label|id=2|owner=1|xmin=4|xmax=6|ymin=4|ymax=6|shape=rect|radius=0
ink-use|picture=k1|class=glyph|id=1|shape=rect
glyph-geometry|picture=k1|owner=1|shape=rect|xmin=0|xmax=10|ymin=0|ymax=10|radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0
"""
    inscribed_label = audit_log(inscribed_label_log)
    assert "label-overlap" not in [
        finding.rule for finding in inscribed_label.findings
    ]

    coincident_id_log = """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=
label-use|picture=k1
bbox|picture=k1|class=label|id=2|owner=0|xmin=4|xmax=6|ymin=4|ymax=6|shape=rect|radius=0
ink-use|picture=k1|class=glyph|id=2|shape=rect
glyph-geometry|picture=k1|owner=2|shape=rect|xmin=0|xmax=10|ymin=0|ymax=10|radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0
"""
    coincident_id = audit_log(coincident_id_log)
    assert "label-overlap" in [
        finding.rule for finding in coincident_id.findings
    ]

    sibling_overlap_log = inscribed_label_log + """\
ink-use|picture=k1|class=glyph|id=2|shape=rect
glyph-geometry|picture=k1|owner=2|shape=rect|xmin=5|xmax=15|ymin=5|ymax=15|radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0
"""
    sibling_overlap = audit_log(sibling_overlap_log)
    sibling_findings = [
        finding for finding in sibling_overlap.findings
        if finding.rule == "label-overlap"
    ]
    assert len(sibling_findings) == 1, sibling_overlap.findings
    assert "id=2" in sibling_findings[0].msg, sibling_findings

    partial_own_overlap_log = """\
picture|id=k1|lang=kernel
atom|id=atom-1|kind=tn
kernel-boundary|signature=
label-use|picture=k1
bbox|picture=k1|class=label|id=2|owner=1|xmin=8|xmax=12|ymin=4|ymax=6|shape=rect|radius=0
ink-use|picture=k1|class=glyph|id=1|shape=rect
glyph-geometry|picture=k1|owner=1|shape=rect|xmin=0|xmax=10|ymin=0|ymax=10|radius=0|stroke=0|x1=0|y1=0|x2=0|y2=0|x3=0|y3=0
"""
    partial_own_overlap = audit_log(partial_own_overlap_log)
    assert "label-overlap" in [
        finding.rule for finding in partial_own_overlap.findings
    ]

    print("tenkz-kernel-audit: parser, crossings, boundaries, and geometry passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
