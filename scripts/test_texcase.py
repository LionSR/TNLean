#!/usr/bin/env python3
"""Focused contract tests for the shared tenkz TeX case reader."""

from tenkz_audit import strip_comments as audit_strip_comments
from tenkz_lint import scan_bodies
from tenkzlib.texcase import (
    following_group,
    following_group_span,
    scan_constructs,
    scan_picture_event_constructs,
    strip_comments,
    top_level_options,
)


def main() -> int:
    source = (
        "before % hidden \\begin{tenkz}\\tn{X}\\end{tenkz}\n"
        "\\% visible percent\n"
        "\\\\% hidden after an even number of slashes\n"
        "\\begin{tenkz}[rows={ket,op,bra}]\n"
        "  \\tn{A} % hidden atom\n"
        "  \\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkz}\n"
        "\\tntree[label={x]y}]{({}{})}\n"
    )
    stripped = strip_comments(source)
    assert len(stripped) == len(source)
    assert stripped.count("\n") == source.count("\n")
    assert "\\% visible percent" in stripped
    assert "hidden after" not in stripped
    assert "hidden atom" not in stripped

    option_source = "  [check={signature, off={1: note}}, frame={x=[a,b]}] tail"
    option_group = following_group(option_source, 0, "[", "]")
    assert option_group == "check={signature, off={1: note}}, frame={x=[a,b]}"
    assert following_group_span(option_source, 0, "[", "]") == (
        option_group,
        option_source.index("] tail") + 1,
    )
    assert top_level_options(option_group) == [
        ("check", "{signature, off={1: note}}"),
        ("frame", "{x=[a,b]}"),
    ]

    constructs = scan_constructs(stripped)
    assert [construct.name for construct in constructs] == [
        "tenkz",
        "tenkz",
        "tntree",
    ]
    outer, inner, tree = constructs
    assert "\\tn{A}" in outer.body
    assert "\\tn{B}" in inner.body
    assert tree.body == "({}{})"
    for construct in constructs:
        assert stripped[construct.body_start : construct.body_start + len(construct.body)] == (
            construct.body
        )
        assert construct.line == source.count("\n", 0, construct.start) + 1
    assert [
        construct.name for construct in scan_picture_event_constructs(stripped)
    ] == ["tenkz", "tenkz"]

    spliced_source = (
        "\\begin {tenkz}\\tn{}\\end {tenkz}\n"
        "\\begin% legal control-word splice\n"
        "{tenkz}\\tn{}\\end% matching closing splice\n"
        "{tenkz}\n"
    )
    spliced = scan_constructs(spliced_source)
    assert [construct.name for construct in spliced] == ["tenkz", "tenkz"]
    assert [construct.line for construct in spliced] == [1, 2]
    assert all("\\tn{}" in construct.body for construct in spliced)

    control_boundaries = (
        r"\\begin{tenkz}\tn{}\\end{tenkz}" "\n"
        r"\\tntree{({}{})}" "\n"
        r"\tntreeⅣ{({}{})}" "\n"
        r"\begin{tenkz}\\end{tenkz}\tn{}\end{tenkz}" "\n"
    )
    real_controls = scan_constructs(control_boundaries)
    assert [construct.name for construct in real_controls] == ["tenkz"]
    assert r"\\end{tenkz}\tn{}" in real_controls[0].body

    bodies = scan_bodies(stripped)
    assert [(body.name, body.start, body.text) for body in bodies] == [
        (construct.name, construct.body_start, construct.body)
        for construct in constructs
    ]
    assert audit_strip_comments is strip_comments
    print(
        "texcase: comment parity, nested constructs, offsets, and shared scanners passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
