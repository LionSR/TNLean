#!/usr/bin/env python3
"""Focused contract tests for the shared tenkz TeX case reader."""

from tenkz_audit import scan_constructs as audit_scan_constructs
from tenkz_audit import strip_comments as audit_strip_comments
from tenkz_lint import scan_bodies
from tenkzlib.texcase import scan_constructs, strip_comments


def main() -> int:
    source = (
        "before % hidden \\begin{tenkz}\\tn{X}\\end{tenkz}\n"
        "\\% visible percent\n"
        "\\\\% hidden after an even number of slashes\n"
        "\\begin{tenkz}[rows={ket,op,bra}]\n"
        "  \\tn{A} % hidden atom\n"
        "  \\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkz}\n"
        "\\begin{tenkzeq}=\\end{tenkzeq}\n"
        "\\tnpic[label={x]y}]{\\tn{C}}\n"
    )
    stripped = strip_comments(source)
    assert len(stripped) == len(source)
    assert stripped.count("\n") == source.count("\n")
    assert "\\% visible percent" in stripped
    assert "hidden after" not in stripped
    assert "hidden atom" not in stripped

    constructs = scan_constructs(stripped)
    assert [construct.name for construct in constructs] == [
        "tenkz",
        "tenkz",
        "tenkzeq",
        "tnpic",
    ]
    outer, inner, equation, inline = constructs
    assert "\\tn{A}" in outer.body
    assert "\\tn{B}" in inner.body
    assert equation.body == "="
    assert inline.body == "\\tn{C}"
    for construct in constructs:
        assert stripped[construct.body_start : construct.body_start + len(construct.body)] == (
            construct.body
        )
        assert construct.line == source.count("\n", 0, construct.start) + 1

    bodies = scan_bodies(stripped)
    assert [(body.name, body.start, body.text) for body in bodies] == [
        (construct.name, construct.body_start, construct.body)
        for construct in constructs
    ]
    assert audit_strip_comments is strip_comments
    assert audit_scan_constructs is scan_constructs
    print("texcase: comment parity, nested constructs, offsets, and shims passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
