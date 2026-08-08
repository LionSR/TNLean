#!/usr/bin/env python3
"""Focused regression tests for tenkz equation-separator recognition."""

import tempfile
from pathlib import Path

from tenkz_audit import Audit, same_equation


POSITIVE = (
    r"$\;=\;$",
    "  \n  $\\; = \\;$  \n",
    r"$\,\! = \:\quad$",
    " = ",
    r"\qquad = \qquad",
)

NEGATIVE = (
    r"$x=y$",
    r"$\;x=y\;$",
    r"$\;=\;1$",
    r"$\;=\;\otimes$",
    r"$\;=\;$ extra text",
    r"extra text $\;=\;$",
    r"$\;=\;$ $\;=\;$",
    r"\begin{center}$\;=\;$\end{center}",
    r"& $\;=\;$",
    r"\[=\]",
    r"$$=$$",
    r"$\;=\;\text{extra}$",
)


def equation_boundary_rules(separator: str) -> list[str]:
    """Run the source-linked boundary check on two mismatched fixtures."""
    source = (
        "\\begin{tenkz}\n\\tn{A}\n\\end{tenkz}\n"
        f"{separator}\n"
        "\\begin{tenkz}\n\\tn{B}\n\\end{tenkz}\n"
    )
    log = (
        "picture|id=k1|lang=kernel\n"
        "atom|id=atom-1|cell=1-1|kind=tn\n"
        "kernel-boundary|signature=open:e,open:w\n"
        "picture|id=k2|lang=kernel\n"
        "atom|id=atom-1|cell=1-1|kind=tn\n"
        "kernel-boundary|signature=up:physical\n"
    )
    with tempfile.TemporaryDirectory(prefix="tenkz_equation_audit_") as tmp:
        work = Path(tmp)
        tex_path = work / "fixture.tex"
        log_path = work / "fixture.tnlog"
        tex_path.write_text(source, encoding="utf-8")
        log_path.write_text(log, encoding="utf-8")
        audit = Audit(log_path, tex_path)
        audit.parse_log()
        audit.link_tex()
        assert audit.tex_linked, "equation-boundary fixture did not link to its source"
        audit.check_equation_boundaries()
        return [finding.rule for finding in audit.findings]


def main() -> int:
    for separator in POSITIVE:
        assert same_equation(separator), f"expected equation glue: {separator!r}"
    for separator in NEGATIVE:
        assert not same_equation(separator), f"expected boundary: {separator!r}"
    assert "eq-boundary-mismatch" in equation_boundary_rules(r"$\;=\;$")
    assert "eq-boundary-mismatch" not in equation_boundary_rules(r"$x=y$")
    print(
        "tenkz-equation-audit: "
        f"{len(POSITIVE)} positive, {len(NEGATIVE)} negative, "
        "and 2 source-linked checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
