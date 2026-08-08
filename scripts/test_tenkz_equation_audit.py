#!/usr/bin/env python3
"""Regressions for the equation group and the source-separator reading.

The group is the `tenkzeq` scope: a mismatch inside one is a hard finding
read from the stream alone, while two pictures joined by a source `=` outside
every group stay advisory.  The seeded defects below are the audit half of
the enforcement; the kernel half lives in `tests/tenkz/kernel/negative/`.
"""

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

PANELS = (
    "\\begin{tenkz}\n\\tn{A}\n\\end{tenkz}\n",
    "\\begin{tenkz}\n\\tn{B}\n\\end{tenkz}\n",
)


def group_source(options: str = "[check={signature}]") -> str:
    return (
        f"\\begin{{tenkzeq}}{options}\n"
        f"{PANELS[0]}=\n{PANELS[1]}"
        "\\end{tenkzeq}\n"
    )


def group_log(left: str, right: str, records: str) -> str:
    return (
        "picture|id=k1|lang=kernel|scope=1\n"
        "atom|id=atom-1|cell=1-1|kind=tn\n"
        f"kernel-boundary|signature={left}\n"
        "picture|id=k2|lang=kernel|scope=1\n"
        "atom|id=atom-1|cell=1-1|kind=tn\n"
        f"kernel-boundary|signature={right}\n"
        f"{records}"
    )


def audit_rules(log: str, source: str) -> list[tuple[str, str]]:
    """Run the whole equation half of the audit on one seeded stream."""
    with tempfile.TemporaryDirectory(prefix="tenkz_equation_audit_") as tmp:
        work = Path(tmp)
        tex_path = work / "fixture.tex"
        log_path = work / "fixture.tnlog"
        tex_path.write_text(source, encoding="utf-8")
        log_path.write_text(log, encoding="utf-8")
        audit = Audit(log_path, tex_path)
        audit.parse_log()
        audit.link_tex()
        assert audit.tex_linked, "equation fixture did not link to its source"
        audit.check_kernel_checks()
        audit.check_equation_groups()
        audit.check_equation_boundaries()
        return [(finding.rule, finding.severity) for finding in audit.findings]


def sibling_rules(separator: str) -> list[tuple[str, str]]:
    """Two mismatched pictures joined by `separator` outside every group."""
    return audit_rules(
        group_log("open:e, open:w", "phys:up", "").replace("|scope=1", ""),
        f"{PANELS[0]}{separator}\n{PANELS[1]}",
    )


def main() -> int:
    for separator in POSITIVE:
        assert same_equation(separator), f"expected equation glue: {separator!r}"
    for separator in NEGATIVE:
        assert not same_equation(separator), f"expected boundary: {separator!r}"

    # Out of scope the source `=` is a reading, so a mismatch advises.
    assert ("eq-sibling-mismatch", "ADV") in sibling_rules(r"$\;=\;$")
    assert not sibling_rules(r"$x=y$")

    # Seeded defect: unequal boundaries inside one group are a hard finding.
    equal_record = "check|scope=1|relation=1|result=equal|signature=open:w\n"
    mismatched = audit_rules(
        group_log("open:w", "phys:up", equal_record), group_source()
    )
    assert ("eq-boundary-mismatch", "HARD") in mismatched, mismatched

    # Seeded defect: the same count of physical legs, opposite orientations.
    directed = audit_rules(
        group_log("phys:n:to", "phys:n:from", equal_record), group_source()
    )
    assert ("eq-boundary-mismatch", "HARD") in directed, directed

    # The clean group passes, orientation included.
    clean = audit_rules(
        group_log("phys:n:to", "phys:s:to", equal_record), group_source()
    )
    assert not clean, clean

    # Seeded defect: a panel no relation ever folded into a side.
    unchecked = audit_rules(group_log("open:w", "open:w", ""), group_source())
    assert ("eq-unchecked", "HARD") in unchecked, unchecked

    # A waiver the source declares is honoured, and never silent.
    waived = audit_rules(
        group_log(
            "open:w",
            "phys:up",
            "check|scope=1|relation=1|result=off|reason=drafted\n",
        ),
        group_source("[check={signature, off={1: drafted}}]"),
    )
    assert ("eq-check-off", "ADV") in waived, waived
    assert "eq-boundary-mismatch" not in [rule for rule, _ in waived], waived

    # A waiver the source does not declare retires nothing.
    forged = audit_rules(
        group_log(
            "open:w",
            "phys:up",
            "check|scope=1|relation=1|result=off|reason=drafted\n",
        ),
        group_source(),
    )
    assert ("eq-check-off", "HARD") in forged, forged
    assert ("eq-boundary-mismatch", "HARD") in forged, forged

    # The kernel's own refusal stays a hard finding of its own.
    refused = audit_rules(
        group_log(
            "open:w",
            "phys:up",
            "check|scope=1|relation=1|result=mismatch"
            "|left=open:w|right=phys:up\n",
        ),
        group_source(),
    )
    assert ("kernel-check", "HARD") in refused, refused

    print(
        "tenkz-equation-audit: "
        f"{len(POSITIVE)} positive, {len(NEGATIVE)} negative, "
        "and 8 seeded group checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
