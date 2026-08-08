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


def panel(index: int, signature: str, scope: str = "|scope=1") -> str:
    """One panel of a seeded stream: its header, one atom, its boundary."""
    return (
        f"picture|id=k{index}|lang=kernel{scope}\n"
        "atom|id=atom-1|cell=1-1|kind=tn\n"
        f"kernel-boundary|signature={signature}\n"
    )


def audit_rules(log: str, source: str | None = None) -> list[tuple[str, str]]:
    """Run the whole equation half of the audit on one seeded stream.

    Passing no source runs the log-only half, which is what the blueprint
    sweep and any unlinked consumer see.
    """
    with tempfile.TemporaryDirectory(prefix="tenkz_equation_audit_") as tmp:
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
        assert source is None or audit.tex_linked, (
            "equation fixture did not link to its source"
        )
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
    assert ("eq-check-drift", "HARD") in forged, forged
    assert ("eq-boundary-mismatch", "HARD") in forged, forged

    # A waiver the source declares but the stream never recorded means the
    # two are not the same document, even where the panels agree.
    stale = audit_rules(
        group_log(
            "open:w",
            "open:w",
            "check|scope=1|relation=1|result=equal|signature=open:w\n",
        ),
        group_source("[check={signature, off={1: drafted}}]"),
    )
    assert ("eq-check-drift", "HARD") in stale, stale

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

    # Seeded defect: one contraction lost and another recorded twice.  The
    # count closes, but panel 4 was never folded into a side.
    duplicated_product = audit_rules(
        panel(1, "open:w") + panel(2, "open:e") + panel(3, "open:w")
        + panel(4, "open:e")
        + "check|scope=1|product=1-2|result=contracted|signature=open:w\n"
        "check|scope=1|product=1-2|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n"
    )
    assert ("eq-unchecked", "HARD") in duplicated_product, duplicated_product

    # The same group with both contractions recorded closes and passes.
    honest_product = audit_rules(
        panel(1, "open:w") + panel(2, "open:e") + panel(3, "open:w")
        + panel(4, "open:e")
        + "check|scope=1|product=1-2|result=contracted|signature=open:w\n"
        "check|scope=1|product=3-4|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n"
    )
    assert not honest_product, honest_product

    # Seeded defect: the panels lost the scope their checks still name.
    orphaned = audit_rules(
        panel(1, "open:w", scope="") + panel(2, "phys:up", scope="")
        + "check|scope=7|relation=1|result=equal|signature=open:w\n"
    )
    assert ("eq-unchecked", "HARD") in orphaned, orphaned

    # A display asserting a relation over a product says nothing pairwise:
    # the right factor of the product is not the side the relation names.
    product_display = audit_rules(
        panel(1, "open:w, open:e", scope="") + panel(2, "open:w", scope="")
        + panel(3, "open:e", scope=""),
        f"{PANELS[0]}$ = $\n{PANELS[1]}$ \\otimes $\n{PANELS[0]}",
    )
    assert ("eq-sibling-unread", "ADV") in product_display, product_display
    assert "eq-sibling-mismatch" not in [
        rule for rule, _ in product_display
    ], product_display

    # Seeded defect: a stale stream compares modulo bundles past a source
    # that asks for strand-for-strand, and the loose reading is not honoured.
    loosened = audit_rules(
        group_log(
            "open:e:bundle=2",
            "open:e, open:e",
            "check|scope=1|relation=1|result=equal|modulo=bundles"
            "|signature=open:e, open:e\n",
        ),
        group_source(),
    )
    assert ("eq-check-drift", "HARD") in loosened, loosened
    assert ("eq-boundary-mismatch", "HARD") in loosened, loosened

    # The same comparison the source does ask for is honoured.
    bundled = audit_rules(
        group_log(
            "open:e:bundle=2",
            "open:e, open:e",
            "check|scope=1|relation=1|result=equal|modulo=bundles"
            "|signature=open:e, open:e\n",
        ),
        group_source("[check={signature, modulo=bundles}]"),
    )
    assert not bundled, bundled

    # A forged waiver on one relation retires nothing, and retires nothing of
    # the author's honest waiver on another relation of the same equation.
    mixed_source = (
        "\\begin{tenkzeq}[check={signature, off={2: drafted}}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}=\n{PANELS[0]}"
        "\\end{tenkzeq}\n"
    )
    mixed = audit_rules(
        panel(1, "open:w") + panel(2, "phys:up") + panel(3, "open:e")
        + "check|scope=1|relation=1|result=off|reason=forged\n"
        "check|scope=1|relation=2|result=off|reason=drafted\n",
        mixed_source,
    )
    assert ("eq-check-drift", "HARD") in mixed, mixed
    assert ("eq-check-off", "ADV") in mixed, mixed
    mismatches = [rule for rule, _ in mixed if rule == "eq-boundary-mismatch"]
    assert len(mismatches) == 1, mixed

    # Seeded defect: a scope whose arity failure went missing with its
    # record.  One panel and no relation compares nothing, whatever the
    # arithmetic says.
    relationless = audit_rules(panel(1, "open:w"))
    assert ("eq-unchecked", "HARD") in relationless, relationless

    # Seeded defect: one record claiming to be both joiners of a three-panel
    # scope.  A check names the one joiner it resolved.
    two_faced = audit_rules(
        panel(1, "open:w") + panel(2, "open:e") + panel(3, "open:w")
        + "check|scope=1|relation=1|product=1-2|result=contracted"
        "|signature=open:w\n"
    )
    assert ("malformed-event", "HARD") in two_faced, two_faced
    assert ("eq-unchecked", "HARD") in two_faced, two_faced

    # Seeded defect: two source equations whose panels the stream has
    # cross-assigned.  Each scope owns two panels and a relation record, so
    # the arithmetic closes, but neither authored pair was compared.
    crossed_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}"
        "\\end{tenkzeq}\n"
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}"
        "\\end{tenkzeq}\n"
    )
    crossed = audit_rules(
        panel(1, "open:w") + panel(2, "open:w", scope="|scope=2")
        + panel(3, "open:w", scope="|scope=1") + panel(4, "open:w", scope="|scope=2")
        + "check|scope=1|relation=1|result=equal|signature=open:w\n"
        "check|scope=2|relation=1|result=equal|signature=open:w\n",
        crossed_source,
    )
    assert ("eq-unchecked", "HARD") in crossed, crossed

    # Seeded defect: `panel1 = panel2 panel3` contracts only the second gap,
    # so a record folding the first one leaves panel 3 uncompared even though
    # the count balances.
    product_side_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}{PANELS[0]}"
        "\\end{tenkzeq}\n"
    )
    crossed_product = audit_rules(
        panel(1, "open:w") + panel(2, "open:e") + panel(3, "open:w")
        + "check|scope=1|product=1-2|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n",
        product_side_source,
    )
    assert ("eq-unchecked", "HARD") in crossed_product, crossed_product

    # The contraction the source does state closes the same scope.
    honest_side = audit_rules(
        panel(1, "open:w") + panel(2, "open:e") + panel(3, "open:w")
        + "check|scope=1|product=2-3|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n",
        product_side_source,
    )
    assert not honest_side, honest_side

    # A display run enters the report once, whether it ends at a boundary or
    # at the end of the stream.
    boundary_source = (
        f"{PANELS[0]}$ = $\n{PANELS[1]}\n"
        "\\begin{center}\n" + PANELS[0] + "\\end{center}\n"
    )
    once = audit_rules(
        panel(1, "open:w", scope="") + panel(2, "phys:up", scope="")
        + panel(3, "open:w", scope=""),
        boundary_source,
    )
    assert once.count(("eq-sibling-mismatch", "ADV")) == 1, once

    # Seeded defect: `panel1 = panel2 = panel3 panel4`.  The last side folds
    # over a contraction and stays the kernel's to answer for, but the first
    # relation has one panel on each side, and a mismatch there is the audit's
    # to find however confidently the record says otherwise.
    beside_product_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}=\n{PANELS[0]}{PANELS[1]}"
        "\\end{tenkzeq}\n"
    )
    beside_product_records = (
        "check|scope=1|product=3-4|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n"
        "check|scope=1|relation=2|result=equal|signature=open:w\n"
    )
    beside_product = audit_rules(
        panel(1, "open:w") + panel(2, "phys:up") + panel(3, "open:w")
        + panel(4, "open:e") + beside_product_records,
        beside_product_source,
    )
    mismatched_sides = [
        rule for rule, _ in beside_product if rule == "eq-boundary-mismatch"
    ]
    assert len(mismatched_sides) == 1, beside_product

    # The same shape with single sides that do agree stays clean: the fold
    # over the contraction is not recomputed here.
    beside_product_clean = audit_rules(
        panel(1, "open:w") + panel(2, "open:w") + panel(3, "open:w")
        + panel(4, "open:e") + beside_product_records,
        beside_product_source,
    )
    assert not beside_product_clean, beside_product_clean

    # Seeded defect: `A = B C D` written with two relation records and one
    # contraction.  The count balances and the contraction stays clear of the
    # one recognized relation, but a gap the source leaves empty joins its
    # panels by juxtaposition and nothing else, so a contraction has to name
    # it -- and the panel behind the unnamed gap carries the mismatch.
    gap_partition_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}{PANELS[0]}{PANELS[1]}"
        "\\end{tenkzeq}\n"
    )
    gap_partition = audit_rules(
        panel(1, "open:w") + panel(2, "open:w") + panel(3, "open:e")
        + panel(4, "phys:up")
        + "check|scope=1|product=2-3|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n"
        "check|scope=1|relation=2|result=equal|signature=open:w\n",
        gap_partition_source,
    )
    assert ("eq-unchecked", "HARD") in gap_partition, gap_partition
    assert ("eq-boundary-mismatch", "HARD") in gap_partition, gap_partition

    # The same display with a contraction on each juxtaposed gap closes.
    gap_partition_whole = audit_rules(
        panel(1, "open:w") + panel(2, "open:w") + panel(3, "open:e")
        + panel(4, "open:w")
        + "check|scope=1|product=2-3|result=contracted|signature=open:w\n"
        "check|scope=1|product=3-4|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n",
        gap_partition_source,
    )
    assert not gap_partition_whole, gap_partition_whole

    # Seeded defect: gaps the reading of the mathematics settles nothing
    # about.  The stream claims a relation on the last gap and a contraction
    # on the middle one; the source spells a product sign on both, so the
    # contractions are the two gaps holding no relation glyph and there is
    # one relation, not two.
    unsettled_source = (
        "\\begin{tenkzeq}[check={signature}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}$\\otimes$\n{PANELS[0]}$\\otimes$\n{PANELS[1]}"
        "\\end{tenkzeq}\n"
    )
    unsettled = audit_rules(
        panel(1, "open:w") + panel(2, "open:w") + panel(3, "open:e")
        + panel(4, "phys:up")
        + "check|scope=1|product=2-3|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n"
        "check|scope=1|relation=2|result=equal|signature=open:w\n",
        unsettled_source,
    )
    assert ("eq-unchecked", "HARD") in unsettled, unsettled
    assert ("eq-boundary-mismatch", "HARD") in unsettled, unsettled

    # The same display read the way the kernel reads it: one relation over
    # the equals sign, a contraction on each product sign.
    unsettled_whole = audit_rules(
        panel(1, "open:w") + panel(2, "open:w") + panel(3, "open:e")
        + panel(4, "open:w")
        + "check|scope=1|product=2-3|result=contracted|signature=open:w\n"
        "check|scope=1|product=3-4|result=contracted|signature=open:w\n"
        "check|scope=1|relation=1|result=equal|signature=open:w\n",
        unsettled_source,
    )
    assert not unsettled_whole, unsettled_whole

    # A relation the source waives stays waived when the scope fails closure
    # for a reason of its own: an author who opted a relation out did not opt
    # back in by losing a record elsewhere.
    waived_under_failure = audit_rules(
        panel(1, "open:w") + panel(2, "phys:up") + panel(3, "phys:up")
        + "check|scope=1|relation=1|result=off|reason=drafted\n"
        "check|scope=1|relation=2|result=equal|signature=open:w\n"
        "check|scope=1|relation=2|result=equal|signature=open:w\n",
        "\\begin{tenkzeq}[check={signature, off={1: drafted}}]\n"
        f"{PANELS[0]}=\n{PANELS[1]}=\n{PANELS[0]}"
        "\\end{tenkzeq}\n",
    )
    assert ("eq-unchecked", "HARD") in waived_under_failure, waived_under_failure
    assert ("eq-check-off", "ADV") in waived_under_failure, waived_under_failure
    assert "eq-boundary-mismatch" not in [
        rule for rule, _ in waived_under_failure
    ], waived_under_failure

    # A waiver runs no comparison and so states no comparison mode: a scope
    # whose every relation is waived leaves the mode unobserved, not observed
    # to be off, and its source's `modulo=bundles` is no disagreement.
    all_waived = audit_rules(
        group_log(
            "open:w",
            "open:w",
            "check|scope=1|relation=1|result=off|reason=drafted\n",
        ),
        group_source("[check={signature, modulo=bundles, off={1: drafted}}]"),
    )
    assert ("eq-check-off", "ADV") in all_waived, all_waived
    assert "eq-check-drift" not in [rule for rule, _ in all_waived], all_waived

    # Two `check=` keys state no single policy, and both halves of the policy
    # reader say so: the waiver reader already refused such a source, and the
    # comparison mode is refused with it rather than taken from one of them.
    two_checks = audit_rules(
        group_log(
            "open:e:bundle=2",
            "open:e, open:e",
            "check|scope=1|relation=1|result=equal|modulo=bundles"
            "|signature=open:e, open:e\n",
        ),
        group_source("[check={signature, modulo=bundles}, check={signature}]"),
    )
    assert ("eq-check-drift", "HARD") in two_checks, two_checks
    assert ("eq-boundary-mismatch", "HARD") in two_checks, two_checks

    # A spaced environment name opens the same equation, so its declared
    # waiver is the source's and not a forgery.
    spaced = audit_rules(
        group_log(
            "open:w",
            "phys:up",
            "check|scope=1|relation=1|result=off|reason=drafted\n",
        ),
        group_source("[check={signature, off={1: drafted}}]").replace(
            "\\begin{tenkzeq}", "\\begin {tenkzeq}"
        ).replace("\\end{tenkzeq}", "\\end {tenkzeq}"),
    )
    assert ("eq-check-off", "ADV") in spaced, spaced
    assert "eq-check-drift" not in [rule for rule, _ in spaced], spaced

    print(
        "tenkz-equation-audit: "
        f"{len(POSITIVE)} positive, {len(NEGATIVE)} negative, "
        "and 33 seeded group checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
