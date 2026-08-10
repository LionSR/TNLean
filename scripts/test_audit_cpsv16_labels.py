#!/usr/bin/env python3
"""Mutation tests for the CPSV16 every-label audit."""

from __future__ import annotations

import tempfile
from pathlib import Path
from typing import Callable

import audit_cpsv16_labels as audit
from tenkzlib.texcase import TeXEnvironmentNestingError


def equation_ledger(*labels: str) -> dict[str, dict[str, str]]:
    return {
        label: {
            "classification": "equation",
            "disposition": "Inherits the complete status and hypothesis boundary.",
        }
        for label in labels
    }


def assert_rejected(
    reader: Callable[[Path], object], contents: str, expected_message: str
) -> None:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "table.tsv"
        path.write_text(contents)
        try:
            reader(path)
        except ValueError as error:
            assert expected_message in str(error), str(error)
        else:
            raise AssertionError(f"invalid TSV was accepted: {contents!r}")


def test_comment_parity_and_activity_offsets() -> None:
    source = (
        r"odd \% \label{odd}" + "\n"
        r"even \\% \label{even}" + "\n"
    )
    stripped = audit.strip_comments(source)
    assert len(stripped) == len(source)
    assert stripped.count("\n") == source.count("\n")
    assert r"\label{odd}" in stripped
    assert r"\label{even}" not in stripped
    even_start = source.index(r"\label{even}")
    assert stripped[even_start : even_start + len(r"\label{even}")].isspace()

    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "source.tex"
        path.write_text(source)
        inventory, active_source = audit.source_inventory(path)
    assert inventory == [
        ("odd", 1, source.splitlines()[0].index(r"\label{odd}"), True),
        ("even", 2, source.splitlines()[1].index(r"\label{even}"), False),
    ]
    assert active_source == stripped


def test_spaced_theorem_environments() -> None:
    source = "\n".join(
        [r"\begin { thm }", r"\be\label{x}x=1\ee", r"\end { thm }"]
    )
    assert audit.theorem_contained_labels(source, equation_ledger("x")) == [
        ("x", 2)
    ]


def test_multiple_environment_tokens_per_line() -> None:
    nested = (
        r"\begin{thm}\label{outer}\begin{proof}\label{inner}"
        r"\end{proof}\label{tail}\end{thm}"
    )
    assert audit.theorem_contained_labels(
        nested, equation_ledger("outer", "inner", "tail")
    ) == [("outer", 1), ("inner", 1), ("tail", 1)]

    sequential = (
        r"\begin{thm}\label{a}\end{thm}\label{outside}"
        r"\begin{lem}\label{b}\end{lem}"
    )
    assert audit.theorem_contained_labels(
        sequential, equation_ledger("a", "outside", "b")
    ) == [("a", 1), ("b", 1)]


def test_mismatched_environment_diagnostic() -> None:
    source = r"\begin{thm}\begin{proof}\end{thm}"
    try:
        audit.theorem_contained_labels(source, {})
    except TeXEnvironmentNestingError as error:
        message = str(error)
        assert "mismatched" in message
        assert r"\end{thm}" in message
        assert r"expected \end{proof}" in message
        assert "line 1" in message
    else:
        raise AssertionError("mismatched theorem/proof nesting was accepted")


def test_inheritance_count_regression() -> None:
    _, active_source = audit.source_inventory()
    ledger = audit.read_ledger()
    baseline = audit.theorem_contained_labels(active_source, ledger)
    assert not audit.inheritance_count_errors(baseline)

    mutated = active_source.replace(r"\begin{cor}", r"\begin{remark}", 1)
    mutated = mutated.replace(r"\end{cor}", r"\end{remark}", 1)
    reduced = audit.theorem_contained_labels(mutated, ledger)
    errors = audit.inheritance_count_errors(reduced)
    assert errors
    assert any("occurrences" in error for error in errors)


def test_classification_identity_regression() -> None:
    ledger = audit.read_ledger()
    assert not audit.classification_count_errors(ledger)

    mutated = {label: dict(row) for label, row in ledger.items()}
    mutated["AA=A"]["classification"] = "theorem-like"
    mutated["propblockinj"]["classification"] = "equation"
    errors = audit.classification_count_errors(mutated)
    assert not any("classification totals" in error for error in errors)
    assert any("AA=A: classification" in error for error in errors)
    assert any("propblockinj: classification" in error for error in errors)


def test_eq2_proof_main_classification_regression() -> None:
    ledger = audit.read_ledger()
    assert ledger["eq2-proof-main-thm"]["classification"] == "equation"
    assert ledger["Figure11"]["classification"] == "figure"

    mutated = {label: dict(row) for label, row in ledger.items()}
    mutated["eq2-proof-main-thm"]["classification"] = "figure"
    mutated["Figure11"]["classification"] = "equation"
    errors = audit.classification_count_errors(mutated)
    assert not any("classification totals" in error for error in errors)
    assert any("eq2-proof-main-thm: classification" in error for error in errors)
    assert any("Figure11: classification" in error for error in errors)


def test_duplicate_occurrence_inheritance() -> None:
    _, active_source = audit.source_inventory()
    ledger = audit.read_ledger()
    contained = audit.theorem_contained_labels(active_source, ledger)
    assert not audit.inheritance_errors(contained, ledger)

    mutated = {label: dict(row) for label, row in ledger.items()}
    mutated["eq1:proof.IV.12"]["disposition"] = (
        "The line-1882 occurrence inherits Proposition 4.13's complete "
        "rectangular-coisometry status and orientation."
    )
    errors = audit.inheritance_errors(contained, mutated)
    assert any(
        "eq1:proof.IV.12 at line 1838" in error and "line 1838" in error
        for error in errors
    )


def test_unique_occurrence_result_anchor_swap() -> None:
    _, active_source = audit.source_inventory()
    ledger = audit.read_ledger()
    contained = audit.theorem_contained_labels(active_source, ledger)
    anchors = audit.read_contained_result_anchors()
    assert len(anchors) == audit.EXPECTED_THEOREM_CONTAINED_OCCURRENCES
    assert set(contained) == set(anchors)

    mutated = {label: dict(row) for label, row in ledger.items()}
    mutated["AA=A"]["disposition"], mutated["KxKy=0"]["disposition"] = (
        mutated["KxKy=0"]["disposition"],
        mutated["AA=A"]["disposition"],
    )
    errors = audit.inheritance_errors(contained, mutated, anchors)
    assert any(
        "AA=A at line 401" in error and "Theorem 3.1" in error
        for error in errors
    )
    assert any(
        "KxKy=0 at line 866" in error and "Theorem 4.9" in error
        for error in errors
    )


def test_exact_result_anchor_matching() -> None:
    _, active_source = audit.source_inventory()
    ledger = audit.read_ledger()
    contained = audit.theorem_contained_labels(active_source, ledger)
    anchors = audit.read_contained_result_anchors()
    assert not audit.inheritance_errors(contained, ledger, anchors)

    wrong_number = {label: dict(row) for label, row in ledger.items()}
    wrong_number["AA=A"]["disposition"] = wrong_number["AA=A"][
        "disposition"
    ].replace("Theorem 3.1", "Theorem 3.11")
    number_errors = audit.inheritance_errors(contained, wrong_number, anchors)
    assert any(
        "AA=A at line 401" in error and "Theorem 3.1" in error
        for error in number_errors
    )

    wrong_scope = {label: dict(row) for label, row in ledger.items()}
    wrong_scope["eq:algebra"]["disposition"] = ledger["Figure9"]["disposition"]
    scope_errors = audit.inheritance_errors(contained, wrong_scope, anchors)
    assert any(
        "eq:algebra at line 978" in error and "Theorem 4.14" in error
        for error in scope_errors
    )
    assert not any("Figure9 at line 1953" in error for error in scope_errors)

    swapped_boundaries = {label: dict(row) for label, row in ledger.items()}
    swapped_boundaries["eq:algebra"]["disposition"] = ledger["Ualphabeta"][
        "disposition"
    ]
    swapped_boundaries["Ualphabeta"]["disposition"] = ledger["eq:algebra"][
        "disposition"
    ]
    boundary_errors = audit.inheritance_errors(
        contained, swapped_boundaries, anchors
    )
    assert any(
        "eq:algebra at line 978" in error
        and "occurrence-specific semantic boundary" in error
        for error in boundary_errors
    )
    assert any(
        "Ualphabeta at line 988" in error
        and "occurrence-specific semantic boundary" in error
        for error in boundary_errors
    )

    uppercase_scope = {label: dict(row) for label, row in ledger.items()}
    uppercase_scope["eq:algebra"]["disposition"] = ledger["Figure9"][
        "disposition"
    ].replace("proof of Theorem 4.14", "Proof of Theorem 4.14")
    uppercase_errors = audit.inheritance_errors(
        contained, uppercase_scope, anchors
    )
    assert any(
        "eq:algebra at line 978" in error and "Theorem 4.14" in error
        for error in uppercase_errors
    )
    assert not any(
        "Figure9 at line 1953" in error for error in uppercase_errors
    )

    flexible_space_scope = {label: dict(row) for label, row in ledger.items()}
    flexible_space_scope["eq:algebra"]["disposition"] = ledger["Figure9"][
        "disposition"
    ].replace("proof of Theorem 4.14", "proof of  Theorem 4.14")
    flexible_space_errors = audit.inheritance_errors(
        contained, flexible_space_scope, anchors
    )
    assert any(
        "eq:algebra at line 978" in error and "Theorem 4.14" in error
        for error in flexible_space_errors
    )
    assert not any(
        "Figure9 at line 1953" in error for error in flexible_space_errors
    )


def test_normalized_anchor_row_uniqueness_and_count() -> None:
    lines = audit.CONTAINED_RESULT_ANCHORS.read_text().splitlines()
    header, *rows = lines
    aa_row = next(row for row in rows if row.startswith("AA=A\t401\t"))
    leading_zero_duplicate = aa_row.replace("\t401\t", "\t0401\t", 1)
    assert_rejected(
        audit.read_contained_result_anchors,
        "\n".join([header, *rows, leading_zero_duplicate]) + "\n",
        "duplicate normalized contained result-anchor row for AA=A at line 401",
    )
    assert_rejected(
        audit.read_contained_result_anchors,
        "\n".join([header, *rows[:-1]]) + "\n",
        "must contain exactly 60 physical rows, got 59",
    )


def test_shared_tsv_schema_and_row_validation() -> None:
    ledger_header = (
        "label\toccurrences\tlines\tactivity\tclassification\tdisposition\n"
    )
    ledger_row = "x\t1\t1\tactive\tequation\tvalid\n"
    snapshot_header = "label\tclassification\n"
    snapshot_row = "x\tequation\n"

    for reader, header, row, table_name in [
        (audit.read_ledger, ledger_header, ledger_row, "ledger"),
        (
            audit.read_classification_snapshot,
            snapshot_header,
            snapshot_row,
            "classification snapshot",
        ),
    ]:
        assert_rejected(reader, header.replace("label", "wrong", 1) + row,
                        "columns must be exactly")
        assert_rejected(reader, header + row.rstrip("\n") + "\tsurplus\n",
                        "surplus fields")
        short_row = row.rstrip("\n").rsplit("\t", 1)[0] + "\n"
        assert_rejected(reader, header + short_row, "missing fields")
        assert_rejected(reader, header + row + row, f"duplicate {table_name} row")
        empty_label_row = row.replace("x", "", 1)
        assert_rejected(reader, header + empty_label_row, f"empty label in {table_name}")


def main() -> int:
    test_comment_parity_and_activity_offsets()
    test_spaced_theorem_environments()
    test_multiple_environment_tokens_per_line()
    test_mismatched_environment_diagnostic()
    test_inheritance_count_regression()
    test_classification_identity_regression()
    test_eq2_proof_main_classification_regression()
    test_duplicate_occurrence_inheritance()
    test_unique_occurrence_result_anchor_swap()
    test_exact_result_anchor_matching()
    test_normalized_anchor_row_uniqueness_and_count()
    test_shared_tsv_schema_and_row_validation()
    print("PASS: CPSV16 audit mutations are rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
