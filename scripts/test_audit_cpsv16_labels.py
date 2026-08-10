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
        "eq1:proof.IV.12 at line 1838" in error and "line-1838" in error
        for error in errors
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
    test_shared_tsv_schema_and_row_validation()
    print("PASS: CPSV16 audit mutations are rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
