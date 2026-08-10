#!/usr/bin/env python3
"""Mutation tests for the CPSV16 every-label audit."""

from __future__ import annotations

import tempfile
from pathlib import Path

import audit_cpsv16_labels as audit


def test_spaced_theorem_environments() -> None:
    ledger = {
        "x": {
            "classification": "equation",
            "disposition": "Inherits the complete status and hypothesis boundary.",
        }
    }
    lines = [
        r"\begin { thm }",
        r"\be\label{x}x=1\ee",
        r"\end { thm }",
    ]
    assert audit.theorem_contained_labels(lines, ledger) == ["x"]


def test_inheritance_count_regression() -> None:
    _, active_lines = audit.source_inventory()
    ledger = audit.read_ledger()
    baseline = audit.theorem_contained_labels(active_lines, ledger)
    assert not audit.inheritance_count_errors(baseline)

    mutated = list(active_lines)
    index = next(
        index for index, line in enumerate(mutated) if r"\begin{cor}" in line
    )
    mutated[index] = mutated[index].replace(r"\begin{cor}", r"\begin{remark}")
    reduced = audit.theorem_contained_labels(mutated, ledger)
    errors = audit.inheritance_count_errors(reduced)
    assert errors
    assert any("occurrences" in error for error in errors)


def test_classification_count_regression() -> None:
    ledger = audit.read_ledger()
    assert not audit.classification_count_errors(ledger)
    assert ledger["eq3:proof.IV.12"]["classification"] == "equation"

    mutated = {label: dict(row) for label, row in ledger.items()}
    mutated["eq3:proof.IV.12"]["classification"] = "figure"
    errors = audit.classification_count_errors(mutated)
    assert any("lexical classification totals" in error for error in errors)
    assert any("active classification totals" in error for error in errors)


def test_surplus_tsv_fields() -> None:
    header = "label\toccurrences\tlines\tactivity\tclassification\tdisposition\n"
    row = "x\t1\t1\tactive\tequation\tvalid\tsurplus\n"
    with tempfile.TemporaryDirectory() as directory:
        ledger = Path(directory) / "ledger.tsv"
        ledger.write_text(header + row)
        try:
            audit.read_ledger(ledger)
        except ValueError as error:
            assert "surplus fields" in str(error)
        else:
            raise AssertionError("surplus TSV field was accepted")


def main() -> int:
    test_spaced_theorem_environments()
    test_inheritance_count_regression()
    test_classification_count_regression()
    test_surplus_tsv_fields()
    print("PASS: CPSV16 audit mutations are rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
