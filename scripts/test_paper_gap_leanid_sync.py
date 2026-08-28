#!/usr/bin/env python3
"""Unit tests for paper-gap ``\\leanid`` declaration extraction."""

from pathlib import Path
from tempfile import TemporaryDirectory

from paper_gap_leanid_sync import (
    collect_paper_gap_leanid_refs,
    lean_decl_head,
    write_decl_list,
)


def _heads(source: str, filename: str = "example.tex") -> list[str]:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        paper_gaps = root / "docs" / "paper-gaps"
        paper_gaps.mkdir(parents=True)
        (paper_gaps / filename).write_text(source)
        return [ref.head for ref in collect_paper_gap_leanid_refs(paper_gaps, root)]


def _refs(source: str):
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        paper_gaps = root / "docs" / "paper-gaps"
        paper_gaps.mkdir(parents=True)
        (paper_gaps / "example.tex").write_text(source)
        return collect_paper_gap_leanid_refs(paper_gaps, root)


def test_comma_lists_percent_continuations_and_applied_arguments() -> None:
    assert _heads(
        r"""
\leanid{MPOTensor.%
  transportedVerticalSectorT_isKrausDirectSumMap,
  WordTupleSpanTop S.basis 1, MPSTensor.majumdarGhosh\_left\_canonical}
"""
    ) == [
        "MPOTensor.transportedVerticalSectorT_isKrausDirectSumMap",
        "WordTupleSpanTop",
        "MPSTensor.majumdarGhosh_left_canonical",
    ]


def test_comments_and_nonmatching_macros_do_not_create_references() -> None:
    assert _heads(
        r"""
% \leanid{Ghost.Name}
\leanidentifier{Also.Ghost}
\leanid
\leanid { Real.Name }
"""
    ) == ["Real.Name"]


def test_head_stops_before_local_type_or_arguments() -> None:
    assert lean_decl_head("hP : IsPeriodic m A") == "hP"
    assert lean_decl_head("Matrix.exists_unitary_conj x y") == "Matrix.exists_unitary_conj"
    assert lean_decl_head("TNLean.PEPS.regionBoundaryLabel_R₂_eq_of_union_sdiff)") == (
        "TNLean.PEPS.regionBoundaryLabel_R₂_eq_of_union_sdiff"
    )


def test_nested_application_commas_do_not_create_extra_heads() -> None:
    assert _heads(
        r"""
\leanid{Outer.head (alpha, beta), Inner.head [gamma, delta],
  Wrapped.head {x, y}}
"""
    ) == ["Outer.head", "Inner.head", "Wrapped.head"]


def test_source_locations_point_to_macro_start() -> None:
    refs = _refs("\n  prose\n    \\leanid{Located.Name}\n")
    assert len(refs) == 1
    assert refs[0].file == "docs/paper-gaps/example.tex"
    assert refs[0].line == 3
    assert refs[0].column == 5


def test_duplicates_are_preserved_in_refs_and_deduplicated_in_output() -> None:
    refs = _refs(r"\leanid{Dup.Name, Dup.Name}")
    assert [ref.head for ref in refs] == ["Dup.Name", "Dup.Name"]
    with TemporaryDirectory() as tmp:
        output = Path(tmp) / "decls"
        write_decl_list(refs, output)
        assert output.read_text() == "Dup.Name\n"


def test_empty_and_malformed_payloads_are_ignored() -> None:
    assert _heads(
        r"""
\leanid{}
\leanid{  , , }
\leanid{Unclosed.Name
"""
    ) == []


def test_intentional_policy_placeholders_are_scoped_to_their_files() -> None:
    assert _heads(r"\leanid{modelCorrected}", "template.tex") == []
    assert _heads(r"\leanid{someDeclaration}", "policy.tex") == []
    assert _heads(r"\leanid{modelCorrected, someDeclaration}") == [
        "modelCorrected",
        "someDeclaration",
    ]


if __name__ == "__main__":
    test_comma_lists_percent_continuations_and_applied_arguments()
    test_comments_and_nonmatching_macros_do_not_create_references()
    test_head_stops_before_local_type_or_arguments()
    test_nested_application_commas_do_not_create_extra_heads()
    test_source_locations_point_to_macro_start()
    test_duplicates_are_preserved_in_refs_and_deduplicated_in_output()
    test_empty_and_malformed_payloads_are_ignored()
    test_intentional_policy_placeholders_are_scoped_to_their_files()
    print("Paper-gap leanid sync tests passed.")
