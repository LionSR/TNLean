#!/usr/bin/env python3
"""Unit tests for Blueprint Lean-declaration source scanning."""

from pathlib import Path
from tempfile import TemporaryDirectory

from blueprint_lean_sync import (
    BlueprintEntry,
    collect_file_lean_decls,
    find_duplicate_lean_tags,
    split_tex_lean_decls,
)


def test_split_tex_lean_decls_handles_continuations_and_top_level_commas() -> None:
    assert split_tex_lean_decls(
        r"""
Foo.%
  bar (x, y), Baz.qux [a, b], Quux.{u}
"""
    ) == ["Foo.bar (x, y)", "Baz.qux [a, b]", "Quux.{u}"]


def test_structure_fields_are_declarations() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        lean_root = root / "TNLean"
        lean_root.mkdir()
        source = lean_root / "Example.lean"
        source.write_text(
            """namespace Example

structure Witness where
  /-- A colon in prose: this is not a field. -/
  /- An outer comment
    /- with a nested comment -/
    fake : Nat
  -/
  value : Nat
  relation (x : Nat) : x = value
  withLocalBinder :
    ∀ (n : Nat),
      letI : NeZero (n + 1) := ⟨by omega⟩
      True

structure InlineDoc where
  /-- Documentation on the first field. -/ first : Nat
  second : Nat

 theorem after : True := by trivial

end Example
"""
        )
        decls = {decl.fqn: decl for decl in collect_file_lean_decls(source, lean_root)}
        assert "Example.Witness" in decls
        assert decls["Example.Witness.value"].kind == "field"
        assert decls["Example.Witness.relation"].kind == "field"
        assert decls["Example.Witness.withLocalBinder"].kind == "field"
        assert "Example.Witness.letI" not in decls
        assert "Example.Witness.this" not in decls
        assert "Example.Witness.fake" not in decls
        assert decls["Example.InlineDoc.first"].kind == "field"
        assert decls["Example.InlineDoc.second"].kind == "field"
        assert "Example.after" in decls


def test_root_prefixed_decls_escape_namespace() -> None:
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        lean_root = root / "TNLean"
        lean_root.mkdir()
        source = lean_root / "Example.lean"
        source.write_text(
            """namespace Owner

theorem _root_.Other.Thing.escaped : True := by trivial

theorem local_decl : True := by trivial

end Owner
"""
        )
        decls = {decl.fqn: decl for decl in collect_file_lean_decls(source, lean_root)}
        # `_root_.` re-qualifies the declaration away from the enclosing
        # namespace: the fully-qualified name is the remainder, not
        # `Owner._root_.…`.
        assert "Other.Thing.escaped" in decls
        assert "Owner._root_.Other.Thing.escaped" not in decls
        assert "Owner.local_decl" in decls


def test_duplicate_lean_tags_are_reported_once_per_declaration() -> None:
    def entry(file: str, line: int, decl: str) -> BlueprintEntry:
        return BlueprintEntry(
            file=file,
            line=line,
            env_type="lean-tag",
            label=None,
            lean_decl=decl,
            has_leanok=False,
            proof_has_leanok=False,
        )

    refs = [
        entry("src/chapter/ch01.tex", 3, "Owner.decl"),
        entry("src/chapter/ch02.tex", 7, "Owner.decl"),
        entry("src/chapter/ch01.tex", 9, "Unique.decl"),
    ]
    duplicates = find_duplicate_lean_tags(refs)
    assert [decl for decl, _ in duplicates] == ["Owner.decl"]
    assert [(e.file, e.line) for e in duplicates[0][1]] == [
        ("src/chapter/ch01.tex", 3),
        ("src/chapter/ch02.tex", 7),
    ]
    assert find_duplicate_lean_tags(refs[1:]) == []


if __name__ == "__main__":
    test_split_tex_lean_decls_handles_continuations_and_top_level_commas()
    test_structure_fields_are_declarations()
    test_duplicate_lean_tags_are_reported_once_per_declaration()
    print("Blueprint declaration scanner tests passed.")
