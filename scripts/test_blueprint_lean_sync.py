#!/usr/bin/env python3
"""Unit tests for Blueprint Lean-declaration source scanning."""

from pathlib import Path
from tempfile import TemporaryDirectory

from blueprint_lean_sync import collect_file_lean_decls, split_tex_lean_decls


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


if __name__ == "__main__":
    test_split_tex_lean_decls_handles_continuations_and_top_level_commas()
    test_structure_fields_are_declarations()
    print("Blueprint declaration scanner tests passed.")
