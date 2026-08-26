#!/usr/bin/env python3
"""Unit tests for Blueprint Lean-declaration source scanning."""

from pathlib import Path
from tempfile import TemporaryDirectory

from blueprint_lean_sync import collect_file_lean_decls


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

 theorem after : True := by trivial

end Example
"""
        )
        decls = {decl.fqn: decl for decl in collect_file_lean_decls(source, lean_root)}
        assert "Example.Witness" in decls
        assert decls["Example.Witness.value"].kind == "field"
        assert decls["Example.Witness.relation"].kind == "field"
        assert "Example.Witness.this" not in decls
        assert "Example.Witness.fake" not in decls
        assert "Example.after" in decls


if __name__ == "__main__":
    test_structure_fields_are_declarations()
    print("Blueprint declaration scanner tests passed.")
