#!/usr/bin/env python3
"""Unit tests for the zero-reference declaration scanner."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import zero_reference_scan as scan

LEAN_FILE = """\
/-
Copyright header.
-/
import Mathlib

/-! A module docstring that mentions theorem. and a sentence ending in back.
It also mentions `mentionedOnlyInProse` to show prose does not count twice. -/

namespace Demo

/-- Used by `liveConsumer`. -/
theorem liveHelper : True := trivial

theorem liveConsumer : True := liveHelper

/-- Nothing refers to this. -/
theorem deadLeaf (n : ℕ) : n = n :=
  rfl

theorem deadRoot : True := by
  exact deadChainHelper

private theorem deadChainHelper : True := trivial

@[simp] theorem simpLemma : True := trivial

instance : Inhabited Unit := ⟨()⟩

/-- Cited by the blueprint. -/
theorem blueprintOnly : True := trivial

-- theorem commentedOut : False := sorry

theorem docsOnly' : True := trivial

/-- Recursive and unused: its only other occurrence is its own recursive call. -/
theorem deadRecursive : (n : ℕ) → n = n
  | 0 => rfl
  | n + 1 => by have := deadRecursive n; rfl

  theorem indentedDead : True := trivial

end Demo
"""

BLUEPRINT = r"""
\begin{theorem}
  \lean{Demo.blueprintOnly}
\end{theorem}
"""

DOC = "The name docsOnly' appears here.\n"


class ZeroReferenceScanTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "TNLean" / "Demo").mkdir(parents=True)
        (self.root / "TNLean" / "Demo" / "Basic.lean").write_text(LEAN_FILE, encoding="utf-8")
        (self.root / "blueprint" / "src").mkdir(parents=True)
        (self.root / "blueprint" / "src" / "ch.tex").write_text(BLUEPRINT, encoding="utf-8")
        (self.root / "docs").mkdir()
        (self.root / "docs" / "note.md").write_text(DOC, encoding="utf-8")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def names(self, **kwargs: object) -> list[str]:
        return [d.name for d in scan.find_zero_reference(self.root, **kwargs)]

    def test_first_round_reports_only_unreferenced_declarations(self) -> None:
        self.assertEqual(
            self.names(transitive=False),
            ["deadLeaf", "deadRoot", "deadRecursive", "indentedDead"],
        )

    def test_fixed_point_reports_helpers_used_only_by_dead_code(self) -> None:
        self.assertEqual(
            self.names(),
            ["deadLeaf", "deadRoot", "deadChainHelper", "deadRecursive", "indentedDead"],
        )

    def test_attributed_declarations_are_opt_in(self) -> None:
        self.assertNotIn("simpLemma", self.names())
        self.assertIn("simpLemma", self.names(include_attributed=True))

    def test_headers_are_read_from_code_not_comments(self) -> None:
        decls = scan.collect_declarations(
            self.root / "TNLean" / "Demo" / "Basic.lean", "TNLean/Demo/Basic.lean", True
        )
        kinds = {d.name: d.kind for d in decls}
        self.assertNotIn("commentedOut", kinds)
        self.assertNotIn("theorem.", kinds)
        self.assertNotIn("back.", kinds)
        self.assertIn("docsOnly'", kinds)
        self.assertEqual(kinds["deadLeaf"], "theorem")

    def test_extent_covers_docstring_header_and_body(self) -> None:
        text = LEAN_FILE
        decl = next(
            d
            for d in scan.collect_declarations(
                self.root / "TNLean" / "Demo" / "Basic.lean", "TNLean/Demo/Basic.lean", True
            )
            if d.name == "deadLeaf"
        )
        extent = text[decl.start : decl.end]
        self.assertTrue(extent.startswith("/-- Nothing refers to this. -/"))
        self.assertIn("  rfl\n", extent)
        self.assertNotIn("deadRoot", extent)

    def test_extent_stops_at_an_indented_following_header(self) -> None:
        decls = scan.collect_declarations(
            self.root / "TNLean" / "Demo" / "Basic.lean", "TNLean/Demo/Basic.lean", True
        )
        recursive = next(d for d in decls if d.name == "deadRecursive")
        self.assertNotIn("indentedDead", LEAN_FILE[recursive.start : recursive.end])

    def test_archive_is_excluded_by_default(self) -> None:
        archive = self.root / "TNLean" / "Archive"
        archive.mkdir()
        (archive / "Old.lean").write_text("theorem archivedDead : True := trivial\n")
        self.assertNotIn("archivedDead", self.names())
        self.assertIn("archivedDead", self.names(include_archive=True))

    def test_cli_runs_and_lists_candidates(self) -> None:
        import contextlib
        import io

        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = scan.main(["--root", str(self.root)])
        self.assertEqual(code, 0)
        lines = buffer.getvalue().splitlines()
        self.assertEqual(lines[0], "5 declarations with no reference outside their own definition")
        self.assertEqual(lines[1], "TNLean/Demo/Basic.lean:17: theorem deadLeaf")


if __name__ == "__main__":
    unittest.main()
