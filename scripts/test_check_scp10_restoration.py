"""Source-closure guard tests; no Lean or network needed."""

from pathlib import Path
import tempfile
import unittest

from check_scp10_restoration import source_closure


class SourceClosureTests(unittest.TestCase):
    def test_transitive_missing_source_rejects_stale_object(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "TNLean").mkdir()
            (root / "TNLean/A.lean").write_text("import TNLean.B\n")
            (root / "TNLean/B.lean").write_text("public import TNLean.C\n")
            stale = root / ".lake/build/lib/lean/TNLean/C.olean"
            stale.parent.mkdir(parents=True)
            stale.touch()
            visited, missing = source_closure(root, ["TNLean.A"])
            self.assertEqual(visited, ["TNLean.A", "TNLean.B", "TNLean.C"])
            self.assertEqual(missing, ["TNLean.C"])

    def test_comments_do_not_create_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "TNLean").mkdir()
            (root / "TNLean/A.lean").write_text(
                "/- /- nested -/\nimport TNLean.Missing\n-/\n"
                "-- import TNLean.AlsoMissing\nimport Mathlib.Data.Nat.Basic\n"
            )
            self.assertEqual(source_closure(root, ["TNLean.A"]), (["TNLean.A"], []))

    def test_missing_root_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(
                source_closure(Path(directory), ["TNLean.Absent"]),
                (["TNLean.Absent"], ["TNLean.Absent"]),
            )

    def test_unknown_import_syntax_is_not_silently_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "TNLean").mkdir()
            (root / "TNLean/A.lean").write_text("import TNLean.B TNLean.C\n")
            with self.assertRaisesRegex(ValueError, "Unsupported import syntax"):
                source_closure(root, ["TNLean.A"])


if __name__ == "__main__":
    unittest.main()
