#!/usr/bin/env python3
"""Regression tests for the deterministic TNLean import-aggregator generator."""

from __future__ import annotations

import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).with_name("generate_import_aggregators.py")
SPEC = importlib.util.spec_from_file_location("generate_import_aggregators", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class ImportAggregatorGeneratorTests(unittest.TestCase):
    def write(self, root: Path, relative: str, content: str) -> Path:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def generated_snapshot(self, root: Path) -> dict[str, bytes]:
        paths = [root / "TNLean.lean", *(root / "TNLean").rglob("*.lean")]
        return {
            path.relative_to(root).as_posix(): path.read_bytes()
            for path in paths
            if GENERATOR.is_generated(path)
        }

    def test_idempotent_and_preserves_shadowing_content(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "TNLean/Foo/Basic.lean", "def foo : Nat := 1\n")
            shadow = self.write(root, "TNLean/Shadow.lean", "def shadow : Nat := 2\n")
            self.write(root, "TNLean/Shadow/Leaf.lean", "def leaf : Nat := 3\n")
            self.write(root, "TNLean/Archive/Old.lean", "def old : Nat := 4\n")
            shadow_before = shadow.read_bytes()

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            first_snapshot = self.generated_snapshot(root)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            second_snapshot = self.generated_snapshot(root)

            self.assertEqual(first_snapshot, second_snapshot)
            self.assertEqual(shadow.read_bytes(), shadow_before)
            self.assertNotIn("TNLean/Shadow.lean", first_snapshot)
            self.assertEqual(set(first_snapshot), {"TNLean.lean", "TNLean/Foo.lean"})
            root_text = (root / "TNLean.lean").read_text(encoding="utf-8")
            self.assertIn("import TNLean.Foo\n", root_text)
            self.assertIn("import TNLean.Shadow\n", root_text)
            self.assertIn("import TNLean.Shadow.Leaf\n", root_text)
            self.assertNotIn("Archive", root_text)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=True), 0)

    def test_write_rejects_incomplete_root_coverage(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "TNLean/Foo/Basic.lean", "def foo : Nat := 1\n")
            output = io.StringIO()
            with mock.patch.object(
                GENERATOR, "check_root_coverage", return_value=["TNLean.Foo.Basic"]
            ), contextlib.redirect_stdout(output):
                self.assertEqual(GENERATOR.update(root, check=False), 1)
            self.assertIn("production module is not reachable", output.getvalue())
            self.assertFalse((root / "TNLean.lean").exists())

    def test_check_rejects_out_of_date_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "TNLean/Foo/Basic.lean", "def foo : Nat := 1\n")
            with contextlib.redirect_stdout(io.StringIO()):
                GENERATOR.update(root, check=False)
            aggregator = root / "TNLean/Foo.lean"
            aggregator.write_text(
                aggregator.read_text(encoding="utf-8") + "import TNLean.Extra\n",
                encoding="utf-8",
            )

            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(GENERATOR.update(root, check=True), 1)
            self.assertIn("out-of-date generated aggregator: TNLean/Foo.lean", output.getvalue())


if __name__ == "__main__":
    unittest.main()
