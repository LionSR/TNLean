#!/usr/bin/env python3
"""Tests for the change-set selection in scripts/ci_lean_checks.py."""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "ci_lean_checks", Path(__file__).with_name("ci_lean_checks.py"))
ci = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(ci)


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout.strip()


class ParseImportsTest(unittest.TestCase):
    def test_header_only(self) -> None:
        text = ("/-\nCopyright\n-/\nimport A.B -- see D\nimport C\n\n/-! doc -/\n"
                "import NotHeader\n")
        self.assertEqual(ci.parse_imports(text), ["A.B", "C"])

    def test_module_system_keywords(self) -> None:
        text = "module\n\npublic import A\nmeta import B\nimport C D\n"
        self.assertEqual(ci.parse_imports(text), ["A", "B", "C", "D"])


class SelectTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        files = {
            "TNLean/Core.lean": "import Mathlib\n",
            "TNLean/Uses.lean": "import TNLean.Core\n",
            "TNLean/Other.lean": "import Mathlib\n",
            "TNLean/Archive/Old.lean": "import TNLean.Core\n",
            "TNLeanTest/Support/Fixture.lean": "import TNLean.Other\n",
            "TNLeanTest/UsesTest.lean": "import TNLean.Uses\n",
            "TNLeanTest/FixtureTest.lean": "import TNLeanTest.Support.Fixture\n",
            "TNLeanTest/Unrelated.lean": "import Mathlib\n",
        }
        for path, text in files.items():
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        git(self.root, "init", "-q")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t",
            "commit", "-qm", "base")
        self.base = git(self.root, "rev-parse", "HEAD")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def change(self, path: str, text: str) -> None:
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t",
            "commit", "-qm", "change")

    def select(self, base: str | None):
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            return ci.select(Path("."), base)[:3]
        finally:
            os.chdir(cwd)

    def test_transitive_dependents_are_selected(self) -> None:
        self.change("TNLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean"])

    def test_imported_test_fixture_runs_first(self) -> None:
        self.change("TNLean/Other.lean", "import Mathlib\n-- edit\n")
        _, _, tests = self.select(self.base)
        self.assertEqual(tests, ["TNLeanTest/Support/Fixture.lean",
                                 "TNLeanTest/FixtureTest.lean"])

    def test_changed_test_brings_its_fixture(self) -> None:
        self.change("TNLeanTest/FixtureTest.lean",
                    "import TNLeanTest.Support.Fixture\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(tests, ["TNLeanTest/Support/Fixture.lean",
                                 "TNLeanTest/FixtureTest.lean"])

    def test_archive_is_not_built_early(self) -> None:
        self.change("TNLean/Archive/Old.lean", "import TNLean.Core\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources, tests), ([], [], []))

    def test_new_module_and_test(self) -> None:
        (self.root / "TNLean/New.lean").write_text("import TNLean.Core\n")
        self.change("TNLeanTest/NewTest.lean", "import TNLean.New\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.New"])
        self.assertEqual(tests, ["TNLeanTest/NewTest.lean"])

    def test_dependency_pin_runs_every_test(self) -> None:
        self.change("lake-manifest.json", "{}\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(len(tests), 4)
        self.assertLess(tests.index("TNLeanTest/Support/Fixture.lean"),
                        tests.index("TNLeanTest/FixtureTest.lean"))

    def test_full_run_change_preserves_changed_production_checks(self) -> None:
        for path in ci.FULL_RUN_PATHS:
            with self.subTest(path=path):
                base = git(self.root, "rev-parse", "HEAD")
                (self.root / "TNLean/Core.lean").write_text(
                    f"import Mathlib\n-- changed with {path}\n")
                self.change(path, "changed\n")
                early, sources, tests = self.select(base)
                self.assertEqual(early, ["TNLean.Core"])
                self.assertEqual(sources, ["TNLean/Core.lean"])
                self.assertEqual(len(tests), 4)
                self.assertLess(tests.index("TNLeanTest/Support/Fixture.lean"),
                                tests.index("TNLeanTest/FixtureTest.lean"))

    def test_no_base_runs_every_test(self) -> None:
        _, _, tests = self.select(None)
        self.assertEqual(len(tests), 4)

    def test_levels_respect_imports(self) -> None:
        _, _, tests = self.select(None)
        files = ci.lean_files(self.root)
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            graph = ci.import_graph(Path("."), files)
        finally:
            os.chdir(cwd)
        batches = ci.levels(tests, graph)
        self.assertIn("TNLeanTest/Support/Fixture.lean", batches[0])
        self.assertIn("TNLeanTest/FixtureTest.lean", batches[1])


if __name__ == "__main__":
    unittest.main()
