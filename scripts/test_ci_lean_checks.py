#!/usr/bin/env python3
"""Tests for the change-set selection in scripts/ci_lean_checks.py."""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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


class EarlyModulesTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        (self.root / "TNLean").mkdir()
        self.aggregator = "TNLean/Aggregator.lean"
        self.other = "TNLean/Other.lean"
        (self.root / self.aggregator).write_text("import TNLean.Other\n")

    def test_no_changed_sources(self) -> None:
        self.assertEqual(ci.early_modules(self.root, []), [])

    def test_all_import_only_targets_are_preserved(self) -> None:
        (self.root / self.other).write_text("import Mathlib\n")
        self.assertEqual(ci.early_modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Aggregator", "TNLean.Other"])

    def test_non_import_commands_and_uncertain_syntax_stay_early(self) -> None:
        cases = {
            "definition": "import Mathlib\ndef answer := 42\n",
            "theorem": "import Mathlib\ntheorem ok : True := by trivial\n",
            "open": "import Mathlib\nopen Nat\n",
            "namespace": "import Mathlib\nnamespace N\nend N\n",
            "option": "import Mathlib\nset_option maxRecDepth 2000\n",
            "command": "import Mathlib\nrun_cmd pure ()\n",
            "directive": "import Mathlib\n#check Nat\n",
            "string": 'import Mathlib\ndef s := "-- /-"\n',
            "empty": "",
            "comments_only": "/- import Mathlib -/\n-- def x := 1\n",
            "unterminated_comment": "import Mathlib\n/- unfinished\n",
            "unmatched_comment_end": "import Mathlib\n-/\n",
            "module": "module\nimport Mathlib\n",
            "prelude": "prelude\nimport Mathlib\n",
            "public_import": "public import Mathlib\n",
            "private_import": "private import Mathlib\n",
            "meta_import": "meta import Mathlib\n",
            "multiline_import": "import\n  Mathlib\n",
            "multi_module_import": "import Mathlib TNLean.Other\n",
        }
        for name, source in cases.items():
            with self.subTest(name=name):
                (self.root / self.other).write_text(source)
                self.assertEqual(
                    ci.early_modules(self.root, [self.aggregator, self.other]),
                    ["TNLean.Other"])

    def test_comments_do_not_make_an_aggregator_substantive(self) -> None:
        (self.root / self.aggregator).write_text(
            "/- header /- def hidden := 1 -/ still a comment -/\n\n"
            "  import TNLean.Other -- theorem hidden : True := by trivial\n"
            "import /- nested /- comment -/ -/ Mathlib\n")
        (self.root / self.other).write_text("import Mathlib\ndef answer := 42\n")
        self.assertEqual(ci.early_modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_invalid_utf8_even_inside_a_comment_stays_early(self) -> None:
        (self.root / self.other).write_bytes(b"import Mathlib\n-- invalid \xff\n")
        self.assertEqual(ci.early_modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_missing_file_stays_early(self) -> None:
        self.assertEqual(ci.early_modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_read_failure_stays_early(self) -> None:
        original_read = Path.read_text

        def read(path, *args, **kwargs):
            if path == self.root / self.other:
                raise PermissionError("unreadable source")
            return original_read(path, *args, **kwargs)

        with patch.object(Path, "read_text", read):
            self.assertEqual(
                ci.early_modules(self.root, [self.aggregator, self.other]),
                ["TNLean.Other"])


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
            "scripts/core_regression.lean": "import TNLean.Uses\n",
            "scripts/LintStyle.lean": "import TNLean.Core\n",
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

    def select(self, base: str | None, with_graph: bool = False):
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            result = ci.select(Path("."), base)
            return result if with_graph else result[:3]
        finally:
            os.chdir(cwd)

    def test_transitive_dependents_are_selected(self) -> None:
        self.change("TNLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                 "scripts/core_regression.lean"])

    def test_mixed_leaf_and_aggregator_preserve_strict_tests_and_graph(self) -> None:
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        expected_graph = ci.import_graph(self.root, ci.lean_files(self.root))
        early, sources, tests, graph = self.select(self.base, with_graph=True)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertNotIn("TNLean.Uses", early)
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                "scripts/core_regression.lean"])
        self.assertEqual(graph, expected_graph)
        self.assertEqual(graph["TNLean.Uses"], {"TNLean.Core", "TNLean.Other"})

    def test_aggregator_only_keeps_early_strict_and_tests(self) -> None:
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Uses"])
        self.assertEqual(sources, ["TNLean/Uses.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                "scripts/core_regression.lean"])

    def test_multiple_substantive_sources_keep_sorted_order(self) -> None:
        self.change("TNLean/ZProof.lean", "import Mathlib\ndef z := 0\n")
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.ZProof\n")
        self.change("TNLean/All.lean", "import TNLean.Uses\n")
        early, sources, _ = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core", "TNLean.ZProof"])
        self.assertEqual(sources, ["TNLean/All.lean", "TNLean/Core.lean",
                                  "TNLean/Uses.lean", "TNLean/ZProof.lean"])

    def test_new_proof_and_aggregator_keep_proof_early(self) -> None:
        self.change("TNLean/New.lean", "import TNLean.Core\ntheorem ok : True := by trivial\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.New\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.New"])
        self.assertEqual(sources, ["TNLean/New.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                "scripts/core_regression.lean"])

    def test_pin_change_with_mixed_sources_keeps_every_test(self) -> None:
        self.change("TNLeanTest/Axioms.lean", "import TNLean.Core\n#print axioms True.intro\n")
        self.change("lake-manifest.json", "{}\n")
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["TNLeanTest/Axioms.lean",
                                "TNLeanTest/Support/Fixture.lean",
                                "TNLeanTest/FixtureTest.lean", "TNLeanTest/Unrelated.lean",
                                "TNLeanTest/UsesTest.lean", "scripts/core_regression.lean"])

    def test_invalid_utf8_source_is_strict_and_early(self) -> None:
        (self.root / "TNLean/Core.lean").write_bytes(b"import Mathlib\n-- invalid \xff\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                "scripts/core_regression.lean"])

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

    def test_changed_regression_script_is_selected(self) -> None:
        self.change("scripts/core_regression.lean", "import TNLean.Uses\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources, tests), ([], [], ["scripts/core_regression.lean"]))

    def test_deleted_module_marks_its_importers(self) -> None:
        (self.root / "TNLean/Uses.lean").unlink()
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "delete")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean", "scripts/core_regression.lean"])

    def test_renamed_module_marks_importers_of_the_old_name(self) -> None:
        git(self.root, "mv", "TNLean/Uses.lean", "TNLean/Renamed.lean")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "rename")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Renamed"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean", "scripts/core_regression.lean"])

    def test_deleted_test_fixture_marks_its_importers(self) -> None:
        (self.root / "TNLeanTest/Support/Fixture.lean").unlink()
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "delete")
        _, _, tests = self.select(self.base)
        self.assertEqual(tests, ["TNLeanTest/FixtureTest.lean"])

    def test_dependency_pin_runs_every_test(self) -> None:
        self.change("lake-manifest.json", "{}\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(len(tests), 5)
        self.assertNotIn("scripts/LintStyle.lean", tests)
        self.assertLess(tests.index("TNLeanTest/Support/Fixture.lean"),
                        tests.index("TNLeanTest/FixtureTest.lean"))

    def test_pin_change_keeps_changed_sources_strict(self) -> None:
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.change("TNLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), (["TNLean.Core"], ["TNLean/Core.lean"]))
        self.assertEqual(len(tests), 5)

    def test_lakefile_lean_runs_every_test(self) -> None:
        self.change("lakefile.lean", "import Lake\n")
        _, _, tests = self.select(self.base)
        self.assertEqual(len(tests), 5)

    def test_no_base_runs_every_test(self) -> None:
        _, _, tests = self.select(None)
        self.assertEqual(len(tests), 5)

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


class EarlyBuildTest(unittest.TestCase):
    """Run early_build against a stand-in `lake`."""

    def setUp(self) -> None:
        import os
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.dir = Path(tmp.name)
        self.old_path = os.environ["PATH"]
        self.addCleanup(os.environ.__setitem__, "PATH", self.old_path)
        os.environ["PATH"] = f"{self.dir}:{self.old_path}"
        self.log = self.dir / "lake-build.log"

    def lake(self, body: str) -> None:
        path = self.dir / "lake"
        path.write_text("#!/bin/bash\necho building \"$@\"\n" + body)
        path.chmod(0o755)

    def test_success_and_log(self) -> None:
        self.lake("exit 0\n")
        self.assertEqual(ci.early_build(["TNLean.Core"], self.log, 0), 0)
        self.assertIn("building --fail-fast build TNLean.Core", self.log.read_text())

    def test_mixed_targets_do_not_request_aggregator_from_lake(self) -> None:
        (self.dir / "TNLean").mkdir()
        (self.dir / "TNLean/Aggregator.lean").write_text(
            "import TNLean.ZLeaf\nimport TNLean.Unchanged\n")
        (self.dir / "TNLean/ZLeaf.lean").write_text("import Mathlib\ndef answer := 42\n")
        targets = ci.early_modules(
            self.dir, ["TNLean/Aggregator.lean", "TNLean/ZLeaf.lean"])
        self.lake("exit 0\n")
        self.assertEqual(ci.early_build(targets, self.log, 0), 0)
        self.assertEqual(self.log.read_text(), "building --fail-fast build TNLean.ZLeaf\n")

    def test_build_failure_fails_the_step(self) -> None:
        self.lake("exit 3\n")
        self.assertEqual(ci.early_build(["TNLean.Core"], self.log, 0), 3)

    def test_budget_kills_descendants_that_ignore_sigterm(self) -> None:
        # lake exits on SIGTERM, but its compiler child ignores it and holds the
        # output pipe; the step must still end promptly.
        self.lake("bash -c 'trap \"\" TERM; sleep 60' &\n"
                  "trap 'exit 143' TERM\nsleep 60 & wait\n")
        import io, time
        from contextlib import redirect_stdout
        start = time.monotonic()
        with redirect_stdout(io.StringIO()):
            code = ci.early_build(["TNLean.Core"], self.log, 1)
        self.assertEqual(code, 0)
        self.assertLess(time.monotonic() - start, 20)

    def test_budget_exceeded_is_a_warning(self) -> None:
        self.lake("sleep 30\n")
        import io
        from contextlib import redirect_stdout
        out = io.StringIO()
        with redirect_stdout(out):
            code = ci.early_build(["TNLean.Core"], self.log, 1)
        self.assertEqual(code, 0)
        self.assertIn("::warning::Early build stopped after 1s", out.getvalue())


if __name__ == "__main__":
    unittest.main()
