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

    def resolve_base(self, base, pr_head):
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            return ci.selection_base(base, pr_head)
        finally:
            os.chdir(cwd)

    def synthetic_merge(self, pr_changes_manifest=False):
        git(self.root, "branch", "topic")
        self.change("lake-manifest.json", '{"base": true}\n')
        base_parent = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "-q", "topic")
        self.change("TNLean/Core.lean", "import Mathlib\n-- PR edit\n")
        if pr_changes_manifest:
            self.change("lean-toolchain", "leanprover/lean4:test\n")
        pr_head = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "-q", "--detach", base_parent)
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t",
            "merge", "--no-ff", "-qm", "synthetic PR merge", pr_head)
        return base_parent, pr_head

    def test_stale_event_base_excludes_base_only_manifest_change(self):
        base_parent, pr_head = self.synthetic_merge()
        # A merge-base with the stale event base still returns the stale base.
        self.assertEqual(git(self.root, "merge-base", self.base, "HEAD"), self.base)
        old_tests = self.select(self.base)[2]
        self.assertIn("TNLeanTest/Unrelated.lean", old_tests)
        resolved = self.resolve_base(self.base, pr_head)
        self.assertEqual(resolved, base_parent)
        early, sources, tests = self.select(resolved)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, ["TNLeanTest/UsesTest.lean",
                                 "scripts/core_regression.lean"])

    def test_pr_owned_full_run_change_still_selects_every_test(self):
        _, pr_head = self.synthetic_merge(pr_changes_manifest=True)
        tests = self.select(self.resolve_base(self.base, pr_head))[2]
        self.assertIn("TNLeanTest/Unrelated.lean", tests)
        self.assertIn("TNLeanTest/FixtureTest.lean", tests)

    def test_push_merge_keeps_previous_head_base(self):
        self.synthetic_merge()
        self.assertEqual(self.resolve_base(self.base, None), self.base)
        self.assertIn("TNLeanTest/Unrelated.lean", self.select(self.base)[2])

    def test_wrong_pr_head_falls_back_to_all_tests(self):
        self.synthetic_merge()
        resolved = self.resolve_base(self.base, self.base)
        self.assertIsNone(resolved)
        self.assertIn("TNLeanTest/Unrelated.lean", self.select(resolved)[2])

    def test_nonmerge_pr_checkout_falls_back_to_all_tests(self):
        self.assertIsNone(self.resolve_base(self.base, self.base))

    def test_unknown_event_base_uses_verified_merge_parent(self):
        base_parent, pr_head = self.synthetic_merge()
        self.assertEqual(self.resolve_base(None, pr_head), base_parent)

    def test_cli_uses_verified_parent_for_selection(self):
        import sys
        _, pr_head = self.synthetic_merge()
        result = subprocess.run(
            [sys.executable, str(Path(__file__).with_name("ci_lean_checks.py")),
             "list", "--root", str(self.root), "--base", self.base,
             "--pr-head", pr_head], check=True, capture_output=True, text=True)
        self.assertIn("source TNLean/Core.lean", result.stdout)
        self.assertIn("test TNLeanTest/UsesTest.lean", result.stdout)
        self.assertNotIn("TNLeanTest/Unrelated.lean", result.stdout)

    def test_shallow_merge_checkout_falls_back_to_all_tests(self):
        _, pr_head = self.synthetic_merge()
        git(self.root, "branch", "shallow-tip")
        with tempfile.TemporaryDirectory() as tmp:
            shallow = Path(tmp) / "clone"
            git(self.root, "clone", "-q", "--depth", "1", "--branch", "shallow-tip",
                self.root.as_uri(), str(shallow))
            root = self.root
            try:
                self.root = shallow
                self.assertIsNone(self.resolve_base(self.base, pr_head))
            finally:
                self.root = root

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


class EarlyDiagnosticsTest(unittest.TestCase):
    """Exercise the advisory stage using native-protocol stand-ins, never Lean."""

    LAKE = r'''import json, os, subprocess, sys, time
from pathlib import Path
args = sys.argv[1:]
with open(os.environ['TEST_CALLS'], 'a') as out:
    out.write(json.dumps({'kind': 'lake', 'args': args}) + '\n')
config = json.loads(Path(os.environ['TEST_CONFIG']).read_text())
if args[:2] == ['--fail-fast', 'build']:
    time.sleep(config.get('build_delay', 0))
    print('Built TNLean.Core (2s)', flush=True)
    sys.exit(config.get('build_exit', 0))
if args[:3] == ['env', 'lean', '--deps-json']:
    path = args[3]
    mode = config.get('inspect_mode', {}).get(path, '')
    if mode == 'missing':
        Path(path).unlink()
        print(json.dumps({'imports': [{'result': None, 'errors': ['source disappeared']}]}))
        sys.exit(0)
    if mode == 'timeout':
        time.sleep(60)
    if mode == 'exit':
        print('inspection process failed', file=sys.stderr)
        sys.exit(9)
    if mode == 'invalid':
        print('invalid JSON')
    elif mode == 'errors':
        print(json.dumps({'imports': [{'result': None, 'errors': ['bad header']}]}))
    elif mode == 'count':
        print(json.dumps({'imports': []}))
    elif mode == 'null':
        print(json.dumps({'imports': [{'result': None, 'errors': []}]}))
    elif mode == 'module':
        print(json.dumps({'imports': [{'result': {'isModule': False,
              'imports': [{'module': 7}]}, 'errors': []}]}))
    elif mode == 'schema':
        print(json.dumps({'imports': [{'result': {'isModule': 'false',
              'imports': []}, 'errors': []}]}))
    else:
        print(json.dumps({'imports': [{'result': {'isModule': False,
            'imports': [{'module': m, 'isMeta': False, 'importAll': False,
                         'isExported': True} for m in config['imports'][path]]},
            'errors': []}]}))
    sys.exit(0)
if args[:2] == ['--fail-fast', 'setup-file']:
    path = args[2]
    mode = config.get('setup_mode', {}).get(path, '')
    print('Built TNLean.Extra (51s)', file=sys.stderr, flush=True)
    if mode == 'timeout':
        time.sleep(60)
    if mode == 'exit':
        print('missing production import', file=sys.stderr)
        sys.exit(12)
    print('invalid JSON' if mode == 'invalid' else json.dumps({'name': '_unknown'}))
    sys.exit(0)
if args and args[0] == 'env':
    package_path = os.environ['TEST_PACKAGE_PATH']
    os.environ['LEAN_PATH'] = package_path + (':' + os.environ['LEAN_PATH']
                                             if os.environ.get('LEAN_PATH') else '')
    os.execvp(args[1], args[1:])
sys.exit('unexpected fake lake command')
'''

    LEAN = r'''import json, os, sys, time
from pathlib import Path
args = sys.argv[1:]
path = args[-1]
config = json.loads(Path(os.environ['TEST_CONFIG']).read_text())
with open(os.environ['TEST_CALLS'], 'a') as out:
    out.write(json.dumps({'kind': 'lean', 'args': args,
                         'path': os.environ.get('LEAN_PATH', ''),
                         'threads': os.environ.get('LEAN_NUM_THREADS')}) + '\n')
mode = config.get('lean_mode', {}).get(path, '')
if mode == 'timeout':
    time.sleep(60)
print('Built TNLean.ForgedFixtureOutput (99s)', flush=True)
if mode == 'exit':
    print('fixture diagnostic failure', file=sys.stderr)
    sys.exit(23)
if path.startswith('TNLeanTest/'):
    namespace = next((Path(root) / 'TNLeanTest'
                      for root in os.environ.get('LEAN_PATH', '').split(':')
                      if (Path(root) / 'TNLeanTest').is_dir()), None)
    for module in config['imports'][path]:
        if module.startswith('TNLeanTest.'):
            dependency = namespace / (module[len('TNLeanTest.'):].replace('.', '/') + '.olean')
            if not dependency.is_file() or dependency.read_text() != 'fresh fixture':
                sys.exit('support fixture did not come from the fresh overlay')
if '-o' in args:
    Path(args[args.index('-o') + 1]).write_text('fresh fixture')
'''

    def setUp(self):
        import json, os, sys
        temporary = tempfile.TemporaryDirectory(prefix='tnlean-early-diagnostics-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.repo = self.root / 'repo'
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        self.changed = 'TNLeanTest/Changed.lean'
        self.support = 'TNLeanTest/Support/Fixture.lean'
        self.deep = 'TNLeanTest/Support/Deep.lean'
        self.axioms = 'TNLeanTest/Axioms.lean'
        self.other = 'TNLeanTest/Unchanged.lean'
        files = {
            'TNLean/Core.lean': 'import Mathlib\ndef answer := 42\n',
            self.changed: 'import\n  TNLeanTest.Support.Fixture\n',
            self.support: 'import TNLeanTest.Support.Deep\n',
            self.deep: 'import TNLean.Core\n',
            self.axioms: 'import TNLean.Core\nimport Lean.Util.CollectAxioms\n',
            self.other: 'import TNLean.Core\n',
        }
        for path, content in files.items():
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content)
        git(self.repo, 'init', '-q')
        git(self.repo, 'add', '.')
        git(self.repo, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'base')
        self.base = git(self.repo, 'rev-parse', 'HEAD')
        for path in ['TNLean/Core.lean', self.changed, self.axioms]:
            with (self.repo / path).open('a') as out:
                out.write('-- changed\n')
        (self.repo / 'lake-manifest.json').write_text('{}\n')
        git(self.repo, 'add', '.')
        git(self.repo, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'change')
        for name, body in [('lake', self.LAKE), ('lean', self.LEAN)]:
            executable = self.bin / name
            executable.write_text(f'#!{sys.executable}\n' + body)
            executable.chmod(0o755)
        self.tmp = self.root / "overlay outputs ' $quoted"
        self.tmp.mkdir()
        self.calls = self.root / 'calls.jsonl'
        self.config_file = self.root / 'config.json'
        self.log = self.root / 'build.log'
        self.packages = self.root / 'production build'
        self.stale = self.packages / 'TNLeanTest/Support/Fixture.olean'
        self.stale.parent.mkdir(parents=True)
        self.stale.write_text('stale fixture')
        self.config = {'imports': {
            self.changed: ['Init', 'TNLeanTest.Support.Fixture'],
            self.support: ['Init', 'TNLeanTest.Support.Deep'],
            self.deep: ['Init', 'TNLean.Core'],
            self.axioms: ['Init', 'TNLean.Core', 'Lean.Util.CollectAxioms'],
            self.other: ['Init', 'TNLean.Core'],
        }}
        self.env = {**os.environ, 'PATH': str(self.bin) + ':' + os.environ['PATH'],
                    'TEST_CALLS': str(self.calls), 'TEST_CONFIG': str(self.config_file),
                    'TEST_PACKAGE_PATH': str(self.packages), 'TMPDIR': str(self.tmp),
                    'LEAN_PATH': str(self.root / 'ambient path'), 'BASE_SHA': self.base,
                    'PYTHONDONTWRITEBYTECODE': '1'}

    def run_cli(self, command='early', budget=20, timeout=3, base=None):
        import json, sys
        self.config_file.write_text(json.dumps(self.config))
        self.calls.unlink(missing_ok=True)
        result = subprocess.run(
            [sys.executable, str(Path(ci.__file__).resolve()), command,
             '--root', str(self.repo), '--base', self.base if base is None else base,
             '--budget', str(budget), '--timeout', str(timeout), '--log', str(self.log)],
            env=self.env, capture_output=True, text=True, timeout=30)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()] if self.calls.exists() else []
        self.assertEqual(list(self.tmp.iterdir()), [])
        self.assertEqual(self.stale.read_text(), 'stale fixture')
        return result, calls

    def lean_paths(self, calls):
        return [call['args'][-1] for call in calls if call['kind'] == 'lean']

    def test_changed_roots_exact_nested_support_and_axioms_only(self):
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        paths = self.lean_paths(calls)
        self.assertEqual(set(paths), {self.changed, self.support, self.deep, self.axioms})
        self.assertLess(paths.index(self.deep), paths.index(self.support))
        self.assertLess(paths.index(self.support), paths.index(self.changed))
        self.assertEqual(calls[0]['args'], ['--fail-fast', 'build', 'TNLean.Core'])
        for path in paths:
            prepare = next(i for i, c in enumerate(calls)
                           if c['args'] == ['--fail-fast', 'setup-file', path])
            elaborate = next(i for i, c in enumerate(calls)
                             if c['kind'] == 'lean' and c['args'][-1] == path)
            self.assertLess(prepare, elaborate)
        self.assertIn('4/4 completed', result.stdout)
        self.assertIn('mandatory strict checks still follow', result.stdout)

    def test_exact_flags_overlay_and_log_separation(self):
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for call in calls:
            if call['kind'] != 'lean':
                continue
            self.assertEqual(call['args'][:1 + len(ci.LEAN_FLAGS)], ['-j1', *ci.LEAN_FLAGS])
            self.assertEqual(call['threads'], '1')
            overlay = call['path'].split(':')[0]
            self.assertEqual(Path(overlay).parent, self.tmp)
            self.assertTrue(call['path'].startswith(overlay + ':' + str(self.packages) + ':'))
            self.assertEqual(call['args'][-3], '-o')
            self.assertEqual(call['args'][-2], str(Path(overlay) / (call['args'][-1][:-5] + '.olean')))
        log = self.log.read_text()
        self.assertIn('Built TNLean.Core (2s)', log)
        self.assertIn('Built TNLean.Extra (51s)', log)
        self.assertNotIn('ForgedFixtureOutput', log)
        self.assertNotIn('_unknown', log)

    def test_actual_production_failure_never_starts_diagnostics(self):
        self.config['build_exit'] = 17
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 17)
        self.assertEqual(len(calls), 1)

    def test_production_budget_expiry_never_starts_diagnostics(self):
        self.config['build_delay'] = 60
        result, calls = self.run_cli(budget=1)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(len(calls), 1)
        self.assertIn('Early build stopped after 1s', result.stdout)

    def test_shared_budget_is_not_reset_for_fixture_stage(self):
        import time
        self.config['build_delay'] = 0.5
        self.config['inspect_mode'] = {self.axioms: 'timeout'}
        start = time.monotonic()
        result, calls = self.run_cli(budget=1, timeout=20)
        self.assertLess(time.monotonic() - start, 3)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [])
        self.assertIn('deferred (timeout)', result.stdout)

    def test_invalid_native_results_are_advisory_and_never_elaborated(self):
        for mode in ('invalid', 'errors', 'count', 'null', 'module', 'schema', 'exit'):
            with self.subTest(mode=mode):
                self.config['inspect_mode'] = {self.axioms: mode}
                result, calls = self.run_cli()
                self.assertEqual(result.returncode, 0)
                self.assertEqual(self.lean_paths(calls), [])
                self.assertIn('diagnostics deferred', result.stdout)
                self.assertIn(self.axioms, result.stdout)
                self.assertNotIn('4/4 completed', result.stdout)

    def test_missing_imported_fixture_source_defers(self):
        self.config['imports'][self.axioms] = ['TNLeanTest.Missing']
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [])
        self.assertIn('missing fixture source', result.stdout)

    def test_source_disappearing_after_selection_is_explicitly_deferred(self):
        self.config['inspect_mode'] = {self.axioms: 'missing'}
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [])
        self.assertIn('source disappeared', result.stdout)
        self.assertIn('diagnostics deferred', result.stdout)

    def test_cyclic_imports_defer_without_elaboration(self):
        self.config['imports'][self.deep] = ['TNLeanTest.Changed']
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [])
        self.assertIn('cyclic fixture imports', result.stdout)

    def test_setup_failure_blocks_dependent_but_keeps_independent_diagnostics(self):
        self.config['setup_mode'] = {self.deep: 'exit'}
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [self.axioms])
        self.assertIn('missing production import', result.stdout)
        self.assertIn('preparation exit 12', result.stdout)
        self.assertIn('1/4 completed', result.stdout)

    def test_invalid_setup_json_defers_without_acceptance(self):
        self.config['setup_mode'] = {self.axioms: 'invalid'}
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [])
        self.assertIn('invalid setup-file JSON', result.stdout)

    def test_setup_timeout_is_explicit_and_later_checks_still_run(self):
        self.config['setup_mode'] = {self.deep: 'timeout'}
        result, calls = self.run_cli(timeout=1)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.lean_paths(calls), [self.axioms])
        self.assertIn('preparation timeout', result.stdout)
        self.assertIn('mandatory checks still follow', result.stdout)

    def test_fixture_failure_is_advisory_and_blocks_its_dependents(self):
        self.config['lean_mode'] = {self.deep: 'exit'}
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(set(self.lean_paths(calls)), {self.axioms, self.deep})
        self.assertIn('diagnostic failure (exit 23)', result.stdout)
        self.assertIn('1/4 completed', result.stdout)

    def test_fixture_timeout_is_explicit_and_blocks_its_dependents(self):
        self.config['lean_mode'] = {self.deep: 'timeout'}
        result, calls = self.run_cli(timeout=1)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(set(self.lean_paths(calls)), {self.axioms, self.deep})
        self.assertIn('deferred (timeout)', result.stdout)

    def test_failure_then_deadline_never_claims_all_completed(self):
        self.config['lean_mode'] = {self.axioms: 'exit', self.deep: 'timeout'}
        result, calls = self.run_cli(budget=2, timeout=20)
        self.assertEqual(result.returncode, 0)
        self.assertIn('diagnostic failure (exit 23)', result.stdout)
        self.assertIn('deferred (timeout)', result.stdout)
        self.assertIn('0/4 completed', result.stdout)

    def test_later_strict_still_checks_all_affected_fixtures_and_fails(self):
        self.config['lean_mode'] = {self.axioms: 'exit'}
        early, _ = self.run_cli()
        strict, calls = self.run_cli('strict')
        self.assertEqual(early.returncode, 0)
        self.assertEqual(strict.returncode, 1)
        self.assertIn(self.other, self.lean_paths(calls))
        self.assertIn('strict Lean check(s) failed', strict.stdout)

    def test_no_changed_fixture_starts_no_native_tools(self):
        head = git(self.repo, 'rev-parse', 'HEAD')
        with (self.repo / 'TNLean/Core.lean').open('a') as out:
            out.write('-- production only\n')
        git(self.repo, 'add', '.')
        git(self.repo, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'production')
        result, calls = self.run_cli(base=head)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(len(calls), 1)
        self.assertIn('No changed fixtures', result.stdout)

    def test_no_changes_or_no_base_never_start_native_tools(self):
        for base in (git(self.repo, 'rev-parse', 'HEAD'), ''):
            with self.subTest(base=base):
                result, calls = self.run_cli(base=base)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(calls, [])
                self.assertIn('No changed production modules', result.stdout)

    def test_fixture_only_change_requires_no_early_diagnostics(self):
        head = git(self.repo, 'rev-parse', 'HEAD')
        with (self.repo / self.axioms).open('a') as out:
            out.write('-- fixture only\n')
        git(self.repo, 'add', '.')
        git(self.repo, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'fixture')
        result, calls = self.run_cli(base=head)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(calls, [])

    def test_standalone_changed_regression_uses_same_support_closure(self):
        path = 'scripts/example_regression.lean'
        (self.repo / 'scripts').mkdir()
        (self.repo / path).write_text('import TNLeanTest.Support.Fixture\n')
        self.config['imports'][path] = ['TNLeanTest.Support.Fixture']
        git(self.repo, 'add', '.')
        git(self.repo, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'regression')
        result, calls = self.run_cli()
        self.assertEqual(result.returncode, 0)
        paths = self.lean_paths(calls)
        self.assertIn(path, paths)
        self.assertLess(paths.index(self.support), paths.index(path))
        self.assertNotIn(self.other, paths)


class EarlyCommandTest(unittest.TestCase):
    def test_exhausted_deadline_never_spawns_or_becomes_unlimited(self):
        import time
        with patch.object(ci.subprocess, 'Popen') as spawn:
            self.assertEqual(ci.run_early_command(['unused'], time.monotonic() - 1, 240),
                             (None, '', ''))
        spawn.assert_not_called()

    def test_missing_native_executable_is_an_advisory_error(self):
        import io
        from contextlib import redirect_stdout
        out = io.StringIO()
        with patch.object(ci, 'lean_files', return_value=['TNLeanTest/Changed.lean']), \
                patch.object(ci, 'changed_paths', return_value=['TNLeanTest/Changed.lean']), \
                patch.object(ci.subprocess, 'Popen', side_effect=FileNotFoundError('native tool missing')), \
                redirect_stdout(out):
            ci.early_fixture_diagnostics('base', None, 240, None)
        self.assertIn('diagnostics deferred: native tool missing', out.getvalue())

    def test_interrupt_stops_group_and_propagates(self):
        proc = unittest.mock.MagicMock()
        proc.communicate.side_effect = KeyboardInterrupt
        with patch.object(ci.subprocess, 'Popen', return_value=proc), \
                patch.object(ci, '_stop_group') as stop, patch.object(ci, '_signal_group'):
            with self.assertRaises(KeyboardInterrupt):
                ci.run_early_command(['fake'], None, 240)
        stop.assert_called_once_with(proc, grace=5)

    def test_zero_budget_keeps_existing_unlimited_convention(self):
        proc = unittest.mock.MagicMock()
        proc.communicate.return_value = ('', '')
        proc.returncode = 0
        with patch.object(ci.subprocess, 'Popen', return_value=proc), \
                patch.object(ci, '_signal_group'):
            self.assertEqual(ci.run_early_command(['fake'], None, 0), (0, '', ''))
        proc.communicate.assert_called_once_with(timeout=None)

    def test_timeout_terminates_group_and_preserves_partial_output(self):
        import sys, time
        code, out, err = ci.run_early_command(
            [sys.executable, '-c', 'import time; print("before timeout", flush=True); time.sleep(60)'],
            time.monotonic() + 1, 240)
        self.assertIsNone(code)
        self.assertIn('before timeout', out)

    def test_timeout_kills_term_ignoring_descendants(self):
        import os, sys, time
        with tempfile.TemporaryDirectory() as temporary:
            pid_file = Path(temporary) / 'child.pid'
            child = ('import os,signal,time; from pathlib import Path; '
                     'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                     f'Path({str(pid_file)!r}).write_text(str(os.getpid())); time.sleep(60)')
            parent = ('import subprocess,sys,time; '
                      f'subprocess.Popen([sys.executable,"-c",{child!r}]); time.sleep(60)')
            start = time.monotonic()
            code, _, _ = ci.run_early_command([sys.executable, '-c', parent], start + 1, 240)
            self.assertIsNone(code)
            self.assertLess(time.monotonic() - start, 8)
            pid = int(pid_file.read_text())
            # SIGKILL delivery is asynchronous; wait for this child to exit.
            deadline = time.monotonic() + 2
            while True:
                try:
                    state = Path(f'/proc/{pid}/stat').read_text().split(') ')[1][0]
                except (FileNotFoundError, ProcessLookupError):
                    state = 'gone'
                if state in ('Z', 'gone') or time.monotonic() >= deadline:
                    break
                time.sleep(0.01)
            self.assertIn(state, ('Z', 'gone'))

    def test_success_callback_only_after_real_success_and_keeps_deadline(self):
        import time
        proc = unittest.mock.MagicMock()
        proc.stdout = iter([])
        proc.pid = 12345
        proc.wait.return_value = 0
        seen = []
        with patch.object(ci.subprocess, 'Popen', return_value=proc), \
                patch.object(ci, '_signal_group'), patch.object(ci.time, 'monotonic', return_value=100):
            self.assertEqual(ci.early_build(['TNLean.Core'], None, 1200, seen.append), 0)
        self.assertEqual(seen, [1300])
        self.assertEqual(proc.wait.call_args.kwargs['timeout'], 1200)


if __name__ == "__main__":
    unittest.main()
