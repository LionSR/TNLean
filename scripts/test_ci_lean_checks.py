#!/usr/bin/env python3
"""Tests for the change-set selection in scripts/ci_lean_checks.py."""

from __future__ import annotations

import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock
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
    modules = staticmethod(ci.early_modules)

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        (self.root / "TNLean").mkdir()
        self.aggregator = "TNLean/Aggregator.lean"
        self.other = "TNLean/Other.lean"
        (self.root / self.aggregator).write_text("import TNLean.Other\n")

    def test_no_changed_sources(self) -> None:
        self.assertEqual(self.modules(self.root, []), [])

    def test_all_import_only_targets_are_preserved(self) -> None:
        (self.root / self.other).write_text("import Mathlib\n")
        self.assertEqual(self.modules(self.root, [self.aggregator, self.other]),
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
                    self.modules(self.root, [self.aggregator, self.other]),
                    ["TNLean.Other"])

    def test_comments_do_not_make_an_aggregator_substantive(self) -> None:
        (self.root / self.aggregator).write_text(
            "/- header /- def hidden := 1 -/ still a comment -/\n\n"
            "  import TNLean.Other -- theorem hidden : True := by trivial\n"
            "import /- nested /- comment -/ -/ Mathlib\n")
        (self.root / self.other).write_text("import Mathlib\ndef answer := 42\n")
        self.assertEqual(self.modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_invalid_utf8_even_inside_a_comment_stays_early(self) -> None:
        (self.root / self.other).write_bytes(b"import Mathlib\n-- invalid \xff\n")
        self.assertEqual(self.modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_missing_file_stays_early(self) -> None:
        self.assertEqual(self.modules(self.root, [self.aggregator, self.other]),
                         ["TNLean.Other"])

    def test_read_failure_stays_early(self) -> None:
        original_read = Path.read_text

        def read(path, *args, **kwargs):
            if path == self.root / self.other:
                raise PermissionError("unreadable source")
            return original_read(path, *args, **kwargs)

        with patch.object(Path, "read_text", read):
            self.assertEqual(
                self.modules(self.root, [self.aggregator, self.other]),
                ["TNLean.Other"])


class FocusedSourcesTest(EarlyModulesTest):
    # Reuse every uncertain-source/read-error case above against the focused
    # classifier, whose all-aggregator policy intentionally differs from early.
    @staticmethod
    def modules(root, sources):
        return [ci.module_of(p) for p in ci.focused_sources(root, sources, sources)]

    def test_all_import_only_targets_are_preserved(self):
        (self.root / self.other).write_text("import Mathlib\n")
        self.assertEqual(ci.focused_sources(self.root, [self.aggregator, self.other], [self.aggregator, self.other]), [])

    def test_read_failure_stays_early(self):
        with patch.object(Path, "read_bytes", side_effect=PermissionError("unreadable")):
            self.assertEqual(ci.focused_sources(self.root, [self.other], [self.other]), [self.other])

    def test_comment_token_splicing_is_not_an_import(self):
        for source in ("im/- comment -/port Mathlib\n",
                       "import Math/- comment -/lib\n",
                       "import Mathlib\n\"-- unterminated string\n"):
            with self.subTest(source=source):
                (self.root / self.other).write_text(source)
                self.assertEqual(ci.focused_sources(self.root, [self.other], [self.other]), [self.other])

    def test_supported_import_spellings_are_deferred(self):
        for source in ("import A.B'\nimport C_D.E2 -- note\n",
                       "/- header -/ import A\nimport /- note -/ B\n",
                       "import A/- trailing comment -/\n"):
            with self.subTest(source=source):
                (self.root / self.other).write_text(source)
                self.assertEqual(ci.focused_sources(self.root, [self.other], [self.other]), [])

    def test_uncertain_whitespace_and_doc_tokens_stay_focused(self):
        for source in ("import\u00a0A", "import A\u2028import B", "import\tA\n",
                       "import A\n/-- unattached doc -/", "import A\n/-! doc -/",
                       "import A\v", "import A\f", "import A\r", "import A\r\n"):
            with self.subTest(source=source):
                (self.root / self.other).write_text(source)
                self.assertEqual(ci.focused_sources(self.root, [self.other], [self.other]),
                                 [self.other])

    def test_no_strict_coverage_retains_import_only_source(self):
        self.assertEqual(ci.focused_sources(self.root, [self.aggregator], []), [self.aggregator])


class SelectTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        files = {
            "TNLean/Core.lean": "import Mathlib\n",
            "TNLean/Uses.lean": "import TNLean.Core\n",
            "TNLean/Other.lean": "import Mathlib\n",
            "TNLean/Archive/Old.lean": "import TNLean.Core\n",
            "scripts/core_regression.lean": "import TNLean.Uses\n",
            "scripts/other_regression.lean": "import TNLean.Other\n",
            "scripts/unrelated_regression.lean": "import Mathlib\n",
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

    def select(self, base: str | None):
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            return ci.select(Path("."), base)
        finally:
            os.chdir(cwd)

    def test_transitive_dependents_are_selected(self) -> None:
        self.change("TNLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

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
        self.assertIn("scripts/unrelated_regression.lean", old_tests)
        resolved = self.resolve_base(self.base, pr_head)
        self.assertEqual(resolved, base_parent)
        early, sources, tests = self.select(resolved)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_pr_owned_full_run_change_still_selects_every_test(self):
        _, pr_head = self.synthetic_merge(pr_changes_manifest=True)
        tests = self.select(self.resolve_base(self.base, pr_head))[2]
        self.assertIn("scripts/unrelated_regression.lean", tests)
        self.assertIn("scripts/other_regression.lean", tests)

    def test_push_merge_keeps_previous_head_base(self):
        self.synthetic_merge()
        self.assertEqual(self.resolve_base(self.base, None), self.base)
        self.assertIn("scripts/unrelated_regression.lean", self.select(self.base)[2])

    def test_wrong_pr_head_falls_back_to_all_tests(self):
        self.synthetic_merge()
        resolved = self.resolve_base(self.base, self.base)
        self.assertIsNone(resolved)
        self.assertIn("scripts/unrelated_regression.lean", self.select(resolved)[2])

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
        self.assertIn("test scripts/core_regression.lean", result.stdout)
        self.assertNotIn("scripts/unrelated_regression.lean", result.stdout)

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

    def test_mixed_leaf_and_aggregator_preserve_strict_tests(self) -> None:
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertNotIn("TNLean.Uses", early)
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_aggregator_only_keeps_early_strict_and_tests(self) -> None:
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Uses"])
        self.assertEqual(sources, ["TNLean/Uses.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

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
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_pin_change_with_mixed_sources_keeps_every_test(self) -> None:
        self.change("lake-manifest.json", "{}\n")
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean",
                                "scripts/other_regression.lean",
                                "scripts/unrelated_regression.lean"])

    def test_invalid_utf8_source_is_strict_and_early(self) -> None:
        (self.root / "TNLean/Core.lean").write_bytes(b"import Mathlib\n-- invalid \xff\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\nimport TNLean.Other\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Core"])
        self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_archive_is_not_built_early(self) -> None:
        self.change("TNLean/Archive/Old.lean", "import TNLean.Core\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources, tests), ([], [], []))

    def test_new_module_and_regression(self) -> None:
        (self.root / "TNLean/New.lean").write_text("import TNLean.Core\n")
        self.change("scripts/new_regression.lean", "import TNLean.New\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.New"])
        self.assertEqual(tests, ["scripts/new_regression.lean"])

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
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_renamed_module_marks_importers_of_the_old_name(self) -> None:
        git(self.root, "mv", "TNLean/Uses.lean", "TNLean/Renamed.lean")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "rename")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["TNLean.Renamed"])
        self.assertEqual(tests, ["scripts/core_regression.lean"])

    def test_dependency_pin_runs_every_test(self) -> None:
        self.change("lake-manifest.json", "{}\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(len(tests), 3)
        self.assertNotIn("scripts/LintStyle.lean", tests)

    def test_pin_change_keeps_changed_sources_strict(self) -> None:
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.change("TNLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), (["TNLean.Core"], ["TNLean/Core.lean"]))
        self.assertEqual(len(tests), 3)

    def test_lakefile_lean_runs_every_test(self) -> None:
        self.change("lakefile.lean", "import Lake\n")
        _, _, tests = self.select(self.base)
        self.assertEqual(len(tests), 3)

    def test_no_base_runs_every_test(self) -> None:
        _, _, tests = self.select(None)
        self.assertEqual(len(tests), 3)


class FocusedSelectTest(unittest.TestCase):
    setUp = SelectTest.setUp
    tearDown = SelectTest.tearDown
    change = SelectTest.change

    def merge_checkout(self, feature):
        git(self.root, "checkout", "--detach", self.base)
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "merge",
            "--no-ff", "-m", "synthetic merge", feature)

    def test_orphan_import_failure_retained_without_verified_merge(self):
        self.change("TNLean/Orphan.lean", "import Does.Not.Exist\n")
        head = git(self.root, "rev-parse", "HEAD")
        cwd = Path.cwd()
        try:
            with patch.object(ci, "early_build", return_value=1) as build, \
                    patch.object(ci, "run_batch", return_value=[]):
                self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                          "--base", self.base, "--head", head,
                                          "--pr-head", head]), 1)
            self.assertEqual(build.call_args.args[0], ["TNLean.Orphan"])
            self.assertIsNone(ci.selection_base(self.base, head))
            self.assertEqual(ci.select(Path("."), None)[1], [])
        finally:
            os.chdir(cwd)

    def test_type_changed_orphan_is_retained_even_in_verified_merge(self):
        self.change("TNLean/Orphan.lean", "import Mathlib\n")
        self.change("target.txt", "import Does.Not.Exist\n")
        self.base = git(self.root, "rev-parse", "HEAD")
        (self.root / "TNLean/Orphan.lean").unlink()
        (self.root / "TNLean/Orphan.lean").symlink_to("../target.txt")
        self.change("README.md", "type change\n")
        head = git(self.root, "rev-parse", "HEAD")
        self.assertIn("T\tTNLean/Orphan.lean", git(self.root, "diff", "--name-status", self.base, head))
        self.merge_checkout(head)
        cwd = Path.cwd()
        try:
            os.chdir(self.root)
            self.assertEqual(ci.selection_base(self.base, head), self.base)
            self.assertEqual(ci.select(Path("."), self.base)[1], [])
            with patch.object(ci, "early_build", return_value=1) as build, \
                    patch.object(ci, "run_batch", return_value=[]):
                self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                          "--base", self.base, "--head", head,
                                          "--pr-head", head]), 1)
            self.assertEqual(build.call_args.args[0], ["TNLean.Orphan"])
        finally:
            os.chdir(cwd)

    def test_verified_merge_defers_orphan_but_strict_reports_its_failure(self):
        orphan = "TNLean/Orphan.lean"
        self.change(orphan, "import Does.Not.Exist\n")
        head = git(self.root, "rev-parse", "HEAD")
        self.merge_checkout(head)
        cwd = Path.cwd()
        args = ["--root", str(self.root), "--base", self.base, "--pr-head", head]
        try:
            with patch.object(ci, "early_build") as build, \
                    patch.object(ci, "run_batch", return_value=[]):
                self.assertEqual(ci.main(["focused", "--head", head, *args]), 0)
            build.assert_not_called()
            with patch.object(ci, "run_batch", return_value=[orphan]) as run:
                self.assertEqual(ci.main(["strict", *args]), 1)
            self.assertEqual(run.call_args.args, ([orphan], 3, 240))
        finally:
            os.chdir(cwd)

    def focused(self, base=None, head=None):
        cwd = Path.cwd()
        try:
            os.chdir(self.root)
            return ci.select_focused(Path("."), base or self.base,
                                     head or git(self.root, "rev-parse", "HEAD"))
        finally:
            os.chdir(cwd)

    def test_direct_source_does_not_replace_full_affected_test_selector(self):
        self.change("TNLean/Core.lean", "import Mathlib\n-- feature\n")
        sources, tests, _ = self.focused()
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, [])

    def test_feature_selection_uses_actual_merged_dependency_contents(self):
        self.change("TNLean/Core.lean", "import Mathlib\n-- feature\n")
        feature = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "-qb", "updated-main", self.base)
        self.change("TNLean/MainOwner.lean", "import Mathlib\n")
        main = git(self.root, "rev-parse", "HEAD")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "merge",
            "--no-ff", "--no-commit", feature)
        # This is the actual integration tree, not the older feature version.
        (self.root / "TNLean/Core.lean").write_text("import TNLean.Other\n-- merged\n")
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "merge")
        sources, tests, graph = self.focused(main, feature)
        self.assertEqual(sources, ["TNLean/Core.lean"])
        self.assertEqual(tests, [])
        self.assertEqual(graph["TNLean.Core"], {"TNLean.Other"})

    def test_direct_regression_script_is_selected_alone(self):
        self.change("scripts/core_regression.lean", "import TNLean.Uses\n-- feature\n")
        sources, tests, graph = self.focused()
        self.assertEqual(sources, [])
        self.assertEqual(tests, ["scripts/core_regression.lean"])
        self.assertEqual(graph[ci.module_of(tests[0])], {"TNLean.Uses"})

    def test_invalid_and_uncontained_heads_fail_closed(self):
        for base, head in [("not-a-commit", self.base), (self.base, "not-a-commit")]:
            with self.subTest(base=base, head=head), self.assertRaises(subprocess.CalledProcessError):
                self.focused(base, head)
        self.change("TNLean/Core.lean", "import Mathlib\n-- feature\n")
        feature = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "--detach", self.base)
        with self.assertRaises(subprocess.CalledProcessError):
            self.focused(self.base, feature)
        with self.assertRaises(ValueError):
            ci.select_focused(self.root, None, self.base)
        with self.assertRaises(ValueError):
            ci.select_focused(self.root, self.base, None)

    def test_missing_changed_target_is_not_silently_dropped(self):
        self.change("TNLean/Core.lean", "import Mathlib\n-- feature\n")
        (self.root / "TNLean/Core.lean").unlink()
        with self.assertRaisesRegex(ValueError, "missing from the checkout"):
            self.focused()

    def test_deletion_has_no_target_and_rename_checks_destination(self):
        (self.root / "TNLean/Uses.lean").unlink()
        self.change("README.md", "delete source\n")
        self.assertEqual(self.focused()[:2], ([], []))
        git(self.root, "mv", "TNLean/Other.lean", "TNLean/Renamed.lean")
        self.change("README.md", "rename source\n")
        self.assertEqual(self.focused()[:2], (["TNLean/Renamed.lean"], []))

    def test_feature_deletion_restored_in_checkout_is_conservatively_checked(self):
        (self.root / "TNLean/Uses.lean").unlink()
        self.change("README.md", "delete source\n")
        (self.root / "TNLean/Uses.lean").write_text("import TNLean.Core\n")
        self.assertEqual(self.focused()[:2], (["TNLean/Uses.lean"], []))

    def test_pin_trigger_still_runs_all_tests_in_full_selector(self):
        self.change("lake-manifest.json", "{}\n")
        self.assertEqual(self.focused()[:2], ([], []))
        cwd = Path.cwd()
        try:
            os.chdir(self.root)
            self.assertEqual(len(ci.select(Path("."), self.base)[2]), 3)
        finally:
            os.chdir(cwd)

    def test_invalid_cli_ref_never_falls_back_to_full_selection(self):
        cwd = Path.cwd()
        try:
            with mock.patch.object(ci, "select") as full, \
                    mock.patch.object(ci, "focused_checks") as run:
                self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                          "--base", self.base, "--head", "missing-ref"]), 1)
            full.assert_not_called()
            run.assert_not_called()
        finally:
            os.chdir(cwd)

    def test_cli_deferral_preserves_post_build_coverage_and_failures(self):
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        self.change("TNLean/Uses.lean", "import TNLean.Core\n-- aggregator edit\n")
        self.change("scripts/core_regression.lean", "import TNLean.Uses\n-- test edit\n")
        head = git(self.root, "rev-parse", "HEAD")
        self.merge_checkout(head)
        cwd = Path.cwd()
        try:
            for outcome in (0, 1):
                with mock.patch.object(ci, "focused_checks", return_value=outcome) as run:
                    self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                              "--base", self.base, "--head", head]), outcome)
                self.assertEqual(run.call_args.args[:2],
                                 (["TNLean/Core.lean"], ["scripts/core_regression.lean"]))
                self.assertIn("TNLean.Uses", run.call_args.args[2])
            early, sources, tests = ci.select(Path("."), self.base)
            self.assertEqual(early, ["TNLean.Core"])
            self.assertEqual(sources, ["TNLean/Core.lean", "TNLean/Uses.lean"])
            self.assertEqual(tests, ["scripts/core_regression.lean"])
            with mock.patch.object(ci, "selection_base", return_value=self.base), \
                    mock.patch.object(ci, "run_batch", return_value=["TNLean/Uses.lean"]) as run:
                self.assertEqual(ci.main(["strict", "--root", str(self.root),
                                          "--base", self.base]), 1)
            self.assertEqual(run.call_args.args, (sources + tests, 3, 240))
        finally:
            os.chdir(cwd)

    def test_cli_import_only_and_empty_selection_do_not_prepare_root(self):
        for changed in (False, True):
            if changed:
                self.change("TNLean/Uses.lean", "import TNLean.Core\n-- edit\n")
            head = git(self.root, "rev-parse", "HEAD")
            if changed:
                self.merge_checkout(head)
            cwd = Path.cwd()
            try:
                with mock.patch.object(ci, "early_build") as build, \
                        mock.patch.object(ci, "run_batch", return_value=[]) as run:
                    self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                              "--base", self.base, "--head", head]), 0)
                build.assert_not_called()
                self.assertTrue(all(not call.args[0] for call in run.call_args_list))
                # Existing early's all-import-only fallback remains unchanged.
                self.assertEqual(ci.select(Path("."), self.base)[:2],
                                 (["TNLean.Uses"], ["TNLean/Uses.lean"]) if changed else ([], []))
            finally:
                os.chdir(cwd)

    def test_unreadable_checkout_fails_focused_before_any_build(self):
        self.change("TNLean/Core.lean", "import Mathlib\ndef answer := 42\n")
        head = git(self.root, "rev-parse", "HEAD")
        cwd = Path.cwd()
        try:
            with patch.object(Path, "read_text", side_effect=PermissionError("unreadable")), \
                    patch.object(ci, "focused_checks") as run:
                self.assertEqual(ci.main(["focused", "--root", str(self.root),
                                          "--base", self.base, "--head", head]), 1)
            run.assert_not_called()
        finally:
            os.chdir(cwd)


class FocusedRunnerTest(unittest.TestCase):
    def run_checks(self, sources, tests, graph, build_codes=None, strict_failures=None):
        build_codes = build_codes or {}
        strict_failures = strict_failures or set()

        def strict(paths, jobs, timeout):
            self.assertEqual((jobs, timeout), (3, 240))
            return [p for p in paths if p in strict_failures]

        with mock.patch.object(ci, "early_build", side_effect=lambda ms, log, budget:
                               build_codes.get(ms[0], 0)) as build, \
                mock.patch.object(ci, "run_batch", side_effect=strict) as runner:
            code = ci.focused_checks(sources, tests, graph, 3, 240, None)
        self.assertTrue(all(call.args[2] == 0 for call in build.call_args_list))
        return code, build, runner

    def test_build_failure_skips_only_failed_source_and_remains_nonzero(self):
        code, build, runner = self.run_checks(
            ["TNLean/Bad.lean", "TNLean/Good.lean"], [], {}, {"TNLean.Bad": 3})
        self.assertEqual(code, 1)
        self.assertEqual([c.args[0] for c in build.call_args_list],
                         [["TNLean.Bad", "TNLean.Good"], ["TNLean.Bad"], ["TNLean.Good"]])
        self.assertEqual(runner.call_args_list[0].args[0], ["TNLean/Good.lean"])
        self.assertFalse(any("TNLean/Bad.lean" in c.args[0] for c in runner.call_args_list))

    def test_sources_are_prepared_by_one_build_and_checked_together(self):
        sources = ["TNLean/A.lean", "TNLean/B.lean", "TNLean/C.lean"]
        code, build, runner = self.run_checks(sources, [], {})
        self.assertEqual(code, 0)
        self.assertEqual([c.args[0] for c in build.call_args_list],
                         [["TNLean.A", "TNLean.B", "TNLean.C"]])
        self.assertEqual([c.args[0] for c in runner.call_args_list], [sources, []])

    def test_prepared_sources_are_not_rebuilt_for_tests(self):
        sources = ["TNLean/Core.lean", "TNLean/Other.lean"]
        test = "scripts/core_regression.lean"
        graph = {"scripts.core_regression": {"TNLean.Core"},
                 "TNLean.Core": set(), "TNLean.Other": set()}
        code, build, runner = self.run_checks(sources, [test], graph)
        self.assertEqual(code, 0)
        self.assertEqual([c.args[0] for c in build.call_args_list],
                         [["TNLean.Core", "TNLean.Other"]])
        self.assertEqual([c.args[0] for c in runner.call_args_list], [sources, [test]])

    def test_strict_and_timeout_failures_remain_nonzero(self):
        source = "TNLean/Good.lean"
        self.assertEqual(self.run_checks([source], [], {}, strict_failures={source})[0], 1)
        self.assertEqual(self.run_checks([source], [], {}, {"TNLean.Good": 124})[0], 1)

    def test_regression_imports_are_prepared_before_strict_check(self):
        tests = ["scripts/core_regression.lean", "scripts/other_regression.lean"]
        graph = {"scripts.core_regression": {"TNLean.Core"},
                 "scripts.other_regression": {"TNLean.Core", "TNLean.Other"},
                 "TNLean.Core": set(), "TNLean.Other": set()}
        code, build, runner = self.run_checks([], tests, graph)
        self.assertEqual(code, 0)
        self.assertEqual([c.args[0] for c in build.call_args_list],
                         [["TNLean.Core"], ["TNLean.Other"]])
        self.assertEqual([c.args[0] for c in runner.call_args_list], [tests])

    def test_failed_production_dependency_blocks_test_without_stale_imports(self):
        test = "scripts/uses_regression.lean"
        graph = {"scripts.uses_regression": {"TNLean.Uses"},
                 "TNLean.Uses": {"TNLean.Core"}, "TNLean.Core": set()}
        code, _, runner = self.run_checks(["TNLean/Core.lean"], [test], graph,
                                         {"TNLean.Core": 1})
        self.assertEqual(code, 1)
        self.assertFalse(any(test in c.args[0] for c in runner.call_args_list))

    def test_test_preparation_failure_preserves_independent_diagnostics(self):
        bad, good = "scripts/bad_regression.lean", "scripts/good_regression.lean"
        graph = {"scripts.bad_regression": {"TNLean.Bad"},
                 "scripts.good_regression": {"TNLean.Good"},
                 "TNLean.Bad": set(), "TNLean.Good": set()}
        code, build, runner = self.run_checks([], [bad, good], graph, {"TNLean.Bad": 1})
        self.assertEqual(code, 1)
        self.assertEqual([c.args[0] for c in build.call_args_list],
                         [["TNLean.Bad"], ["TNLean.Good"]])
        self.assertEqual([p for c in runner.call_args_list for p in c.args[0]], [good])

    def test_missing_test_dependency_is_blocked_not_ignored(self):
        test = "scripts/uses_regression.lean"
        code, build, runner = self.run_checks([], [test],
                                             {"scripts.uses_regression": {"TNLean.Deleted"}})
        self.assertEqual(code, 1)
        build.assert_not_called()
        self.assertFalse(any(test in c.args[0] for c in runner.call_args_list))

    def test_required_root_import_is_not_silently_filtered(self):
        test = "scripts/uses_regression.lean"
        code, build, _ = self.run_checks([], [test],
                                         {"scripts.uses_regression": {"TNLean"}, "TNLean": set()})
        self.assertEqual(code, 0)
        self.assertEqual(build.call_args.args[0], ["TNLean"])


class FocusedWorkflowTest(unittest.TestCase):
    def setUp(self):
        workflow = Path(__file__).resolve().parents[1] / ".github/workflows/pr-ci.yml"
        block = workflow.read_text().split(
            "      - name: Check directly changed Lean sources and tests strictly\n", 1)[1]
        block = block.split("      # Build the changed production modules", 1)[0]
        self.assertIn("if: github.event_name == 'pull_request'", block)
        self.assertIn("BASE_SHA: ${{ github.event.pull_request.base.sha }}", block)
        self.assertIn("PR_HEAD_SHA: ${{ github.event.pull_request.head.sha }}", block)
        self.assertIn("timeout-minutes: 60", block)
        self.script = "\n".join(line[10:] for line in block.split("        run: |\n", 1)[1]
                                .splitlines() if line.strip())

    def run_script(self, git_status=0, base="a" * 40, cache=True):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            if cache:
                artifact = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
                artifact.parent.mkdir(parents=True)
                artifact.touch()
            for name, body in {
                "git": f"echo git >> '{root}/calls'\nexit {git_status}\n",
                "python3": f"echo python >> '{root}/calls'\nexit 0\n",
            }.items():
                path = root / name
                path.write_text("#!/bin/sh\n" + body)
                path.chmod(0o755)
            env = dict(os.environ, PATH=f"{root}:{os.environ['PATH']}", BASE_SHA=base,
                       PR_HEAD_SHA="b" * 40, RUNNER_TEMP=tmp)
            result = subprocess.run(["bash", "-c", self.script], env=env, cwd=root,
                                    capture_output=True)
            calls = (root / "calls").read_text() if (root / "calls").exists() else ""
            return result.returncode, calls

    def test_refs_are_required_and_fetch_failure_cannot_pass(self):
        code, calls = self.run_script(git_status=73)
        self.assertNotEqual(code, 0)
        self.assertNotIn("python", calls)
        code, calls = self.run_script(base="")
        self.assertNotEqual(code, 0)
        self.assertEqual(calls, "")

    def test_missing_prebuilt_cache_stops_before_git_or_python(self):
        code, calls = self.run_script(cache=False)
        self.assertNotEqual(code, 0)
        self.assertEqual(calls, "")

    def test_valid_refs_run_generic_mode_without_module_lists(self):
        self.assertEqual(self.run_script()[0], 0)
        self.assertIn("ci_lean_checks.py focused", self.script)
        self.assertIn('--base "$BASE_SHA" --head "$PR_HEAD_SHA"', self.script)
        self.assertNotIn("TNLean.", self.script)
        self.assertNotIn("||", self.script)

    def test_full_build_and_post_build_strict_remain_required_in_order(self):
        import yaml
        workflow = Path(__file__).resolve().parents[1] / ".github/workflows/pr-ci.yml"
        steps = yaml.safe_load(workflow.read_text())["jobs"]["build"]["steps"]
        names = [step["name"] for step in steps if "name" in step]
        ordered = ["Check directly changed Lean sources and tests strictly",
                   "Build changed Lean modules early",
                   "Build Lean project and capture timings",
                   "Check changed Lean files and affected tests strictly"]
        self.assertEqual(sorted(names.index(n) for n in ordered),
                         [names.index(n) for n in ordered])
        full, strict = [next(s for s in steps if s.get("name") == n) for n in ordered[2:]]
        for step in (full, strict):
            self.assertNotIn("if", step)
            self.assertNotIn("continue-on-error", step)
            self.assertIn("set -eo pipefail", step["run"])
        self.assertIn("lake build\n", full["run"])
        self.assertIn("ci_lean_checks.py strict --jobs 3", strict["run"])
        self.assertEqual(strict["timeout-minutes"], 60)


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
