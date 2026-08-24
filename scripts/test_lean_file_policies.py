#!/usr/bin/env python3
"""Unit tests for Lean module naming and file-size policy checkers."""

from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path

import check_numbered_lean_files as numbered
import check_oversized_lean_files as oversized
import check_orphan_lean_modules as orphan
import check_dead_lean_declarations as dead


class CapturedCheck(unittest.TestCase):
    def capture(self, function: Callable[..., int], *args: object) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = function(*args)
        return status, output.getvalue()


class NumberedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def track(self, relative: str, source: str = "def x := 1\n") -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        subprocess.run(["git", "-C", str(self.root), "add", relative], check=True)

    def check(
        self,
        debt: frozenset[str] = frozenset(),
        exceptions: dict[str, str] | None = None,
        base_debt: frozenset[str] | None = None,
    ) -> tuple[int, str]:
        return self.capture(
            numbered.check_numbered_files,
            self.root,
            debt,
            {} if exceptions is None else exceptions,
            base_debt,
        )

    def test_new_numbered_production_file_fails_with_guidance(self) -> None:
        self.track("TNLean/Proof2.lean")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("new numbered-sequel filename", output)
        self.assertIn("Basic.lean", output)

    def test_existing_debt_is_allowed(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}))
        self.assertEqual(status, 0)
        self.assertIn("1 numbered debt", output)

    def test_new_debt_allowlist_entry_fails_against_base(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}), base_debt=frozenset())
        self.assertEqual(status, 1)
        self.assertIn("debt allowlist; this set may only shrink", output)

    def test_base_debt_ratchet_rejects_pr_and_multicommit_push_additions(self) -> None:
        old_path = "TNLean/Old2.lean"
        new_path = "TNLean/New3.lean"
        self.track(old_path)
        checker = self.root / "scripts" / "check_numbered_lean_files.py"
        checker.parent.mkdir(parents=True)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "baseline",
            ],
            check=True,
        )
        base_ref = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

        self.track(new_path)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}, {new_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "proposed addition",
            ],
            check=True,
        )

        baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        status, output = self.check(
            frozenset({old_path, new_path}),
            base_debt=baseline,
        )
        self.assertEqual(status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", output)

        self.track("TNLean/Unrelated.lean")
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "later commit in the same push",
            ],
            check=True,
        )

        parent_baseline = numbered._debt_allowlist_at_merge_base(self.root, "HEAD^")
        parent_status, _ = self.check(
            frozenset({old_path, new_path}),
            base_debt=parent_baseline,
        )
        self.assertEqual(parent_status, 0)

        push_baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        push_status, push_output = self.check(
            frozenset({old_path, new_path}),
            base_debt=push_baseline,
        )
        self.assertEqual(push_status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", push_output)

    def test_removing_debt_allowlist_entry_is_allowed(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(
            frozenset({path}),
            base_debt=frozenset({path, "TNLean/Removed3.lean"}),
        )
        self.assertEqual(status, 0)

    def test_stale_debt_entry_fails_so_allowlist_shrinks(self) -> None:
        status, output = self.check(frozenset({"TNLean/Gone2.lean"}))
        self.assertEqual(status, 1)
        self.assertIn("stale debt allowlist entry", output)

    def test_documented_semantic_exception_is_allowed(self) -> None:
        path = "TNLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(
            exceptions={path: "The numeral is part of the mathematical type name."}
        )
        self.assertEqual(status, 0)
        self.assertIn("1 semantic exceptions", output)

    def test_empty_semantic_explanation_fails(self) -> None:
        path = "TNLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(exceptions={path: "  "})
        self.assertEqual(status, 1)
        self.assertIn("has no explanation", output)

    def test_archive_and_untracked_files_are_out_of_scope(self) -> None:
        self.track("TNLean/Archive/Legacy2.lean")
        untracked = self.root / "TNLean" / "Scratch2.lean"
        untracked.write_text("def scratch := 2\n", encoding="utf-8")
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 numbered debt", output)


class OversizedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, source: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_oversized_module_fails_with_actionable_split_guidance(self) -> None:
        self.write("TNLean/Huge.lean", "def x := 1\n" * (oversized.THRESHOLD + 1))
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("concept-named modules", output)
        self.assertIn("Foo2.lean", output)

    def test_near_limit_module_warns_without_failing(self) -> None:
        self.write(
            "TNLean/NearLimit.lean",
            "def x := 1\n" * oversized.EARLY_WARNING_THRESHOLD,
        )
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 0)
        self.assertIn("approaching size limit", output)
        self.assertIn("1 file(s) are in the", output)

    def test_exact_import_only_aggregator_is_exempt(self) -> None:
        source = "/- generated\n  /- nested comment -/\n-/\n" + (
            "import TNLean.Algebra.Basic -- public import\n" * (oversized.THRESHOLD + 1)
        )
        self.write("TNLean.lean", source)
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 0)
        self.assertIn("validated 1 of 1 exact aggregator exemption", output)

    def test_import_only_file_is_not_exempt_without_exact_registration(self) -> None:
        self.write(
            "TNLean/All.lean",
            "import TNLean.Basic\n" * (oversized.THRESHOLD + 1),
        )
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("Oversized Lean file", output)

    def test_aggregator_with_declaration_is_rejected_even_below_limit(self) -> None:
        self.write("TNLean.lean", "import TNLean.Basic\ndef notAnAggregator := 1\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_aggregator_with_invalid_module_segment_is_rejected(self) -> None:
        self.write("TNLean.lean", "import TNLean.0Invalid\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_missing_aggregator_exemption_is_rejected(self) -> None:
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"Missing.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("must name an existing, scanned .lean file", output)

    def test_unterminated_comment_rejects_aggregator(self) -> None:
        self.write("TNLean.lean", "import TNLean.Basic\n/- never closed\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("unterminated block comment", output)


class LeanDebtRatchetTestBase(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, source: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def track(self, relative: str, source: str) -> None:
        self.write(relative, source)
        subprocess.run(["git", "-C", str(self.root), "add", relative], check=True)


class OrphanLeanModulePolicyTests(LeanDebtRatchetTestBase):
    def check(
        self,
        allowlist: frozenset[str] = frozenset(),
        base_allowlist: frozenset[str] | None = None,
    ) -> tuple[int, str]:
        return self.capture(
            orphan.check_orphan_modules,
            self.root,
            allowlist,
            base_allowlist,
        )

    def test_new_declaration_bearing_orphan_fails(self) -> None:
        self.track("TNLean/Lonely.lean", "def lonely : Nat := 1\n")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("no handwritten importer", output)

    def test_unignored_new_module_is_checked_before_staging(self) -> None:
        self.write("TNLean/NewLonely.lean", "def newLonely : Nat := 1\n")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("NewLonely.lean", output)

    def test_inline_attributed_declaration_still_makes_module_nonempty(self) -> None:
        self.track(
            "TNLean/Attributed.lean",
            "@[simp] theorem attributed : True := by trivial\n",
        )
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("Attributed.lean", output)

    def test_alias_only_module_is_checked(self) -> None:
        self.track(
            "TNLean/AliasOnly.lean",
            "alias lonelyAlias := Nat.succ_le_succ_iff\n",
        )
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("AliasOnly.lean", output)

    def test_handwritten_import_and_blueprint_citation_are_consumers(self) -> None:
        self.track("TNLean/Basic.lean", "def basicValue : Nat := 1\n")
        self.track(
            "TNLean/Use.lean",
            "import TNLean.Basic\n\ndef publicUse : Nat := basicValue\n",
        )
        self.track(
            "blueprint/src/chapter/test.tex",
            "\\lean{publicUse}\n",
        )
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 current orphan", output)

    def test_existing_orphan_is_allowed_but_allowlist_cannot_grow(self) -> None:
        path = "TNLean/Lonely.lean"
        self.track(path, "def lonely : Nat := 1\n")
        status, _ = self.check(frozenset({path}))
        self.assertEqual(status, 0)
        ratchet_status, output = self.check(
            frozenset({path}),
            base_allowlist=frozenset(),
        )
        self.assertEqual(ratchet_status, 1)
        self.assertIn("allowlist; this set may only shrink", output)

    def test_stale_orphan_entry_fails(self) -> None:
        status, output = self.check(frozenset({"TNLean/Gone.lean"}))
        self.assertEqual(status, 1)
        self.assertIn("stale orphan-module allowlist entry", output)


class DeadLeanDeclarationPolicyTests(LeanDebtRatchetTestBase):
    def check(
        self,
        allowlist: frozenset[str] = frozenset(),
        base_allowlist: frozenset[str] | None = None,
    ) -> tuple[int, str]:
        return self.capture(
            dead.check_dead_declarations,
            self.root,
            allowlist,
            base_allowlist,
        )

    def test_new_single_occurrence_declaration_fails(self) -> None:
        self.track("TNLean/Lonely.lean", "def lonelyValue : Nat := 1\n")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("no second textual occurrence", output)

    def test_unignored_new_declaration_is_checked_before_staging(self) -> None:
        self.write("TNLean/NewLonely.lean", "def newLonelyValue : Nat := 1\n")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("newLonelyValue", output)

    def test_inline_attributed_declaration_is_not_name_counted(self) -> None:
        self.track(
            "TNLean/InlineSimp.lean",
            "@[simp] theorem inlineSimp : True := by trivial\n",
        )
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 current single-occurrence", output)

    def test_preceding_attributed_declaration_is_not_name_counted(self) -> None:
        self.track(
            "TNLean/PrecedingSimp.lean",
            "@[simp]\ntheorem precedingSimp : True := by trivial\n",
        )
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 current single-occurrence", output)

    def test_consumer_and_blueprint_citation_prevent_false_positive(self) -> None:
        self.track(
            "TNLean/Used.lean",
            "def usedValue : Nat := 1\n\ndef publicValue : Nat := usedValue\n",
        )
        self.track("blueprint/src/chapter/test.tex", "\\lean{publicValue}\n")
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 current single-occurrence", output)

    def test_comment_that_looks_like_declaration_is_ignored(self) -> None:
        self.track(
            "TNLean/Comment.lean",
            "/- theorem proseOnly is not a declaration. -/\n",
        )
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 current single-occurrence", output)

    def test_qualified_declaration_name_is_checked(self) -> None:
        self.track(
            "TNLean/Qualified.lean",
            "theorem Nat.lonelyQualified : True := by trivial\n",
        )
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("lonelyQualified", output)

    def test_existing_candidate_is_allowed_but_allowlist_cannot_grow(self) -> None:
        key = "TNLean/Lonely.lean::lonelyValue"
        self.track("TNLean/Lonely.lean", "def lonelyValue : Nat := 1\n")
        status, _ = self.check(frozenset({key}))
        self.assertEqual(status, 0)
        ratchet_status, output = self.check(
            frozenset({key}),
            base_allowlist=frozenset(),
        )
        self.assertEqual(ratchet_status, 1)
        self.assertIn("allowlist; this set may only shrink", output)

    def test_stale_declaration_entry_fails(self) -> None:
        status, output = self.check(frozenset({"TNLean/Gone.lean::gone"}))
        self.assertEqual(status, 1)
        self.assertIn("stale dead-declaration allowlist entry", output)

    def test_empty_allowlist_literal_is_parseable(self) -> None:
        orphan_source = "ORPHAN_MODULE_ALLOWLIST: frozenset[str] = frozenset()\n"
        dead_source = "DEAD_DECLARATION_ALLOWLIST: frozenset[str] = frozenset()\n"
        self.assertEqual(orphan._allowlist_from_source(orphan_source), frozenset())
        self.assertEqual(dead._allowlist_from_source(dead_source), frozenset())


if __name__ == "__main__":
    unittest.main()
