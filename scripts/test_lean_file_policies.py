#!/usr/bin/env python3
"""Unit tests for Lean file policies and reader-facing comments."""

from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path

import check_reader_facing_prose as prose
import check_numbered_lean_files as numbered
import check_oversized_lean_files as oversized


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


class OriginalProvenanceProseTests(unittest.TestCase):
    """Synthetic comments test classification, without Git or Lean operations."""

    CLAIM = "Public claim: https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051085776"
    NOTICE = (
        "/-\n"
        "Original formalization from the cited manuscript;\n"
        "no upstream Lean proof text reused.\n"
        "Manuscript: An example mathematical paper.\n"
        "Provenance-ID: fixture-original\n"
        "Downstream declaration:\n"
        "TNLean.Example.theorem_name\n"
        "Source: Section 11, geometry:initial-stars, lines 333–370.\n"
        + CLAIM + "\n-/\n"
    )

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.relative = Path("TNLean/MPS/ParentHamiltonian/Example.lean")
        self.path = self.root / self.relative
        self.path.parent.mkdir(parents=True)

    def check(self, source: str) -> list[prose.Finding]:
        self.path.write_text(source, encoding="utf-8")
        return prose.check_all(self.root)

    def test_canonical_original_notice_allows_public_claim(self) -> None:
        self.assertEqual(self.check(self.NOTICE), [])

    def test_added_claim_uses_surrounding_notice(self) -> None:
        self.path.write_text(self.NOTICE, encoding="utf-8")
        line = self.NOTICE.splitlines().index(self.CLAIM) + 1
        self.assertEqual(prose.check_added_lines([
            prose.AddedLine(self.path, line, self.CLAIM)
        ]), [])

    def test_public_claim_outside_notice_is_rejected(self) -> None:
        for source in ("-- " + self.CLAIM + "\n", "/-\n" + self.CLAIM + "\n-/\n"):
            with self.subTest(source=source):
                self.assertEqual(len(self.check(source)), 1)

    def test_docstrings_and_module_comments_do_not_exempt_claim(self) -> None:
        for opening in ("/--", "/-!"):
            with self.subTest(opening=opening):
                source = self.NOTICE.replace("/-\n", opening + "\n", 1)
                self.assertEqual(len(self.check(source)), 1)

    def test_incomplete_and_malformed_notices_are_rejected(self) -> None:
        mutations = {
            "heading": self.NOTICE.replace("Original formalization", "Adapted formalization"),
            "independence": self.NOTICE.replace("no upstream Lean proof text reused.\n", ""),
            "identifier": self.NOTICE.replace("Provenance-ID: fixture-original\n", ""),
            "bad identifier": self.NOTICE.replace("fixture-original", "bad id"),
            "declaration": self.NOTICE.replace("Downstream declaration:\n", ""),
            "bad declaration": self.NOTICE.replace("TNLean.Example.theorem_name", "not a declaration"),
            "source": self.NOTICE.replace(
                "Source: Section 11, geometry:initial-stars, lines 333–370.\n", ""
            ),
            "unclosed": self.NOTICE.removesuffix("-/\n"),
            "nested": self.NOTICE.replace("Manuscript:", "/- nested -/\nManuscript:"),
            "mathematical preface": self.NOTICE.replace("/-\n", "/-\nA mathematical argument.\n", 1),
        }
        for label, source in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(len(self.check(source)), 1)

    def test_only_complete_public_claim_field_is_exempt(self) -> None:
        variants = (
            self.CLAIM.replace("Public claim:", "Claim:"),
            self.CLAIM.split("#issuecomment-")[0],
            self.CLAIM + " explains the proof.",
            self.CLAIM.replace("#issuecomment-", "#discussion-"),
        )
        for claim in variants:
            with self.subTest(claim=claim):
                self.assertEqual(len(self.check(self.NOTICE.replace(self.CLAIM, claim))), 1)

    def test_other_issue_reference_in_notice_stays_a_finding(self) -> None:
        for reference in ("See issue #8733 for the proof.",
                          "Source: https://github.com/LionSR/TNLean/issues/8733"):
            with self.subTest(reference=reference):
                source = self.NOTICE.replace(self.CLAIM, self.CLAIM + "\n" + reference)
                findings = self.check(source)
                self.assertEqual([finding.text for finding in findings], [reference])

    def test_math_comments_after_notice_keep_issue_check(self) -> None:
        reference = "The estimate follows from issue #8733."
        findings = self.check(self.NOTICE + "/-- " + reference + " -/\n")
        self.assertEqual(len(findings), 1)
        self.assertIn(reference, findings[0].text)

    def test_math_in_notice_keeps_code_span_check(self) -> None:
        notation = "The radius is `S_v = 2`."
        findings = self.check(self.NOTICE.replace(self.CLAIM, notation + "\n" + self.CLAIM))
        self.assertEqual([finding.text for finding in findings], [notation])
        self.assertIn("mathematical expressions", findings[0].message)

    def test_added_other_issue_reference_in_notice_is_rejected(self) -> None:
        reference = "The estimate follows from issue #8733."
        source = self.NOTICE.replace(self.CLAIM, reference + "\n" + self.CLAIM)
        self.path.write_text(source, encoding="utf-8")
        line = source.splitlines().index(reference) + 1
        findings = prose.check_added_lines([prose.AddedLine(self.path, line, reference)])
        self.assertEqual([finding.text for finding in findings], [reference])


if __name__ == "__main__":
    unittest.main()
