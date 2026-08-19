#!/usr/bin/env python3
"""Unit tests for the channel/tensor-network import-direction guard."""

from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import check_import_direction as guard


class ImportDirectionGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, content: str) -> Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def write_manifest(self, content: str) -> Path:
        return self.write(str(guard.MANIFEST_PATH), content)

    def capture_check_all(self) -> tuple[int, str]:
        # Isolate tests from the real repository's seeded NAMESPACE_ALLOWLIST
        # offender, which does not exist in these synthetic temp trees.
        output = io.StringIO()
        with mock.patch.object(guard, "NAMESPACE_ALLOWLIST", frozenset()), \
                contextlib.redirect_stdout(output):
            status = guard.check_all(self.root)
        return status, output.getvalue()

    # -- Clean pass ---------------------------------------------------------

    def test_clean_tree_passes(self) -> None:
        self.write_manifest("# empty manifest\n")
        self.write(
            "TNLean/Channel/Basic.lean",
            "import TNLean.Algebra.Matrix\nimport TNLean.Channel.Choi\n\ndef foo := 1\n",
        )
        status, output = self.capture_check_all()
        self.assertEqual(status, 0)
        self.assertIn("0 import-direction violation(s)", output)
        self.assertIn("0 namespace-ratchet violation(s)", output)

    def test_absent_qic_directories_are_tolerated(self) -> None:
        # TNLean/Kraus does not exist yet; TNLean/Channel and TNLean/Entropy
        # are absent too in this synthetic tree. The checker must not crash.
        self.write_manifest("# empty manifest\n")
        status, output = self.capture_check_all()
        self.assertEqual(status, 0)
        self.assertIn("Checked 0 QIC-bound Lean file(s)", output)

    # -- Forbidden import -----------------------------------------------------

    def test_forbidden_import_reported(self) -> None:
        self.write_manifest("")
        self.write(
            "TNLean/Channel/Foo.lean",
            "import TNLean.Channel.Basic\nimport TNLean.MPS.Core.TPGauge\n",
        )
        errors, checked = guard.check_import_direction(self.root)
        self.assertEqual(checked, 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("TNLean/Channel/Foo.lean:2", errors[0])
        self.assertIn("TNLean.MPS.Core.TPGauge", errors[0])
        self.assertIn("LionSR/TNLean#6560", errors[0])

    def test_every_forbidden_prefix_is_rejected(self) -> None:
        self.write_manifest("")
        forbidden_modules = (
            "TNLean.MPS.Core.TPGauge",
            "TNLean.QPF.Uniqueness",
            "TNLean.Wielandt.Basic",
            "TNLean.Spectral.Radius",
            "TNLean.PEPS.Basic",
            "TNLean.QCA.Basic",
            "TNLean.PiAlgebra.Basic",
        )
        content = "\n".join(f"import {module}" for module in forbidden_modules) + "\n"
        self.write("TNLean/Channel/Foo.lean", content)
        errors, _ = guard.check_import_direction(self.root)
        self.assertEqual(len(errors), len(forbidden_modules))
        for module in forbidden_modules:
            self.assertTrue(any(module in error for error in errors), module)

    def test_allowed_channel_side_imports_are_not_flagged(self) -> None:
        self.write_manifest("")
        self.write(
            "TNLean/Channel/Foo.lean",
            "import TNLean.Channel.Choi\nimport TNLean.Entropy.Basic\n"
            "import TNLean.Algebra.Matrix\n",
        )
        errors, _ = guard.check_import_direction(self.root)
        self.assertEqual(errors, [])

    # -- Comment masking ------------------------------------------------------

    def test_comment_masked_import_ignored(self) -> None:
        self.write_manifest("")
        self.write(
            "TNLean/Channel/Foo.lean",
            "-- import TNLean.MPS.Core.TPGauge\n"
            "/- import TNLean.QPF.Uniqueness -/\n"
            "import TNLean.Channel.Basic\n",
        )
        errors, checked = guard.check_import_direction(self.root)
        self.assertEqual(checked, 1)
        self.assertEqual(errors, [])

    # -- Manifest entries -------------------------------------------------------

    def test_manifest_listed_file_violation(self) -> None:
        self.write(
            "TNLean/Algebra/QicFoundation.lean",
            "import TNLean.MPS.Core.TPGauge\n",
        )
        self.write_manifest("TNLean/Algebra/QicFoundation.lean\n")
        errors, checked = guard.check_import_direction(self.root)
        self.assertEqual(checked, 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("TNLean/Algebra/QicFoundation.lean:1", errors[0])
        self.assertIn("TNLean.MPS.Core.TPGauge", errors[0])

    def test_manifest_comments_and_blank_lines_are_skipped(self) -> None:
        self.write("TNLean/Algebra/QicFoundation.lean", "def foo := 1\n")
        self.write_manifest(
            "# a header comment\n\nTNLean/Algebra/QicFoundation.lean\n\n"
        )
        entries, errors = guard.manifest_entries(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(len(entries), 1)
        self.assertEqual(entries[0][1], Path("TNLean/Algebra/QicFoundation.lean"))

    def test_stale_manifest_entry(self) -> None:
        self.write_manifest("TNLean/Algebra/DoesNotExist.lean\n")
        errors, _ = guard.check_import_direction(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("stale manifest entry", errors[0])
        self.assertIn("TNLean/Algebra/DoesNotExist.lean", errors[0])

    def test_missing_manifest_file_is_an_error(self) -> None:
        # No manifest written at all.
        errors, _ = guard.check_import_direction(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("manifest file is missing", errors[0])

    # -- Namespace ratchet ------------------------------------------------------

    def test_new_namespace_declaration_outside_allowlist_is_rejected(self) -> None:
        self.write(
            "TNLean/Channel/Foo.lean",
            "namespace MPSTensor\n\ndef bar := 1\n\nend MPSTensor\n",
        )
        errors = guard.check_namespace_ratchet(self.root, allowlist=frozenset())
        self.assertEqual(len(errors), 1)
        self.assertIn("TNLean/Channel/Foo.lean", errors[0])
        self.assertIn("new `namespace MPSTensor`", errors[0])

    def test_allowlisted_namespace_declaration_is_accepted(self) -> None:
        self.write(
            "TNLean/Channel/Foo.lean",
            "namespace MPSTensor\n\ndef bar := 1\n\nend MPSTensor\n",
        )
        errors = guard.check_namespace_ratchet(
            self.root, allowlist=frozenset({"TNLean/Channel/Foo.lean"})
        )
        self.assertEqual(errors, [])

    def test_commented_out_namespace_declaration_is_ignored(self) -> None:
        self.write(
            "TNLean/Channel/Foo.lean",
            "-- namespace MPSTensor\ndef bar := 1\n",
        )
        errors = guard.check_namespace_ratchet(self.root, allowlist=frozenset())
        self.assertEqual(errors, [])

    def test_stale_namespace_allowlist_entry_is_rejected(self) -> None:
        self.write("TNLean/Channel/Foo.lean", "def bar := 1\n")
        errors = guard.check_namespace_ratchet(
            self.root, allowlist=frozenset({"TNLean/Channel/Foo.lean"})
        )
        self.assertEqual(len(errors), 1)
        self.assertIn("stale NAMESPACE_ALLOWLIST entry", errors[0])

    def test_ratchet_rejects_allowlist_growth_against_base(self) -> None:
        self.write(
            "TNLean/Channel/Foo.lean",
            "namespace MPSTensor\nend MPSTensor\n",
        )
        self.write(
            "TNLean/Channel/Bar.lean",
            "namespace MPSTensor\nend MPSTensor\n",
        )
        current = frozenset({"TNLean/Channel/Foo.lean", "TNLean/Channel/Bar.lean"})
        base = frozenset({"TNLean/Channel/Foo.lean"})
        errors = guard.check_namespace_ratchet(self.root, allowlist=current, base_allowlist=base)
        self.assertTrue(
            any("TNLean/Channel/Bar.lean: added to NAMESPACE_ALLOWLIST" in error
                for error in errors)
        )

    def test_ratchet_accepts_shrinking_allowlist_against_base(self) -> None:
        self.write(
            "TNLean/Channel/Foo.lean",
            "namespace MPSTensor\nend MPSTensor\n",
        )
        current = frozenset({"TNLean/Channel/Foo.lean"})
        base = frozenset({"TNLean/Channel/Foo.lean", "TNLean/Channel/Removed.lean"})
        errors = guard.check_namespace_ratchet(self.root, allowlist=current, base_allowlist=base)
        self.assertEqual(errors, [])


class MergeBaseAllowlistTests(unittest.TestCase):
    """End-to-end tests for the git-merge-base ratchet, mirroring
    check_numbered_lean_files.py's `_debt_allowlist_at_merge_base` tests."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _commit(self, message: str) -> None:
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", message,
            ],
            check=True,
        )

    def _write_checker(self, allowlist_repr: str) -> None:
        checker = self.root / "scripts" / "check_import_direction.py"
        checker.parent.mkdir(parents=True, exist_ok=True)
        checker.write_text(
            f"NAMESPACE_ALLOWLIST: frozenset[str] = frozenset({allowlist_repr})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", "scripts/check_import_direction.py"],
            check=True,
        )

    def test_missing_checker_at_base_initializes_baseline(self) -> None:
        (self.root / "README.md").write_text("placeholder\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(self.root), "add", "README.md"], check=True)
        self._commit("initial commit without the checker")
        base_ref = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True, stdout=subprocess.PIPE, text=True,
        ).stdout.strip()

        self._write_checker("{'TNLean/Channel/Foo.lean'}")
        self._commit("introduce the checker")

        baseline = guard._namespace_allowlist_at_merge_base(self.root, base_ref)
        self.assertIsNone(baseline)

    def test_growth_against_recorded_baseline_is_rejected(self) -> None:
        self._write_checker("{'TNLean/Channel/Foo.lean'}")
        self._commit("baseline")
        base_ref = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True, stdout=subprocess.PIPE, text=True,
        ).stdout.strip()

        self._write_checker("{'TNLean/Channel/Foo.lean', 'TNLean/Channel/Bar.lean'}")
        self._commit("proposed growth")

        baseline = guard._namespace_allowlist_at_merge_base(self.root, base_ref)
        self.assertEqual(baseline, frozenset({"TNLean/Channel/Foo.lean"}))

        (self.root / "TNLean/Channel").mkdir(parents=True, exist_ok=True)
        (self.root / "TNLean/Channel/Foo.lean").write_text(
            "namespace MPSTensor\nend MPSTensor\n", encoding="utf-8"
        )
        (self.root / "TNLean/Channel/Bar.lean").write_text(
            "namespace MPSTensor\nend MPSTensor\n", encoding="utf-8"
        )
        errors = guard.check_namespace_ratchet(
            self.root,
            allowlist=frozenset({"TNLean/Channel/Foo.lean", "TNLean/Channel/Bar.lean"}),
            base_allowlist=baseline,
        )
        self.assertTrue(
            any("TNLean/Channel/Bar.lean: added to NAMESPACE_ALLOWLIST" in error
                for error in errors)
        )


if __name__ == "__main__":
    unittest.main()
