#!/usr/bin/env python3
"""Unit tests for the Lake build hotspot parser."""

from __future__ import annotations

import contextlib
import io
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import lake_build_hotspots as hotspots


class PRRangeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cwd = os.getcwd()
        os.chdir(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.email", "test@example.com")
        self.git("config", "user.name", "Test")
        for name in ("Modified", "Deleted", "Renamed"):
            Path(name + ".lean").write_text("-- original\n")
        self.base = self.commit()
        self.git("checkout", "-qb", "feature")
        Path("Modified.lean").write_text("-- modified\n")
        Path("Deleted.lean").unlink()
        Path("Renamed.lean").rename("NewName.lean")
        Path("Added.lean").write_text("-- added\n")
        self.head = self.commit()
        self.git("checkout", "-qb", "advanced", self.base)
        Path("Upstream.lean").write_text("-- upstream\n")
        self.advanced = self.commit()
        self.git("merge", "--no-edit", "feature")

    def tearDown(self):
        os.chdir(self.cwd)
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", *args], text=True, stderr=subprocess.DEVNULL).strip()

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-qm", "fixture")
        return self.git("rev-parse", "HEAD")

    def test_advanced_merge_selects_only_feature_edits(self):
        expected = ["Added.lean", "Modified.lean", "NewName.lean"]
        self.assertEqual(hotspots.pr_changed_paths(self.base, self.head), expected)
        self.assertEqual(hotspots.pr_changed_paths(self.advanced, self.head), expected)
        jobs = hotspots.parse_timed_jobs("Built Upstream (81s)\nBuilt Added (51s)")
        selected = hotspots.changed_jobs(jobs, expected)
        self.assertEqual([j.job for j in selected], ["Added"])
        self.assertTrue(any(j.seconds >= 50 for j in selected))

    def test_invalid_missing_and_uncontained_heads_fail(self):
        for value in ("", "HEAD", "0" * 40, "--help"):
            with self.assertRaises(ValueError):
                hotspots.pr_changed_paths(self.base, value)
        # No origin: missing immutable objects must fail, not produce an empty list.
        with self.assertRaises(subprocess.CalledProcessError):
            hotspots.pr_changed_paths(self.base, "f" * 40)
        self.git("checkout", "--detach", self.base)
        with self.assertRaises(subprocess.CalledProcessError):
            hotspots.pr_changed_paths(self.base, self.head)


class LakeBuildHotspotTests(unittest.TestCase):
    def test_parses_units_ansi_and_optional_progress_prefix(self) -> None:
        jobs = hotspots.parse_timed_jobs(
            "\n".join(
                [
                    "✔ [9622/9713] Built TNLean.Slow (831s)",
                    "\x1b[32m⚠ [2/3] Built TNLean.Fast:c.o (250ms)\x1b[0m",
                    "Replayed TNLean.Middle (1.5m)",
                    "✖ [3/3] Built TNLean.Failed (98s)",
                    "info: unrelated output",
                ]
            )
        )
        self.assertEqual(
            jobs,
            [
                hotspots.TimedJob("TNLean.Slow", 831.0),
                hotspots.TimedJob("TNLean.Failed", 98.0),
                hotspots.TimedJob("TNLean.Middle", 90.0),
                hotspots.TimedJob("TNLean.Fast:c.o", 0.25),
            ],
        )

    def test_report_is_ranked_filtered_and_limited(self) -> None:
        jobs = [
            hotspots.TimedJob("TNLean.A", 10.0),
            hotspots.TimedJob("TNLean.B", 5.0),
            hotspots.TimedJob("TNLean.C", 1.0),
        ]
        self.assertEqual(
            hotspots.render_tsv(jobs, threshold=5.0, limit=1),
            "seconds\tjob\n10.000\tTNLean.A\n",
        )

    def test_equal_timings_are_deterministic(self) -> None:
        jobs = hotspots.parse_timed_jobs(
            "[1/2] Built TNLean.Z (12s)\n[2/2] Built TNLean.A (12s)\n"
        )
        self.assertEqual([job.job for job in jobs], ["TNLean.A", "TNLean.Z"])

    def test_changed_file_gate_warns_at_twenty_five_and_fails_at_fifty(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "lake.log"
            changed = Path(directory) / "changed.txt"
            log.write_text(
                "\n".join(
                    [
                        "Built TNLean.Unchanged (80s)",
                        "Built TNLean.Warning (25s)",
                        "Built TNLean.TooSlow (50s)",
                        "Built LintStyle (30s)",
                        "Built TNLean.Σlow (26s)",
                    ]
                ),
                encoding="utf-8",
            )
            changed.write_text(
                "TNLean/Warning.lean\nTNLean/TooSlow.lean\nscripts/LintStyle.lean\n"
                "TNLean/Σlow.lean\nREADME.md\n",
                encoding="utf-8",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = hotspots.main([str(log), "--changed-files-from", str(changed)])
        self.assertEqual(status, hotspots.TIMING_LIMIT_EXIT)
        self.assertEqual(
            output.getvalue(),
            "\n".join(
                [
                    "seconds\tjob",
                    "50.000\tTNLean.TooSlow",
                    "30.000\tLintStyle",
                    "26.000\tTNLean.Σlow",
                    "25.000\tTNLean.Warning",
                    "::error file=TNLean/TooSlow.lean::TNLean.TooSlow compiled in 50.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=scripts/LintStyle.lean::LintStyle compiled in 30.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=TNLean/Σlow.lean::TNLean.Σlow compiled in 26.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=TNLean/Warning.lean::TNLean.Warning compiled in 25.000s "
                    "(warning at 25s, error at 50s)",
                    "",
                ]
            ),
        )

    def test_changed_file_gate_ignores_unmodified_slow_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "lake.log"
            changed = Path(directory) / "changed.txt"
            log.write_text("Built TNLean.Unchanged (80s)\n", encoding="utf-8")
            changed.write_text("TNLean/Changed.lean\n", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()):
                status = hotspots.main([str(log), "--changed-files-from", str(changed)])
        self.assertEqual(status, 0)

    def test_annotations_ignore_jobs_without_a_matching_path(self) -> None:
        self.assertEqual(
            hotspots.render_github_annotations(
                [hotspots.TimedJob("TNLean.Unchanged", 80.0)],
                ["TNLean/Changed.lean"],
                warn_threshold=25.0,
                error_threshold=50.0,
            ),
            "",
        )

    def test_changed_file_gate_includes_native_facets(self) -> None:
        jobs = [hotspots.TimedJob("LintStyle:c.o", 51.0)]
        paths = ["scripts/LintStyle.lean"]
        self.assertEqual(hotspots.changed_jobs(jobs, paths), jobs)
        self.assertIn(
            "::error file=scripts/LintStyle.lean::LintStyle:c.o compiled in 51.000s",
            hotspots.render_github_annotations(jobs, paths, 25.0, 50.0),
        )


if __name__ == "__main__":
    unittest.main()
