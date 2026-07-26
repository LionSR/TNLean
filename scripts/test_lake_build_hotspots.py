#!/usr/bin/env python3
"""Unit tests for the Lake build hotspot parser."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import lake_build_hotspots as hotspots


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
                    ]
                ),
                encoding="utf-8",
            )
            changed.write_text(
                "TNLean/Warning.lean\nTNLean/TooSlow.lean\nscripts/LintStyle.lean\nREADME.md\n",
                encoding="utf-8",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = hotspots.main([str(log), "--changed-files-from", str(changed)])
        self.assertEqual(status, 1)
        self.assertEqual(
            output.getvalue(),
            "\n".join(
                [
                    "seconds\tjob",
                    "50.000\tTNLean.TooSlow",
                    "30.000\tLintStyle",
                    "25.000\tTNLean.Warning",
                    "::error file=TNLean/TooSlow.lean::TNLean.TooSlow compiled in 50.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=scripts/LintStyle.lean::LintStyle compiled in 30.000s "
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


if __name__ == "__main__":
    unittest.main()
