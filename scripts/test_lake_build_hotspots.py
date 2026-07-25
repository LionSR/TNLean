#!/usr/bin/env python3
"""Unit tests for the Lake build hotspot parser."""

from __future__ import annotations

import unittest

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


if __name__ == "__main__":
    unittest.main()
