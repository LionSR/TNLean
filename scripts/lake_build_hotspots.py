#!/usr/bin/env python3
"""Rank timed Lake build jobs from a build log."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

ANSI_ESCAPE_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
TIMED_JOB_RE = re.compile(
    r"^\s*(?:[✔⚠✖]\s+)?(?:\[\d+/\d+\]\s+)?(?:Built|Replayed)\s+"
    r"(?P<job>.+?)\s+\((?P<duration>\d+(?:\.\d+)?)"
    r"(?P<unit>ms|s|m|h)\)\s*$"
)
SECONDS_PER_UNIT = {"ms": 0.001, "s": 1.0, "m": 60.0, "h": 3600.0}


@dataclass(frozen=True)
class TimedJob:
    """One timed Lake job."""

    job: str
    seconds: float


def parse_timed_jobs(log_text: str) -> list[TimedJob]:
    """Extract timed build jobs, sorted from slowest to fastest."""
    jobs: list[TimedJob] = []
    for raw_line in log_text.splitlines():
        line = ANSI_ESCAPE_RE.sub("", raw_line)
        if match := TIMED_JOB_RE.match(line):
            seconds = float(match.group("duration")) * SECONDS_PER_UNIT[match.group("unit")]
            jobs.append(TimedJob(job=match.group("job"), seconds=seconds))
    return sorted(jobs, key=lambda job: (-job.seconds, job.job))


def render_tsv(jobs: Sequence[TimedJob], threshold: float, limit: int | None) -> str:
    """Render jobs at or above threshold as a deterministic TSV report."""
    selected = [job for job in jobs if job.seconds >= threshold]
    if limit is not None:
        selected = selected[:limit]
    lines = ["seconds\tjob"]
    lines.extend(f"{job.seconds:.3f}\t{job.job}" for job in selected)
    return "\n".join(lines) + "\n"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="Lake build log")
    parser.add_argument(
        "--threshold",
        type=float,
        default=50.0,
        help="minimum elapsed seconds to report (default: 50)",
    )
    parser.add_argument("--limit", type=int, help="maximum number of jobs to report")
    parser.add_argument(
        "--fail-over-threshold",
        action="store_true",
        help="exit unsuccessfully when any job reaches the threshold",
    )
    args = parser.parse_args(argv)
    if args.threshold < 0:
        parser.error("--threshold must be nonnegative")
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be positive")
    jobs = parse_timed_jobs(args.log.read_text(encoding="utf-8", errors="replace"))
    print(render_tsv(jobs, args.threshold, args.limit), end="")
    return int(args.fail_over_threshold and any(job.seconds >= args.threshold for job in jobs))


if __name__ == "__main__":
    raise SystemExit(main())
