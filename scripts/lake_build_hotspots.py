#!/usr/bin/env python3
"""Rank timed Lake build jobs from a build log."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
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
TIMING_LIMIT_EXIT = 50


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


def lean_modules(path: str) -> set[str]:
    """Return possible Lake module names for a Lean source path."""
    normalized = path.strip().replace("\\", "/")
    if not normalized.endswith(".lean"):
        return set()
    modules = {normalized.removesuffix(".lean").replace("/", ".")}
    if normalized.startswith("scripts/"):
        modules.add(Path(normalized).stem)
    return modules


def changed_jobs(jobs: Sequence[TimedJob], paths: Sequence[str]) -> list[TimedJob]:
    """Keep jobs corresponding to changed Lean source files."""
    modules = {module for path in paths for module in lean_modules(path)}
    return [job for job in jobs if job.job.partition(":")[0] in modules]


def render_tsv(jobs: Sequence[TimedJob], threshold: float, limit: int | None) -> str:
    """Render jobs at or above threshold as a deterministic TSV report."""
    selected = [job for job in jobs if job.seconds >= threshold]
    if limit is not None:
        selected = selected[:limit]
    lines = ["seconds\tjob"]
    lines.extend(f"{job.seconds:.3f}\t{job.job}" for job in selected)
    return "\n".join(lines) + "\n"


def render_github_annotations(
    jobs: Sequence[TimedJob],
    paths: Sequence[str],
    warn_threshold: float,
    error_threshold: float,
) -> str:
    """Render GitHub annotations for slow changed Lean modules."""
    module_paths = {
        module: path.strip()
        for path in paths
        for module in lean_modules(path)
    }
    lines = []
    for job in jobs:
        if job.seconds < warn_threshold:
            continue
        path = module_paths.get(job.job.partition(":")[0])
        if path is None:
            continue
        level = "error" if job.seconds >= error_threshold else "warning"
        lines.append(
            f"::{level} file={path}::"
            f"{job.job} compiled in {job.seconds:.3f}s "
            f"(warning at {warn_threshold:g}s, error at {error_threshold:g}s)"
        )
    return "\n".join(lines) + ("\n" if lines else "")


def pr_changed_paths(base: str, head: str) -> list[str]:
    """Select feature edits from immutable event commits, not the build checkout.

    Fetch missing objects by SHA only. Verify the checkout contains the feature
    head, but never switch it: timings still belong to the integration build.
    """
    def git(*args: str) -> str:
        return subprocess.check_output(["git", *args], text=True).strip()

    for sha in (base, head):
        if not re.fullmatch(r"[0-9a-f]{40}", sha) or sha == "0" * 40:
            raise ValueError("PR timing endpoints must be nonzero full commit SHAs")
    for sha in (base, head):
        if subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
            subprocess.run(["git", "fetch", "--no-tags", "origin", sha], check=True)
        if git("rev-parse", "--verify", f"{sha}^{{commit}}") != sha:
            raise ValueError("PR timing endpoint is not a commit")
    subprocess.run(["git", "merge-base", "--is-ancestor", head, "HEAD"], check=True)
    forks = git("merge-base", "--all", base, head).splitlines()
    if len(forks) != 1:
        raise ValueError("PR timing endpoints must have a unique merge base")
    fork = forks[0]
    paths = subprocess.check_output(
        ["git", "-c", "core.quotePath=false", "diff", "--name-only", "--no-renames",
         "--diff-filter=AM", "-z", fork, head, "--", "*.lean"], text=True).split("\0")
    paths = [p for p in paths if p]
    if any("\n" in p or "\r" in p for p in paths):
        raise ValueError("newline in Lean source path cannot be represented in timing list")
    return paths


def select_pr_main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description="Select immutable PR timing paths")
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    args = parser.parse_args(argv)
    try:
        paths = pr_changed_paths(args.base, args.head)
    except (ValueError, subprocess.CalledProcessError) as exc:
        print(f"PR timing selection failed: {exc}", file=sys.stderr)
        return 1
    print("".join(p + "\n" for p in paths), end="")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="Lake build log")
    parser.add_argument(
        "--warn-threshold",
        type=float,
        default=25.0,
        help="minimum elapsed seconds to warn and report (default: 25)",
    )
    parser.add_argument(
        "--error-threshold",
        type=float,
        default=50.0,
        help="minimum elapsed seconds to fail (default: 50)",
    )
    parser.add_argument("--limit", type=int, help="maximum number of jobs to report")
    parser.add_argument(
        "--changed-files-from",
        type=Path,
        help="only check Lean source paths listed in this newline-delimited file",
    )
    args = parser.parse_args(argv)
    if args.warn_threshold < 0:
        parser.error("--warn-threshold must be nonnegative")
    if args.error_threshold < args.warn_threshold:
        parser.error("--error-threshold must be at least --warn-threshold")
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be positive")
    jobs = parse_timed_jobs(args.log.read_text(encoding="utf-8", errors="replace"))
    paths = None
    if args.changed_files_from is not None:
        paths = args.changed_files_from.read_text(encoding="utf-8").splitlines()
        jobs = changed_jobs(jobs, paths)
    print(render_tsv(jobs, args.warn_threshold, args.limit), end="")
    if paths is not None:
        print(
            render_github_annotations(
                jobs,
                paths,
                args.warn_threshold,
                args.error_threshold,
            ),
            end="",
        )
    if any(job.seconds >= args.error_threshold for job in jobs):
        return TIMING_LIMIT_EXIT
    return 0


if __name__ == "__main__":
    raise SystemExit(select_pr_main(sys.argv[2:]) if sys.argv[1:2] == ["select-pr"] else main())
