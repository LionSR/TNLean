#!/usr/bin/env python3
"""Select tested PR changes and rank timed Lake build jobs."""

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


def pr_changed_paths(head: str) -> list[str]:
    """Compare a verified synthetic merge with its actual tested base parent.

    Mirror ci_lean_checks.selection_base's two-parent contract, but fail closed
    instead of falling back to all files. The event base is deliberately unused.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", head) or head == "0" * 40:
        raise ValueError("PR head must be a nonzero full commit SHA")
    if subprocess.run(["git", "cat-file", "-e", f"{head}^{{commit}}"],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
        subprocess.run(["git", "fetch", "--no-tags", "origin", head], check=True)
    if subprocess.check_output(["git", "rev-parse", "--verify", f"{head}^{{commit}}"],
                               text=True).strip() != head:
        raise ValueError("PR head is not a commit")
    commits = subprocess.check_output(
        ["git", "rev-list", "--parents", "-n", "1", "HEAD"], text=True).split()
    if len(commits) != 3 or commits[2] != head:
        raise ValueError("cannot verify two-parent PR merge with event head as second parent")
    fork = commits[1]
    subprocess.run(["git", "cat-file", "-e", f"{fork}^{{commit}}"], check=True)
    paths = subprocess.check_output(
        ["git", "-c", "core.quotePath=false", "diff", "--name-only", "--no-renames",
         "--diff-filter=AM", "-z", fork, "HEAD", "--", "*.lean"], text=True).split("\0")
    paths = [p for p in paths if p]
    if any("\n" in p or "\r" in p for p in paths):
        raise ValueError("newline in Lean source path cannot be represented in timing list")
    return paths


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    select = commands.add_parser("select-pr", help="select changed paths from a verified PR merge")
    select.add_argument("--head", required=True, help="immutable event PR head SHA")
    report = commands.add_parser("report", help="rank a Lake build log (default for legacy invocations)")
    report.add_argument("log", type=Path, help="Lake build log")
    report.add_argument(
        "--warn-threshold",
        type=float,
        default=25.0,
        help="minimum elapsed seconds to warn and report (default: 25)",
    )
    report.add_argument(
        "--error-threshold",
        type=float,
        default=50.0,
        help="minimum elapsed seconds to fail (default: 50)",
    )
    report.add_argument("--limit", type=int, help="maximum number of jobs to report")
    report.add_argument(
        "--changed-files-from",
        type=Path,
        help="only check Lean source paths listed in this newline-delimited file",
    )
    argv = list(sys.argv[1:] if argv is None else argv)
    # Preserve the original LOG [options] interface; argparse owns both commands.
    if argv and argv[0] not in ("select-pr", "report", "-h", "--help"):
        argv.insert(0, "report")
    args = parser.parse_args(argv)
    if args.command == "select-pr":
        try:
            paths = pr_changed_paths(args.head)
        except (ValueError, subprocess.CalledProcessError) as exc:
            print(f"PR timing selection failed: {exc}", file=sys.stderr)
            return 1
        print("".join(p + "\n" for p in paths), end="")
        return 0
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
    raise SystemExit(main())
