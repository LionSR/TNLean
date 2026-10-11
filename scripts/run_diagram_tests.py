#!/usr/bin/env python3
"""Run every blueprint diagram test and declaration-inventory check.

`pr-ci.yml` used to carry one step per diagram test ("Check X diagrams"), and
every new diagram test added its path to three path lists as well, so
concurrent pull requests conflicted in the workflow. This runner discovers the
tests instead:

* ``scripts/test_tenkz_*.py`` and ``scripts/test_*_diagram.py``, except the
  tests in ``EXCLUDED``, which need a built web site or run in another job;
* ``scripts/check_*_blueprint.py`` declaration-inventory checks.

A test whose source declares an ``--output-dir`` option renders into
``<output-dir>/<test name>``, so CI can preserve the diagrams for review.
Every test runs, each with a time limit; the runner then reports all
failures and exits nonzero if there were any.
"""

from __future__ import annotations

import argparse
import os
import re
import signal
import subprocess
import sys
from pathlib import Path

OUTPUT_DIR_OPTION = re.compile(r"""['"]--output-dir['"]""")

PATTERNS = ("test_tenkz_*.py", "test_*_diagram.py", "check_*_blueprint.py")

# Run elsewhere with their own setup.
EXCLUDED = {
    "test_tenkz_equation_web.py",  # needs the built blueprint web site
    "test_tenkz_inline_web.py",  # runs in the inline-layout job
}


def discover(scripts: Path) -> list[Path]:
    found = {p for pattern in PATTERNS for p in scripts.glob(pattern)}
    return sorted(p for p in found if p.name not in EXCLUDED)


def command(test: Path, output_dir: Path | None) -> list[str]:
    cmd = [sys.executable, str(test)]
    if output_dir is not None and OUTPUT_DIR_OPTION.search(test.read_text(encoding="utf-8")):
        cmd += ["--output-dir", str(output_dir / test.stem)]
    return cmd


def run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    """Run one test in its own process group; on timeout kill the whole group,
    including renderer subprocesses the test started."""
    proc = subprocess.Popen(cmd, cwd=cwd, start_new_session=True)
    try:
        code = proc.wait(timeout=timeout)
        return code, f"exit {code}"
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
        return 1, f"timed out after {timeout}s"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--output-dir", type=Path,
                        help="parent directory for tests that render diagrams")
    parser.add_argument("--list", action="store_true", help="print the tests and exit")
    parser.add_argument("--timeout", type=int, default=600, help="seconds allowed per test")
    args = parser.parse_args(argv)
    args.root = args.root.resolve()
    if args.output_dir is not None:
        args.output_dir = args.output_dir.resolve()

    tests = discover(args.root / "scripts")
    if args.list:
        for test in tests:
            print(" ".join(command(test, args.output_dir)))
        return 0

    failed = []
    for test in tests:
        print(f"::group::{test.name}", flush=True)
        code, status = run(command(test, args.output_dir), args.root, args.timeout)
        print("::endgroup::", flush=True)
        if code != 0:
            print(f"::error file={test}::{test.name} failed ({status})", flush=True)
            failed.append(test.name)
    if failed:
        print(f"{len(failed)} of {len(tests)} diagram test(s) failed:", *failed, sep="\n  ")
        return 1
    print(f"All {len(tests)} diagram tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
