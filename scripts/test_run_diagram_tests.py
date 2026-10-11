#!/usr/bin/env python3
"""Tests for scripts/run_diagram_tests.py; runs stand-in tests, never TeX."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

RUNNER = Path(__file__).with_name("run_diagram_tests.py")
PASS = "import sys\nsys.exit(0)\n"
FAIL = "import sys\nsys.exit(3)\n"
WRITES = '''import argparse
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument("--output-dir", type=Path)
args = parser.parse_args()
args.output_dir.mkdir(parents=True)
(args.output_dir / "tenkz-a.svg").write_text("svg")
'''


class RunnerTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        # Nest the repository so a relative --output-dir stays inside tmp.
        self.root = Path(tmp.name) / "repo"
        self.scripts = self.root / "scripts"
        self.scripts.mkdir(parents=True)

    def write(self, name: str, source: str) -> None:
        (self.scripts / name).write_text(source)

    def run_runner(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run([sys.executable, str(RUNNER), "--root", str(self.root), *args],
                              capture_output=True, text=True, timeout=60)

    def test_discovery_patterns_and_exclusions(self) -> None:
        for name in ["test_tenkz_a.py", "test_b_diagram.py", "check_c_blueprint.py",
                     "test_tenkz_equation_web.py", "test_tenkz_inline_web.py",
                     "test_other.py", "check_other.py"]:
            self.write(name, PASS)
        listed = self.run_runner("--list").stdout.split("\n")
        names = sorted(Path(line.split()[1]).name for line in listed if line)
        self.assertEqual(names, ["check_c_blueprint.py", "test_b_diagram.py", "test_tenkz_a.py"])

    def test_output_dir_only_for_tests_that_declare_it(self) -> None:
        self.write("test_tenkz_plain.py", PASS)
        self.write("test_tenkz_render.py", WRITES)
        out = self.root / "out"
        result = self.run_runner("--output-dir", str(out))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((out / "test_tenkz_render" / "tenkz-a.svg").is_file())
        self.assertFalse((out / "test_tenkz_plain").exists())

    def test_hung_test_times_out_and_is_reported(self) -> None:
        self.write("test_tenkz_hang.py", "import time\ntime.sleep(30)\n")
        self.write("test_tenkz_ok.py", PASS)
        result = self.run_runner("--timeout", "1")
        self.assertEqual(result.returncode, 1)
        self.assertIn("timed out after 1s", result.stdout)

    def test_relative_root_and_single_quoted_option(self) -> None:
        self.write("test_tenkz_render.py", WRITES.replace('"--output-dir"', "'--output-dir'"))
        result = subprocess.run([sys.executable, str(RUNNER), "--root", self.root.name,
                                 "--output-dir", "out"], cwd=self.root.parent,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.root.parent / "out/test_tenkz_render/tenkz-a.svg").is_file())

    def test_every_test_runs_and_failures_are_reported(self) -> None:
        self.write("test_tenkz_a.py", FAIL)
        self.write("test_tenkz_b.py", PASS)
        self.write("test_c_diagram.py", FAIL)
        result = self.run_runner()
        self.assertEqual(result.returncode, 1)
        self.assertIn("2 of 3 diagram test(s) failed", result.stdout)
        self.assertIn("::error file=", result.stdout)
        self.assertIn("test_tenkz_b.py", result.stdout)


if __name__ == "__main__":
    unittest.main()
