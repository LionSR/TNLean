#!/usr/bin/env python3
"""Resource fixtures and real shell/pipeline/signal tests; no Lean build."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch

import yaml
import ci_resource_diagnostics as diagnostics

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/pr-ci.yml").read_text())
STEPS = WORKFLOW["jobs"]["build"]["steps"]
BUILD = next(s["run"] for s in STEPS if s.get("name") == "Build Lean project and capture timings")


def stat(pid, name="lean", start=100, state="R", cpu=400, rss=20):
    fields = ["0"] * 22
    fields[0], fields[11], fields[12] = state, str(cpu), "50"
    fields[19], fields[21] = str(start), str(rss)
    return f"{pid} ({name}) " + " ".join(fields)


class SamplesTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.proc = self.root / "proc"
        self.proc.mkdir()
        self.cg = self.root / "cgroup"
        self.cg.mkdir()
        self.write("meminfo", "MemTotal: 1000 kB\nMemAvailable: 350 kB\nSecret: 123 kB\n")
        self.write("stat", "cpu 1 2 3 4 5 6 7 8 9 10\n")
        self.write("uptime", "1000 0\n")
        self.write("loadavg", "1.0 2.0 3.0 1/99 123\n")
        self.write("123/stat", stat(123))
        self.write("123/cgroup", "0::/\n")
        (self.cg / "memory.current").write_text("321\n")
        (self.cg / "memory.max").write_text("max\n")
        (self.cg / "memory.events").write_text("oom 2\noom_kill 1\nsecret 9\n")
        (self.cg / "cpu.stat").write_text("usage_usec 100\nnr_throttled 3\nthrottled_usec 200\n")

    def write(self, name, value):
        path = self.proc / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def sample(self):
        return diagnostics.sample(self.proc, self.cg, self.root)

    def test_numeric_metrics_and_oom_counts(self):
        row = self.sample()
        self.assertEqual(row["memory_kib"], {"MemTotal": 1000, "MemAvailable": 350})
        self.assertEqual(row["cpu_ticks"]["iowait"], 5)
        self.assertEqual(row["loadavg"], [1.0, 2.0, 3.0])
        self.assertGreater(row["disk"]["available_bytes"], 0)
        self.assertEqual(row["cgroup_v2"]["memory_events"], {"oom": 2, "oom_kill": 1})
        self.assertEqual(row["cgroup_v2"]["memory_max_bytes"], "max")
        p = row["processes"][0]
        self.assertEqual(p["cpu_seconds"], 450 / os.sysconf("SC_CLK_TCK"))
        self.assertEqual(p["rss_bytes"], 20 * os.sysconf("SC_PAGE_SIZE"))
        self.assertEqual(p["elapsed_seconds"], 1000 - 100 / os.sysconf("SC_CLK_TCK"))

    def test_no_arguments_environment_paths_or_unknown_names(self):
        secret = "SENSITIVE_MARKER"
        self.write("124/stat", stat(124, secret))
        self.write("123/cmdline", secret)
        self.write("123/environ", secret)
        self.write("123/cgroup", "0::/" + secret)
        real_read = diagnostics.read_small
        def read(path):
            self.assertNotIn(path.name, {"cmdline", "environ"})
            return real_read(path)
        with patch.object(diagnostics, "read_small", side_effect=read):
            content = json.dumps(self.sample())
        self.assertNotIn(secret, content)
        self.assertNotIn(str(self.root), content)
        self.assertNotIn("Secret", content)

    def test_missing_and_malformed_metrics_are_unavailable_not_zero(self):
        self.write("stat", "invalid")
        self.write("meminfo", "MemTotal: not-a-number")
        self.write("uptime", "bad")
        (self.cg / "memory.current").unlink()
        with patch.object(os, "statvfs", side_effect=PermissionError("secret")):
            row = self.sample()
        for key in ("cpu_ticks", "memory_kib", "disk", "processes"):
            self.assertIsNone(row[key])
        self.assertIsNone(row["cgroup_v2"]["memory_current_bytes"])
        self.assertIsNone(diagnostics.sample(self.proc, None, self.root)["cgroup_v2"])

    def test_process_detail_cap_and_totals(self):
        for pid in range(200, 240):
            self.write(f"{pid}/stat", stat(pid, cpu=pid))
        row = self.sample()
        self.assertEqual(row["observed_build_processes"], 41)
        self.assertEqual(len(row["processes"]), diagnostics.MAX_PROCESSES)
        self.assertEqual(row["observed_build_rss_bytes"], 41 * 20 * os.sysconf("SC_PAGE_SIZE"))

    def test_parent_reuse_zombie_and_missing(self):
        self.assertTrue(diagnostics.parent_alive(self.proc, 123, 100))
        self.assertFalse(diagnostics.parent_alive(self.proc, 123, 101))
        self.write("123/stat", stat(123, state="Z"))
        self.assertFalse(diagnostics.parent_alive(self.proc, 123, 100))
        self.assertFalse(diagnostics.parent_alive(self.proc, 999, 100))

    def test_cgroup_path_not_allowed_to_escape(self):
        self.assertEqual(diagnostics.cgroup_dir(self.proc, 123, self.cg), self.cg)
        self.write("123/cgroup", "0::/../../secret\n")
        self.assertIsNone(diagnostics.cgroup_dir(self.proc, 123, self.cg))
        self.write("123/cgroup", "1:memory:/legacy\n")
        self.assertIsNone(diagnostics.cgroup_dir(self.proc, 123, self.cg))

    def test_sample_and_byte_caps(self):
        out = self.root / "samples.jsonl"
        with patch.object(time, "sleep"), contextlib.redirect_stdout(io.StringIO()):
            diagnostics.monitor(out, 123, self.proc, self.cg, self.root, interval=0, max_samples=3)
        lines = out.read_text().splitlines()
        self.assertEqual(len(lines), 3)
        self.assertTrue(all(json.loads(line)["utc"] for line in lines))
        out.unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            diagnostics.monitor(out, 123, self.proc, self.cg, self.root, max_bytes=1)
        self.assertEqual(out.stat().st_size, 0)

    def test_parent_exit_records_final_counters(self):
        out = self.root / "samples.jsonl"
        with patch.object(time, "sleep"), contextlib.redirect_stdout(io.StringIO()), \
                patch.object(diagnostics, "parent_alive", side_effect=[True, False]):
            diagnostics.monitor(out, 123, self.proc, self.cg, self.root)
        rows = [json.loads(line) for line in out.read_text().splitlines()]
        self.assertEqual([r['phase'] for r in rows], ['periodic', 'final'])
        self.assertEqual(rows[-1]['cgroup_v2']['memory_events']['oom_kill'], 1)

    def test_existing_output_never_overwritten(self):
        out = self.root / "samples.jsonl"
        out.write_text("preserve")
        with self.assertRaises(FileExistsError):
            diagnostics.monitor(out, 123, self.proc, self.cg, self.root)
        self.assertEqual(out.read_text(), "preserve")

    def test_dead_parent_does_not_start(self):
        out = self.root / "samples.jsonl"
        diagnostics.monitor(out, 999, self.proc, self.cg, self.root)
        self.assertFalse(out.exists())


class ShellTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.env = dict(os.environ, RUNNER_TEMP=str(self.root),
                        PATH=str(self.bin) + os.pathsep + os.environ["PATH"],
                        CALLS=str(self.root / "calls"))
        self.fake_lake('echo "$*" >> "$CALLS"\nexit 0\n')

    def fake_lake(self, body):
        file = self.bin / "lake"
        file.write_text("#!/bin/bash\n" + body)
        file.chmod(0o755)

    def run_build(self, script=BUILD):
        return subprocess.run(["bash", "-c", script], cwd=ROOT, env=self.env,
                              capture_output=True, text=True, timeout=10)

    def calls(self):
        path = self.root / "calls"
        return path.read_text().splitlines() if path.exists() else []

    def test_success_preserves_both_commands(self):
        result = self.run_build()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ["build", "build lint_style"])

    def test_first_build_failure_stops_lint_and_preserves_status(self):
        self.fake_lake('echo "$*" >> "$CALLS"\nexit 7\n')
        result = self.run_build()
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(self.calls(), ["build"])

    def test_second_build_failure_preserves_status(self):
        self.fake_lake('echo "$*" >> "$CALLS"\n[[ "$*" != "build lint_style" ]] || exit 9\n')
        self.assertEqual(self.run_build().returncode, 9)
        self.assertEqual(self.calls(), ["build", "build lint_style"])

    def test_tee_failure_still_fails_pipefail(self):
        file = self.bin / "tee"
        file.write_text("#!/bin/bash\ncat >/dev/null\nexit 11\n")
        file.chmod(0o755)
        self.assertEqual(self.run_build().returncode, 11)

    def test_diagnostic_output_unavailable_does_not_change_success_or_failure(self):
        (self.root / "lean-resources.jsonl").mkdir()
        for code in (0, 7):
            with self.subTest(code=code):
                self.fake_lake(f'sleep 0.1\nexit {code}\n')
                self.assertEqual(self.run_build().returncode, code)

    def test_python_unavailable_does_not_change_success_or_failure(self):
        file = self.bin / "python3"
        file.write_text("#!/bin/bash\nexit 127\n")
        file.chmod(0o755)
        for code in (0, 7):
            self.fake_lake(f'exit {code}\n')
            self.assertEqual(self.run_build().returncode, code)

    def test_normal_success_and_failure_reap_sampler(self):
        for code in (0, 7):
            with self.subTest(code=code):
                self.fake_lake(f'sleep 0.1\nexit {code}\n')
                script = BUILD.replace('\n{\n', '\necho "$_ci_resource_pid" > "$RUNNER_TEMP/sampler.pid"\n{\n')
                result = self.run_build(script)
                self.assertEqual(result.returncode, code)
                pid = int((self.root / "sampler.pid").read_text())
                self.assertIsNone(diagnostics.process(Path('/proc') / str(pid)))
                rows = [json.loads(line) for line in (self.root / 'lean-resources.jsonl').read_text().splitlines()]
                self.assertEqual(rows[-1]['phase'], 'final')
                (self.root / 'lean-resources.jsonl').unlink()

    def test_unresponsive_sampler_cannot_mask_build_failure(self):
        import sys
        file = self.bin / "python3"
        file.write_text(f"#!{sys.executable}\nimport signal,time\nsignal.signal(signal.SIGTERM, signal.SIG_IGN)\nwhile True: time.sleep(1)\n")
        file.chmod(0o755)
        self.fake_lake('sleep 0.1\nexit 7\n')
        script = BUILD.replace('\n{\n', '\necho "$_ci_resource_pid" > "$RUNNER_TEMP/sampler.pid"\n{\n')
        start = time.monotonic()
        self.assertEqual(self.run_build(script).returncode, 7)
        self.assertLess(time.monotonic() - start, 5)
        pid = int((self.root / 'sampler.pid').read_text())
        self.assertIsNone(diagnostics.process(Path('/proc') / str(pid)))

    def test_blocked_console_write_terminates_only_sampler(self):
        import sys
        code = ("import os,sys; from pathlib import Path; "
                "sys.path.insert(0,'scripts'); import ci_resource_diagnostics as d; "
                "d.monitor(Path(sys.argv[1]),os.getppid(),interval=0)")
        p = subprocess.Popen([sys.executable, '-c', code, str(self.root / 'blocked.jsonl')],
                             cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            # Deliberately do not drain stdout, simulating an unavailable sink.
            self.assertEqual(p.wait(timeout=8), -signal.SIGALRM)
        finally:
            if p.poll() is None:
                p.kill()
            p.communicate(timeout=2)

    def test_sigint_sigterm_and_parent_sigkill_leave_no_sampler(self):
        # Send to the step group, as cancellation does. Also kill only the
        # parent to exercise identity polling when the EXIT trap cannot run.
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGKILL):
            with self.subTest(signal=sig):
                pidfile = self.root / "sampler.pid"
                output = self.root / "lean-resources.jsonl"
                output.unlink(missing_ok=True)
                script = ('set -eo pipefail\n'
                          'source scripts/ci_resource_diagnostics.sh "$RUNNER_TEMP/lean-resources.jsonl"\n'
                          'echo "$_ci_resource_pid" > "$RUNNER_TEMP/sampler.pid"\n'
                          'while :; do sleep 0.05; done\n')
                p = subprocess.Popen(["bash", "-c", script], cwd=ROOT, env=self.env,
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                     start_new_session=True)
                sampler = None
                try:
                    deadline = time.monotonic() + 5
                    while time.monotonic() < deadline:
                        if pidfile.exists() and output.exists() and output.stat().st_size:
                            sampler = int(pidfile.read_text())
                            break
                        time.sleep(0.02)
                    self.assertIsNotNone(sampler, "sampler did not start")
                    if sig == signal.SIGKILL:
                        os.kill(p.pid, sig)
                    else:
                        os.killpg(p.pid, sig)
                    code = p.wait(timeout=5)
                    self.assertEqual(code, -9 if sig == signal.SIGKILL else 128 + sig)
                    deadline = time.monotonic() + 4
                    while time.monotonic() < deadline:
                        state = diagnostics.process(Path('/proc') / str(sampler))
                        if state is None or state['state'] == 'Z':
                            break
                        time.sleep(0.05)
                    else:
                        self.fail("sampler survived parent")
                finally:
                    with contextlib.suppress(ProcessLookupError):
                        os.killpg(p.pid, signal.SIGKILL)
                    p.wait(timeout=5)
                    if sampler is not None:
                        with contextlib.suppress(ProcessLookupError):
                            os.kill(sampler, signal.SIGKILL)
                    pidfile.unlink(missing_ok=True)


class WorkflowTest(unittest.TestCase):
    def test_original_build_pipeline_and_required_steps(self):
        self.assertEqual(BUILD.replace(
            'source scripts/ci_resource_diagnostics.sh "$RUNNER_TEMP/lean-resources.jsonl"\n', ''),
            'set -eo pipefail\n{\n  lake build\n  lake build lint_style\n} 2>&1 | tee -a "$RUNNER_TEMP/lake-build.log"\n')
        names = [s.get("name") for s in STEPS]
        ordered = ["Check directly changed Lean sources and tests strictly",
                   "Build changed Lean modules early", "Build Lean project and capture timings",
                   "Upload build resource diagnostics", "Check changed Lean files and affected tests strictly",
                   "Run text-based style linter", "Check Blueprint Lean declarations",
                   "Check paper-gap Lean declarations", "Save Lean build cache (main only)"]
        self.assertEqual([names.index(n) for n in ordered], sorted(names.index(n) for n in ordered))
        for name in (ordered[2], ordered[4], ordered[5], ordered[6], ordered[7]):
            step = STEPS[names.index(name)]
            self.assertNotIn('if', step)
            self.assertNotIn('continue-on-error', step)
        save = STEPS[names.index(ordered[-1])]
        self.assertEqual(save['if'], "success() && github.ref == 'refs/heads/main'")
        self.assertEqual(save['with']['key'], "tnlean-build-${{ hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml') }}-${{ github.sha }}")

    def test_diagnostic_artifact_is_bounded_optional_and_runs_on_failure(self):
        step = next(s for s in STEPS if s.get('name') == 'Upload build resource diagnostics')
        self.assertEqual(step['if'], 'always()')
        self.assertTrue(step['continue-on-error'])
        self.assertEqual(step['timeout-minutes'], 2)
        self.assertEqual(step['with']['path'], '${{ runner.temp }}/lean-resources.jsonl')
        self.assertEqual(step['with']['retention-days'], 7)
        self.assertEqual(step['with']['if-no-files-found'], 'ignore')

    def test_tests_are_executed_and_script_paths_trigger_ci(self):
        policy = WORKFLOW['jobs']['file-length']['steps']
        self.assertTrue(any('python3 scripts/test_ci_resource_diagnostics.py' in s.get('run', '') for s in policy))
        text = (ROOT / '.github/workflows/pr-ci.yml').read_text()
        for name in ('ci_resource_diagnostics.py', 'ci_resource_diagnostics.sh', 'test_ci_resource_diagnostics.py'):
            self.assertEqual(text.count("- 'scripts/" + name + "'"), 3)


if __name__ == '__main__':
    unittest.main()
