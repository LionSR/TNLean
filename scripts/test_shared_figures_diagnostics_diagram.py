#!/usr/bin/env python3
"""Exercise shared-figure diagnostics with mocked TeX, never a real renderer."""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import run_diagram_tests as runner
import test_shared_figures_diagram as shared


class ContractDiagnosticsTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / "output"
        self.names = ["alpha", "beta", "gamma", "delta"]
        self.labels = {"beta": {r"\tnlBetaLabel"}, "delta": {r"\tnlDeltaLabel"}}
        self.calls = []

    def fake_run(self, command, **kwargs):
        work = Path(kwargs["cwd"])
        self.calls.append((command, kwargs, work))
        self.assertNotEqual(kwargs["stdout"], subprocess.PIPE)
        self.assertTrue((work / "contract.tex").exists())
        status = json.loads((work / "status.json").read_text())
        if command[0] == "/mock/pdflatex":
            self.assertEqual(status["stage"], "tex-start")
            self.assertEqual(command[1:],
                             ["-interaction=nonstopmode", "-halt-on-error", "contract.tex"])
            self.assertEqual(kwargs["timeout"], 1800)
            kwargs["stdout"].write("partial TeX output\n")
            kwargs["stdout"].flush()
            self.assertEqual((work / "tex.stdout.log").read_text(), "partial TeX output\n")
            (work / "contract.pdf").write_bytes(b"mock PDF")
            (work / "contract.log").write_text("(/mock/tikz-tensor-networks.sty)\n")
        else:
            self.assertEqual(command, ["/mock/pdftotext", "contract.pdf", "-"])
            self.assertEqual(status["stage"], "pdftotext-start")
            kwargs["stdout"].write("QQQ " * status["override_label_count"])
        return subprocess.CompletedProcess(command, 0)

    def run_contract(self, fake=None, *, output=True, jobs=2, pdftotext=True):
        def which(name):
            return None if name == "pdftotext" and not pdftotext else "/mock/" + name
        with patch.object(shared.shutil, "which", side_effect=which), \
                patch.object(shared, "tenkz_tex", return_value=self.root), \
                patch.object(shared.subprocess, "run", side_effect=fake or self.fake_run), \
                patch("builtins.print") as printed:
            failures = shared.compile_contract(
                self.root, self.names, self.labels, "pdflatex", True, jobs,
                self.output if output else None,
            )
        for call in printed.call_args_list:
            self.assertTrue(call.kwargs.get("flush"), call)
        return failures

    def test_success_preserves_exact_documents_and_existing_checks(self):
        self.assertEqual(self.run_contract(), [])
        roots = list(self.output.glob("contract-*"))
        self.assertEqual(len(roots), 1)
        for index in range(2):
            work = roots[0] / f"part{index}"
            chunk = self.names[index::2]
            self.assertEqual((work / "contract.tex").read_text(),
                             shared.contract_document(chunk, self.labels))
            status = json.loads((work / "status.json").read_text())
            self.assertEqual(status["figures"], chunk)
            self.assertEqual(status["stage"], "complete")
            self.assertEqual(status["tex_returncode"], 0)
            self.assertEqual(status["pdftotext_returncode"], 0)
            self.assertGreaterEqual(status["elapsed_seconds"], 0)
            self.assertTrue((work / "tex.stdout.log").exists())
        self.assertEqual(len(self.calls), 4)

    def test_failed_tex_keeps_partial_output_and_generated_source(self):
        def fail(command, **kwargs):
            kwargs["stdout"].write("actual TeX failure\n")
            return subprocess.CompletedProcess(command, 2)
        failures = self.run_contract(fail)
        self.assertEqual(len(failures), 2)
        self.assertTrue(all("actual TeX failure" in item for item in failures))
        for status in self.output.glob("contract-*/part*/status.json"):
            self.assertEqual(json.loads(status.read_text())["stage"], "tex-failed")
            self.assertTrue(status.with_name("contract.tex").exists())
            self.assertIn("actual TeX failure", status.with_name("tex.stdout.log").read_text())

    def test_inner_timeout_keeps_output_and_reports_error(self):
        def timeout(command, **kwargs):
            kwargs["stdout"].write("before timeout\n")
            raise subprocess.TimeoutExpired(command, kwargs["timeout"])
        failures = self.run_contract(timeout, jobs=1)
        self.assertEqual(len(failures), 1)
        status = next(self.output.glob("contract-*/part*/status.json"))
        self.assertEqual(json.loads(status.read_text())["stage"], "tex-error")
        self.assertEqual(status.with_name("tex.stdout.log").read_text(), "before timeout\n")

    def test_launch_failure_is_reported_and_preserved(self):
        def missing(command, **kwargs):
            raise OSError("mock launch failure")
        failures = self.run_contract(missing, jobs=1)
        self.assertIn("mock launch failure", failures[0])
        status = next(self.output.glob("contract-*/part*/status.json"))
        self.assertEqual(json.loads(status.read_text())["stage"], "tex-error")

    def test_new_run_cannot_reuse_stale_pdf(self):
        self.assertEqual(self.run_contract(jobs=1), [])
        def no_pdf(command, **kwargs):
            return subprocess.CompletedProcess(command, 0)
        self.assertTrue(self.run_contract(no_pdf, jobs=1))
        self.assertEqual(len(list(self.output.glob("contract-*"))), 2)

    def test_override_failures_remain_failures(self):
        def no_overrides(command, **kwargs):
            if command[0] == "/mock/pdflatex":
                return self.fake_run(command, **kwargs)
            return subprocess.CompletedProcess(command, 1)
        failures = self.run_contract(no_overrides)
        self.assertIn("host overrides did not win", failures[0])

    def test_no_pdftotext_retains_previous_optional_check_behavior(self):
        self.assertEqual(self.run_contract(pdftotext=False), [])
        self.assertEqual(len(self.calls), 2)
        for status in self.output.glob("contract-*/part*/status.json"):
            self.assertEqual(json.loads(status.read_text())["pdftotext"], "unavailable")

    def test_without_output_dir_keeps_temporary_cleanup(self):
        self.assertEqual(self.run_contract(output=False), [])
        self.assertTrue(self.calls)
        self.assertTrue(all(not work.exists() for _, _, work in self.calls))

    def test_runner_recognizes_output_option(self):
        test = Path(shared.__file__)
        self.assertEqual(runner.command(test, self.output)[-2:],
                         ["--" + "output-dir", str(self.output / test.stem)])
        # The runner probes source literals to detect opt-in. This harness
        # is a unittest script, so it must not receive the renderer option.
        harness = Path(__file__)
        self.assertEqual(runner.command(harness, self.output),
                         [sys.executable, str(harness)])

    def test_interrupted_status_update_keeps_last_complete_record(self):
        original_replace = Path.replace

        def interrupted_replace(source, target):
            if Path(target).exists():
                raise OSError("mock interruption before atomic replace")
            return original_replace(source, target)

        with patch.object(Path, "replace", interrupted_replace):
            with self.assertRaisesRegex(OSError, "mock interruption"):
                self.run_contract(jobs=1)
        state = next(self.output.glob("contract-*/part*/status.json"))
        self.assertEqual(json.loads(state.read_text())["stage"], "tex-start")
        self.assertEqual(json.loads(state.with_name("status.tmp").read_text())["stage"],
                         "tex-finished")

    def test_outer_group_timeout_leaves_diagnostics(self):
        # The child calls the real orchestration but substitutes a blocking
        # Python stand-in for subprocess.run. No TeX executable is started.
        ready = self.root / "ready"
        source = (
            "import sys, time\n"
            "from pathlib import Path\n"
            f"sys.path.insert(0, {str(Path(shared.__file__).parent)!r})\n"
            "import test_shared_figures_diagram as shared\n"
            "shared.shutil.which = lambda name: '/mock/' + name\n"
            f"shared.tenkz_tex = lambda: Path({str(self.root)!r})\n"
            "def blocked(command, **kwargs):\n"
            "    kwargs['stdout'].write('before outer kill\\n')\n"
            "    kwargs['stdout'].flush()\n"
            f"    Path({str(ready)!r}).write_text('ready')\n"
            "    while True: time.sleep(1)\n"
            "shared.subprocess.run = blocked\n"
            f"shared.compile_contract(Path({str(self.root)!r}), ['alpha'], {{}}, "
            f"'pdflatex', True, 1, Path({str(self.output)!r}))\n"
        )
        real_popen = subprocess.Popen

        def ready_popen(*args, **kwargs):
            # Start the production runner's timeout only after the stand-in
            # has flushed its diagnostics, independent of child startup load.
            proc = real_popen(*args, **kwargs)
            try:
                deadline = time.monotonic() + 30
                while not ready.exists():
                    if proc.poll() is not None:
                        self.fail("stand-in exited before writing its ready marker")
                    if time.monotonic() >= deadline:
                        self.fail("stand-in did not become ready within 30 seconds")
                    time.sleep(0.01)
                return proc
            except BaseException:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                raise

        with patch.object(runner.subprocess, "Popen", side_effect=ready_popen):
            code, status = runner.run([sys.executable, "-c", source], self.root, 2)
        self.assertEqual(code, 1)
        self.assertIn("timed out after 2s", status)
        state = next(self.output.glob("contract-*/part*/status.json"))
        self.assertEqual(json.loads(state.read_text())["stage"], "tex-start")
        self.assertEqual(state.with_name("tex.stdout.log").read_text(), "before outer kill\n")
        self.assertTrue(state.with_name("contract.tex").exists())


if __name__ == "__main__":
    unittest.main()
