#!/usr/bin/env python3
"""Run the real PR workflow blocks against small Git histories, without Lean."""

import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/pr-ci.yml").read_text())
BLUEPRINT = WORKFLOW["jobs"]["blueprint"]
STEPS = {step.get("name"): step for step in BLUEPRINT["steps"]}
TIMING_NAME = "Check changed Lean compilation times"
STEPS[TIMING_NAME] = next(step for step in WORKFLOW["jobs"]["build"]["steps"]
                          if step.get("name") == TIMING_NAME)
ENFORCE = "Enforce changed-module timing limit"
STEPS[ENFORCE] = next(step for job in WORKFLOW["jobs"].values()
                      for step in job.get("steps", []) if step.get("name") == ENFORCE)
DEBT_STEPS = {step.get("name"): step for step in WORKFLOW["jobs"]["file-length"]["steps"]}
DEBT_FETCH = "Fetch pull-request base for the debt ratchet"
STEPS[DEBT_FETCH] = DEBT_STEPS[DEBT_FETCH]
FETCH = "Fetch immutable PR base for blueprint comparisons"
VERIFY = "Verify immutable PR base for diff"
DETECT = "Detect changed Lean files"
COVERAGE = "Error on changed Lean declarations missing blueprint entries"
LEAN = "TNLean/Fixture/Existing.lean"
TEX = "blueprint/src/chapter/fixture.tex"


class ImmutableBaseTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        self.runtime = Path(self.tmp.name) / "runner"
        self.runtime.mkdir()
        self.bin = Path(self.tmp.name) / "bin"
        self.bin.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "CI regression")
        self.git("config", "user.email", "ci@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.write("README", "fixture\n")
        self.write(LEAN, "namespace Regression\ntheorem existing : True := by trivial\nend Regression\n")
        self.write(TEX, "Plain prose.\n")
        self.commit("event base")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("branch", "moving-base")
        self.git("remote", "add", "origin", str(self.root))
        (self.root / "scripts").mkdir()
        for script in ("blueprint_lean_sync.py", "lake_build_hotspots.py", "check_reader_facing_prose.py"):
            shutil.copy2(ROOT / "scripts" / script, self.root / "scripts")
        self.output = self.runtime / "github-output"
        self.write_executable("lake", "#!/bin/sh\necho 'Unexpected Lean compilation' >&2\nexit 99\n")

    def git(self, *args, check=True):
        return subprocess.run(["git", *args], cwd=self.root, check=check,
                              text=True, capture_output=True)

    def write(self, path, content):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

    def commit(self, message):
        # Runtime scripts and Git/Python wrappers are not part of the PR diff.
        self.git("add", "--all", "--", ".", ":(exclude)scripts")
        self.git("commit", "-qm", message)

    def write_executable(self, name, content):
        target = self.bin / name
        target.write_text(content)
        target.chmod(0o755)

    def fail_git(self, command, *, path=None):
        """Fail only the selected real Git call, including `git -c ... diff`."""
        real_git = shlex.quote(shutil.which("git"))
        predicate = f'[[ " $* " == *" {command} "* ]]'
        if path is not None:
            predicate += f' && [[ " $* " == *{shlex.quote(path)}* ]]'
        self.write_executable("git", "#!/bin/bash\n"
                              f"if {predicate}; then\n"
                              "  echo 'injected git failure' >&2\n  exit 73\nfi\n"
                              f'exec {real_git} "$@"\n')

    def run_step(self, name, *, base=None, check=True, extra_env=None):
        self.output.unlink(missing_ok=True)
        env = os.environ | {"BASE_REF": self.base if base is None else base,
                            "GITHUB_OUTPUT": str(self.output),
                            "RUNNER_TEMP": str(self.runtime),
                            "PATH": str(self.bin) + os.pathsep + os.environ["PATH"]}
        env.update(extra_env or {})
        result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", STEPS[name]["run"]],
                                cwd=self.root, env=env, text=True, capture_output=True)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def assert_detection(self, expected):
        self.run_step(DETECT)
        self.assertEqual(self.output.read_text(), f"has_changed_lean={str(expected).lower()}\n")

    def make_criss_cross(self):
        self.git("checkout", "-qb", "left")
        self.write("TNLean/Fixture/Added.lean", "namespace Regression\n"
                   "theorem added : True := by trivial\nend Regression\n")
        self.commit("PR declaration")
        left = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("checkout", "-q", "moving-base")
        self.write("base.txt", "base before workflow starts\n")
        self.commit("event snapshot")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("checkout", "-q", "left")
        self.git("merge", "--no-ff", "-m", "PR merge snapshot", self.base)
        self.git("checkout", "-q", "moving-base")
        self.git("merge", "--no-ff", "-m", "base advances independently", left)
        self.git("checkout", "-q", "left")

    def test_event_snapshot_survives_multiple_merge_bases_and_keeps_coverage(self):
        self.make_criss_cross()
        self.assertEqual(len(self.git("merge-base", "--all", "HEAD", "moving-base").stdout.split()), 2)
        old = self.git("diff", "--merge-base", "--name-only", "moving-base", check=False)
        self.assertNotEqual(old.returncode, 0)
        self.assertIn("multiple merge bases", old.stderr)
        self.run_step(FETCH)
        self.run_step(DEBT_FETCH)
        self.assert_detection(True)
        self.run_step(VERIFY)
        (self.runtime / "lake-build.log").write_text("Built TNLean.Fixture.Added (50s)\n")
        self.run_step(TIMING_NAME)
        self.assertEqual(self.output.read_text(), "result=limit\n")
        self.assertEqual((self.runtime / "changed-lean-files.txt").read_text(),
                         "TNLean/Fixture/Added.lean\n")
        coverage = self.run_step(COVERAGE)
        self.assertIn("Regression.added", coverage.stdout)
        self.write(TEX, "\\begin{theorem}\n\\lean{Regression.added}\n\\end{theorem}\n")
        covered = self.run_step(COVERAGE)
        self.assertIn("No changed def/theorem/lemma declarations are missing", covered.stdout)

    def test_moving_branch_cannot_hide_pr_change(self):
        self.write(LEAN, "namespace Regression\ntheorem added : True := by trivial\nend Regression\n")
        self.commit("PR change")
        # The remote branch now contains the PR, so diffing it would hide the change.
        self.git("branch", "-f", "moving-base", "HEAD")
        self.assertEqual(self.git("diff", "--name-only", "moving-base", "HEAD").stdout, "")
        self.run_step(FETCH)
        self.run_step(DEBT_FETCH)
        self.assert_detection(True)
        self.assertIn("Regression.added", self.run_step(COVERAGE).stdout)

    def test_lean_add_modify_rename_delete_are_detected(self):
        for operation in ("add", "modify", "rename", "delete"):
            with self.subTest(operation=operation):
                self.git("reset", "--hard", self.base)
                if operation == "add":
                    self.write("TNLean/Fixture/New.lean", "theorem fresh : True := by trivial\n")
                elif operation == "modify":
                    self.write(LEAN, "theorem replacement : True := by trivial\n")
                elif operation == "rename":
                    self.git("mv", LEAN, "TNLean/Fixture/Renamed.lean")
                else:
                    self.git("rm", LEAN)
                self.commit(operation)
                self.assert_detection(True)
                # Deletions must trigger sync but are not passed as nonexistent
                # input files to the changed-declaration scanner.
                result = self.run_step(COVERAGE)
                if operation == "delete":
                    self.assertIn("No changed TNLean/*.lean files", result.stdout)

    def test_config_only_changes_trigger_sync(self):
        for path in ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"):
            with self.subTest(path=path):
                self.git("reset", "--hard", self.base)
                self.write(path, "fixture\n")
                self.commit("config only")
                self.assert_detection(True)
                self.assertIn("No changed TNLean/*.lean files", self.run_step(COVERAGE).stdout)

    def test_unchanged_and_prose_only_input_skip_sync(self):
        self.assert_detection(False)
        self.write(TEX, "New prose, without Lean markers.\n")
        self.commit("prose only")
        self.assert_detection(False)
        self.write("blueprint/src/chapter/new.tex", "New file without markers.\n")
        self.commit("add plain TeX")
        self.assert_detection(False)

    def test_added_tex_markers_trigger_sync(self):
        for marker in (r"\lean{Regression.existing}", r"\uses{label}", r"\leanok", r"\notready"):
            with self.subTest(marker=marker):
                self.git("reset", "--hard", self.base)
                self.write("blueprint/src/chapter/new.tex", marker + "\n")
                self.commit("TeX-only marker")
                self.assert_detection(True)

    def test_removed_markers_and_deleted_or_renamed_tex_trigger_sync(self):
        common_prose = "".join(f"Unchanged paragraph {index}.\n" for index in range(30))
        self.write(TEX, common_prose + "\\lean{Regression.existing}\n")
        self.commit("base marker")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        for operation in ("remove marker", "delete", "rename"):
            with self.subTest(operation=operation):
                self.git("reset", "--hard", self.base)
                if operation == "remove marker":
                    self.write(TEX, "Now just prose.\n")
                elif operation == "delete":
                    self.git("rm", TEX)
                else:
                    self.git("mv", TEX, "blueprint/src/chapter/renamed.tex")
                    self.write("blueprint/src/chapter/renamed.tex", common_prose)
                self.commit(operation)
                if operation == "rename":
                    status = self.git("diff", "--find-renames", "--name-status", self.base, "HEAD").stdout
                    self.assertRegex(status, r"(?m)^R\d+\s", "fixture must be a real detected rename")
                self.assert_detection(True)

    def test_missing_and_nonancestor_bases_fail_closed(self):
        self.make_criss_cross()
        wrong_base = self.git("rev-parse", "moving-base").stdout.strip()
        for base in ("", "0" * 40, wrong_base):
            for name in (FETCH, VERIFY, DEBT_FETCH):
                with self.subTest(base=base, step=name):
                    self.assertNotEqual(self.run_step(name, base=base, check=False).returncode, 0)

    def test_fetch_failure_is_not_swallowed(self):
        self.fail_git("fetch")
        for name in (FETCH, DEBT_FETCH):
            with self.subTest(step=name):
                result = self.run_step(name, check=False)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("injected git failure", result.stderr)

    def test_lean_and_tex_diff_failures_are_not_swallowed(self):
        for path in ("TNLean.lean", "blueprint/src/"):
            with self.subTest(path=path):
                self.fail_git("diff", path=path)
                result = self.run_step(DETECT, check=False)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("injected git failure", result.stderr)
                self.assertFalse(self.output.exists(), "failure must not emit a successful change decision")

    def test_existing_tex_show_failure_is_not_treated_as_an_added_file(self):
        self.write(TEX, "Updated prose.\n")
        self.commit("modify existing TeX")
        for command in ("ls-tree", "show"):
            with self.subTest(command=command):
                self.fail_git(command)
                result = self.run_step(DETECT, check=False)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("injected git failure", result.stderr)
                self.assertFalse(self.output.exists())

    def test_changed_declaration_diff_failure_is_not_swallowed(self):
        self.fail_git("diff")
        self.assertNotEqual(self.run_step(COVERAGE, check=False).returncode, 0)

    def test_timing_pass_threshold_and_checker_error_use_real_logs(self):
        self.write(LEAN, "theorem updated : True := by trivial\n")
        self.commit("changed timed module")
        log = self.runtime / "lake-build.log"
        for seconds, expected in ((24, "success"), (25, "success"), (50, "limit")):
            with self.subTest(seconds=seconds):
                log.write_text(f"Built TNLean.Fixture.Existing ({seconds}s)\n"
                               "Built TNLean.Unchanged (999s)\n")
                result = self.run_step(TIMING_NAME)
                self.assertEqual(self.output.read_text(), f"result={expected}\n")
                self.assertEqual((self.runtime / "changed-lean-files.txt").read_text(), LEAN + "\n")
                if seconds >= 25:
                    self.assertIn("::warning" if seconds < 50 else "::error", result.stdout)
        log.unlink()  # A real checker input error must not be reported as a timing limit.
        self.run_step(TIMING_NAME)
        self.assertEqual(self.output.read_text(), "result=error\n")

    def test_early_actual_round_timings_reach_the_final_failure_gate(self):
        source = "TNLean/PEPS/AreaLaw/Scan/ActualRoundTransport.lean"
        module = "TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport"
        self.write(source, "theorem synthetic_timed_source : True := by trivial\n")
        self.commit("add synthetic changed actual-round module")
        log = self.runtime / "lake-build.log"
        for facet, seconds, later in (
            ("", 50, f"Replayed {module} (1s)\nBuild completed successfully (2 jobs).\n"),
            (":olean", 51, "Build completed successfully (9713 jobs).\n"),
        ):
            with self.subTest(facet=facet, seconds=seconds):
                log.write_text(f"Built {module}{facet} ({seconds}s)\n")
                with log.open("a") as stream:
                    stream.write(later)
                before = log.read_bytes()
                result = self.run_step(TIMING_NAME)
                self.assertEqual(self.output.read_text(), "result=limit\n")
                self.assertEqual(log.read_bytes(), before)
                self.assertEqual((self.runtime / "changed-lean-files.txt").read_text(), source + "\n")
                self.assertIn(f"::error file={source}::{module}{facet} compiled in {seconds}.000s",
                              result.stdout)
                enforced = self.run_step(ENFORCE, check=False, extra_env={"TIMING_RESULT": "limit"})
                self.assertNotEqual(enforced.returncode, 0)
                self.assertIn("50-second compilation limit", enforced.stdout)

    def test_timing_fetch_diff_and_invalid_base_errors(self):
        (self.runtime / "lake-build.log").write_text("")
        for command in ("fetch", "diff"):
            with self.subTest(command=command):
                self.fail_git(command)
                result = self.run_step(TIMING_NAME)
                self.assertEqual(self.output.read_text(), "result=error\n")
                self.assertIn("injected git failure", result.stderr)
        (self.bin / "git").unlink()
        self.make_criss_cross()
        for base in ("", "0" * 40, self.git("rev-parse", "moving-base").stdout.strip()):
            with self.subTest(base=base):
                self.run_step(TIMING_NAME, base=base)
                self.assertEqual(self.output.read_text(), "result=error\n")

    def test_coverage_is_scoped_to_changed_declarations_in_a_changed_file(self):
        self.write(LEAN, "namespace Regression\n"
                   "theorem existing : True := by trivial\n"
                   "theorem added : True := by trivial\nend Regression\n")
        self.commit("add declaration beside old untagged declaration")
        result = self.run_step(COVERAGE)
        self.assertIn("Regression.added", result.stdout)
        self.assertNotIn("Regression.existing", result.stdout)
        self.write(TEX, "\\begin{theorem}\n\\lean{Regression.added}\n\\end{theorem}\n")
        covered = self.run_step(COVERAGE)
        self.assertIn("No changed def/theorem/lemma declarations are missing", covered.stdout)
        self.assertNotIn("Regression.existing", covered.stdout)

    def test_prose_guard_rejects_new_but_not_existing_violations(self):
        self.write(TEX, "Old tracker shorthand #123.\n")
        self.commit("old prose violation")
        self.git("branch", "-f", "moving-base", "HEAD")
        self.make_criss_cross()
        name = "Check reader-facing prose patterns"
        clean = self.run_step(name)
        self.assertIn("No newly added reader-facing prose violations", clean.stdout)
        self.write(TEX, "Old tracker shorthand #123.\nNew tracker shorthand #456.\n")
        self.commit("new prose violation")
        result = self.run_step(name, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("#456", result.stdout)
        self.assertNotIn("#123", result.stdout)
        self.fail_git("diff")
        self.assertNotEqual(self.run_step(name, check=False).returncode, 0)

    def test_downstream_timing_gate_preserves_limit_and_error_failures(self):
        for timing_result in ("success", "limit", "error", ""):
            with self.subTest(timing_result=timing_result):
                result = self.run_step(ENFORCE, check=False,
                                       extra_env={"TIMING_RESULT": timing_result})
                if timing_result == "success":
                    self.assertEqual(result.returncode, 0)
                    self.assertNotIn("::error", result.stdout)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("50-second compilation limit" if timing_result == "limit"
                                  else "compilation-time checker failed", result.stdout)

    def test_workflow_uses_one_event_sha_and_retains_all_coverage_steps(self):
        expression = "${{ github.event.pull_request.base.sha }}"
        self.assertEqual(WORKFLOW["jobs"]["file-length"]["env"]["BASE_REF"], expression)
        self.assertIn('--base-ref "$BASE_REF"',
                      DEBT_STEPS["Reject new numbered-sequel modules (pull request)"]["run"])
        self.assertIn('${{ github.event.before }}',
                      DEBT_STEPS["Reject new numbered-sequel modules (push)"]["run"])
        self.assertIn('--base-ref HEAD^',
                      DEBT_STEPS["Reject new numbered-sequel modules (manual dispatch)"]["run"])
        self.assertEqual(BLUEPRINT["env"]["BASE_REF"], expression)
        for step in BLUEPRINT["steps"]:
            self.assertNotIn("BASE_REF", step.get("env", {}))
            self.assertNotIn("github.event.pull_request.base.ref", step.get("run", ""))
        self.assertEqual(STEPS[TIMING_NAME]["env"]["BASE_REF"], expression)
        self.assertIn('git merge-base --is-ancestor "$BASE_REF" HEAD', STEPS[TIMING_NAME]["run"])
        self.assertNotIn("--merge-base", STEPS[TIMING_NAME]["run"])
        for name in ("Check reader-facing prose patterns", "Check blueprint and Lean source stay in sync",
                     "Generate lean_decls from blueprint .tex files", COVERAGE):
            self.assertIn(name, STEPS)


if __name__ == "__main__":
    unittest.main()
