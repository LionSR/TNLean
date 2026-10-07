#!/usr/bin/env python3
"""Exercise the real blueprint workflow steps against a moving, criss-cross base."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/pr-ci.yml").read_text())
BLUEPRINT = WORKFLOW["jobs"]["blueprint"]
STEPS = {step.get("name"): step for step in BLUEPRINT["steps"]}


class ImmutableBaseTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "CI regression")
        self.git("config", "user.email", "ci@example.invalid")
        self.write("README", "fixture\n")
        self.commit("root")
        root_commit = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("checkout", "-qb", "left")
        self.write("TNLean/Fixture/Added.lean", "namespace Regression\n"
                   "theorem added : True := by trivial\nend Regression\n")
        self.commit("PR declaration")
        left = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("checkout", "-qb", "moving-base", root_commit)
        self.write("base.txt", "base before the workflow starts\n")
        self.commit("event base")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("checkout", "-q", "left")
        self.git("merge", "--no-ff", "-m", "PR merge snapshot", self.base)
        self.git("checkout", "-q", "moving-base")
        self.git("merge", "--no-ff", "-m", "base advances independently", left)
        self.git("checkout", "-q", "left")
        self.git("remote", "add", "origin", str(self.root))
        (self.root / "scripts").mkdir()
        shutil.copy2(ROOT / "scripts/blueprint_lean_sync.py", self.root / "scripts")
        self.output = self.root / "github-output"

    def git(self, *args, check=True):
        return subprocess.run(["git", *args], cwd=self.root, check=check,
                              text=True, capture_output=True)

    def write(self, path, content):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

    def commit(self, message):
        self.git("add", ".")
        self.git("commit", "-qm", message)

    def run_step(self, name, *, base=None, check=True):
        env = os.environ | {"BASE_REF": base or self.base,
                            "GITHUB_OUTPUT": str(self.output)}
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", STEPS[name]["run"]],
                              cwd=self.root, env=env, text=True,
                              capture_output=True, check=check)

    def test_event_snapshot_survives_multiple_merge_bases_and_keeps_coverage(self):
        bases = self.git("merge-base", "--all", "HEAD", "moving-base").stdout.split()
        self.assertEqual(len(bases), 2)
        old = self.git("diff", "--merge-base", "--name-only", "moving-base", check=False)
        self.assertNotEqual(old.returncode, 0)
        self.assertIn("multiple merge bases", old.stderr)
        self.run_step("Fetch immutable PR base for blueprint comparisons")
        self.run_step("Detect changed Lean files")
        self.assertIn("has_changed_lean=true", self.output.read_text())
        self.run_step("Verify immutable PR base for diff")
        coverage = self.run_step("Error on changed Lean declarations missing blueprint entries")
        self.assertIn("Regression.added", coverage.stdout)
        self.write("blueprint/src/chapter/fixture.tex", "\\begin{theorem}\n"
                   "\\lean{Regression.added}\n\\end{theorem}\n")
        covered = self.run_step("Error on changed Lean declarations missing blueprint entries")
        self.assertIn("No changed def/theorem/lemma declarations are missing", covered.stdout)

    def test_nonancestor_is_rejected_instead_of_selecting_an_arbitrary_merge_base(self):
        wrong_base = self.git("rev-parse", "moving-base").stdout.strip()
        for name in ("Fetch immutable PR base for blueprint comparisons",
                     "Verify immutable PR base for diff"):
            self.assertNotEqual(self.run_step(name, base=wrong_base, check=False).returncode, 0)

    def test_workflow_uses_one_event_sha_and_retains_all_coverage_steps(self):
        expression = "${{ github.event.pull_request.base.sha }}"
        self.assertEqual(BLUEPRINT["env"]["BASE_REF"], expression)
        for step in BLUEPRINT["steps"]:
            self.assertNotIn("BASE_REF", step.get("env", {}))
            self.assertNotIn("github.event.pull_request.base.ref", step.get("run", ""))
        timing = next(s for s in WORKFLOW["jobs"]["build"]["steps"]
                      if s.get("name") == "Check changed Lean compilation times")
        self.assertEqual(timing["env"]["BASE_REF"], expression)
        self.assertIn('git merge-base --is-ancestor "$BASE_REF" HEAD', timing["run"])
        self.assertNotIn("--merge-base", timing["run"])
        for name in ("Check reader-facing prose patterns", "Check blueprint and Lean source stay in sync",
                     "Generate lean_decls from blueprint .tex files",
                     "Error on changed Lean declarations missing blueprint entries"):
            self.assertIn(name, STEPS)


if __name__ == "__main__":
    unittest.main()
