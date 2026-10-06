"""Guard the focused restoration check's position and strict build policy."""

from pathlib import Path
import unittest


class WorkflowGuardTests(unittest.TestCase):
    def setUp(self):
        self.workflow = (Path(__file__).resolve().parents[1] /
                         ".github/workflows/pr-ci.yml").read_text()
        start = self.workflow.index("      - name: Check SCP10 restoration lower layers\n")
        end = self.workflow.index("      - name:", start + 1)
        self.step = self.workflow[start:end]
        start = self.workflow.index("      - name: Check SCP10 restoration strict regressions\n")
        end = self.workflow.index("      - name:", start + 1)
        self.regression = self.workflow[start:end]

    def test_provenance_pruning_precedes_focused_checks(self):
        self.assertLess(self.workflow.index("Discard unvalidated cross-commit artifacts"),
                        self.workflow.index("Check SCP10 restoration lower layers"))
        self.assertLess(self.workflow.index("Check SCP10 restoration lower layers"),
                        self.workflow.index("Build Lean project and capture timings"))
        self.assertIn("lake build\n", self.workflow)
        self.assertIn("lake build lint_style", self.workflow)
        self.assertLess(self.workflow.index("Build Lean project and capture timings"),
                        self.workflow.index("Check SCP10 restoration strict regressions"))
        self.assertNotIn("lake env lean", self.step)

    def test_prebuilt_guard_and_strict_checks_are_mandatory(self):
        self.assertLess(self.step.index("test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"),
                        self.step.index("lake --fail-fast build"))
        for option in ("autoImplicit=false", "relaxedAutoImplicit=false",
                       "pp.unicode.fun=true", "maxSynthPendingDepth=3",
                       "linter.mathlibStandardSet=true", "warningAsError=true"):
            self.assertIn("-D" + option, self.regression)
        self.assertIn("set -eo pipefail", self.step)
        self.assertNotIn("continue-on-error", self.step)
        self.assertNotIn("|| true", self.step)
        self.assertIn("set -eo pipefail", self.regression)
        self.assertNotIn("continue-on-error", self.regression)
        self.assertNotIn("|| true", self.regression)

    def test_import_closure_guard_and_regression_are_not_optional(self):
        self.assertIn("TNLeanTest/CommutingMatrixProjectionProduct.lean", self.regression)
        self.assertIn("python3 scripts/check_scp10_restoration.py", self.step)
        self.assertIn("git fetch --no-tags origin ca5273cd335633e0aea2e4930c897d732b8260de",
                      self.step)
        self.assertNotIn("if:", self.step)


if __name__ == "__main__":
    unittest.main()
