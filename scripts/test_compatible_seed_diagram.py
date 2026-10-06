#!/usr/bin/env python3
"""Guard the full-ring wire convention of the compatible-seed diagram."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch32_log_depth_compatible_seed.tex"


class CompatibleSeedDiagramTests(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text()
        self.diagram = self.source.split(r"\begin{tenkzequation}", 1)[1].split(
            r"\end{tenkzequation}", 1
        )[0]

    def test_web_supported_equation(self):
        self.assertNotIn(r"\begin{tenkzeq}", self.source)
        self.assertEqual(self.diagram.count(r"\begin{tenkz}"), 2)

    def test_typed_boundary_and_composition_order(self):
        self.assertEqual(self.diagram.count(r"90:physical:$\mathcal H_N$"), 2)
        self.assertEqual(self.diagram.count(r"270:physical:$\mathcal H_N$"), 2)
        self.assertEqual(
            re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", self.diagram),
            [("ua.90", "r.270"), ("r.90", "ub.270")],
        )
        for location, name, label in [(1, "ub", "U_B"), (2, "r", "R"), (3, "ua", r"U_A^\dagger")]:
            self.assertRegex(self.diagram, rf"(?s)at=\({location},1\).*?name={name},.*?\]\{{{re.escape(label)}\}}")

    def test_no_suppressed_normalization_or_free_block_gate(self):
        self.assertIn("No trace, state contraction, or normalization scalar is suppressed", self.source)
        self.assertIn("whole circuits on $N$ sites", self.source)
        self.assertIn("not\n    free gates on growing physical blocks", self.source)
        self.assertNotIn(r"\operatorname{tr}", self.diagram)
        self.assertNotIn(r"\sqrt", self.diagram)


if __name__ == "__main__":
    unittest.main()
