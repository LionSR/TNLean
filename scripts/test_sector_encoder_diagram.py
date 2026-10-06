#!/usr/bin/env python3
"""Check the logical and physical boundary types of the coherent-encoder diagram."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch32_log_depth_sector_encoders.tex"


class SectorEncoderDiagramTests(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text()
        self.diagram = self.source.split(r"\begin{tenkzequation}", 1)[1].split(
            r"\end{tenkzequation}", 1
        )[0]

    def test_matching_logical_to_physical_boundaries(self):
        self.assertEqual(self.diagram.count(r"\begin{tenkz}"), 2)
        self.assertEqual(self.diagram.count(r"90:physical:$\mathcal H_N$"), 2)
        self.assertEqual(self.diagram.count(r"270:virtual:$\C^b$"), 2)
        self.assertNotIn(r"\begin{tenkzeq}", self.source)

    def test_physical_contraction_and_operator_order(self):
        self.assertEqual(
            re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", self.diagram),
            [("wa.90", "u.270")],
        )
        for location, name, label in [(1, "u", r"U_B U_A^\dagger"), (2, "wa", "U_A J")]:
            self.assertRegex(
                self.diagram,
                rf"(?s)at=\({location},1\).*?name={name},.*?\]\{{{re.escape(label)}\}}",
            )
        self.assertIn("{U_B J}", self.diagram)

    def test_no_trace_or_reference_contraction(self):
        self.assertNotIn(r"\operatorname{tr}", self.diagram)
        self.assertNotIn(r"\Tr", self.diagram)
        self.assertIn("complete circuits", self.source)
        self.assertIn("logical wire carries every superposition", self.source)


if __name__ == "__main__":
    unittest.main()
