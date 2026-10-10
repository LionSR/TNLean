#!/usr/bin/env python3
"""Check the exact clipped-square samples and edge in the native tenkz diagram."""

from fractions import Fraction
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch24_peps_nested_patch_geometry.tex"


class NestedPatchGeometryDiagramTests(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text(encoding="utf-8")
        diagrams = re.findall(r"\\begin\{tenkz\}\[.*?\\end\{tenkz\}", self.source, re.S)
        self.assertEqual(len(diagrams), 1)
        self.diagram = diagrams[0]
        self.domain = {(x, y) for x in range(11) for y in range(3)}
        self.center = (Fraction(5, 4), Fraction(3, 2))
        self.patches = [
            {site for site in self.domain
             if all(abs(site[k] - self.center[k]) <= radius for k in range(2))}
            for radius in (4, 6, 8)
        ]
        self.edge = frozenset({(7, 1), (8, 1)})

    def test_native_finite_grid(self):
        self.assertIn("rows={wire,wire,wire}", self.diagram)
        self.assertIn("cols=11", self.diagram)
        self.assertEqual(len(re.findall(r"\\tn\[", self.diagram)), 33)
        for side in ("west", "east", "north", "south"):
            self.assertIn(f"{side}=none", self.diagram)
        for forbidden in (r"\draw", r"\node", "trace", "physical=", "boundary=open"):
            self.assertNotIn(forbidden, self.diagram)
        edges = {
            frozenset({site, neighbor}) for site in self.domain
            for neighbor in ((site[0] + 1, site[1]), (site[0], site[1] + 1))
            if neighbor in self.domain
        }
        self.assertEqual((len(self.domain), len(edges)), (33, 52))
        self.assertIn(self.edge, edges)
        self.assertIn("not a tensor contraction or an operator", self.source)

    def test_exact_closed_samples_match_enclosures(self):
        marks = re.findall(
            r"\\tnmark\[form=enclosure,[^]]*\]\s*"
            r"\{\(1,1\) \.\. \(3,(\d+)\)\}\{\$\\textcolor\{\w+\}\{K_(\d)\}\$\}",
            self.diagram,
        )
        self.assertEqual(marks, [("6", "0"), ("8", "1"), ("10", "2")])
        for index, color in enumerate(("tenkzAction", "tenkzMarked", "tenkzExtra")):
            self.assertIn(r"$\textcolor{" + color + "}{K_" + str(index) + "}$", self.diagram)
        self.assertIn("rounded outlines enclose the clipped sets", self.source)
        for columns, index in marks:
            drawn = {(x, y) for x in range(int(columns)) for y in range(3)}
            self.assertEqual(self.patches[int(index)], drawn)
        self.assertEqual(len(self.patches), 4 // 2 + 1)

    def test_marked_edge_and_unique_crossing(self):
        self.assertRegex(self.diagram, r"at=\(2,8\), name=inside,")
        self.assertRegex(self.diagram, r"at=\(2,9\), name=outside,")
        wires = re.findall(r"\\tnwire\[([^]]+)\]\{([^}]+)\}\{([^}]+)\}", self.diagram)
        self.assertEqual(wires, [("name=crossing, species=marked", "inside.0", "outside.180")])
        self.assertIn(r"{on crossing 0.65}{$e$}", self.diagram)
        crossing = [i for i, patch in enumerate(self.patches)
                    if len(self.edge.intersection(patch)) == 1]
        self.assertEqual(crossing, [1])
        self.assertTrue(self.edge.isdisjoint(self.patches[0]))
        self.assertTrue(self.edge.issubset(self.patches[2]))

    def test_boundary_counts_respect_clipping(self):
        edges = {
            frozenset({site, neighbor}) for site in self.domain
            for neighbor in ((site[0] + 1, site[1]), (site[0], site[1] + 1))
            if neighbor in self.domain
        }
        for radius, patch in zip((4, 6, 8), self.patches):
            count = sum(len(edge.intersection(patch)) == 1 for edge in edges)
            self.assertEqual(count, 3)
            self.assertLessEqual(count, 8 * radius + 4)
            self.assertLessEqual(count, 16 * 4 + 4)


if __name__ == "__main__":
    unittest.main()
