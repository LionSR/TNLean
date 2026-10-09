#!/usr/bin/env python3
"""Check the mathematical source contract of the native ancestry diagram.

The standard blueprint tenkz sweep renders and audits the picture in CI. This
small check fixes its site labels, charge-ball membership, stationary front,
and good-lead threshold; it does not claim to replace a rendered layout check.
"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch24_peps_area_law_bad_histories.tex"


class ScanAncestryDiagram(unittest.TestCase):
    def setUp(self):
        text = SOURCE.read_text()
        self.picture = re.search(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", text, re.S).group()
        self.compact = re.sub(r"\s+", "", self.picture)

    def test_native_site_rows(self):
        labels = re.findall(r"\\tn(?:\[[^\]]*\])?\{(\d+)\}", self.picture)
        self.assertEqual(list(map(int, labels)), list(range(32, 40)) * 3)
        self.assertIn("bonds=none", self.compact)
        self.assertIn("west=none,east=none", self.compact)
        self.assertNotIn("\\tnwire", self.picture)
        self.assertNotIn("ports=", self.picture)

    def test_actual_radius_one_balls(self):
        for row, anchor, first, last in ((1, 34, 2, 4), (2, 36, 4, 6), (3, 38, 6, 8)):
            pattern = (rf"\\tnmark\[[^\]]*name=scanCharge{anchor},[^\]]*\]"
                       rf"\{{\({row},{first}\)\.\.\({row},{last}\)\}}\{{\$B_1\({anchor}\)\$\}}")
            self.assertRegex(self.compact, pattern)
            members = set(range(31 + first, 32 + last))
            self.assertEqual(members, {x for x in range(32, 40) if abs(x - anchor) <= 1})
        self.assertEqual({33, 34, 35} & {35, 36, 37}, {35})
        self.assertEqual({35, 36, 37} & {37, 38, 39}, {37})

    def test_front_threshold_and_bad_endpoint(self):
        for name, depth in (("scanFront", 33), ("scanGoodThreshold", 37), ("scanBadEndpoint", 39)):
            self.assertRegex(self.compact, rf"\\tn\[[^\]]*name={name}\]\{{{depth}\}}")
        self.assertIn(r"{scanFront}{$j=33$}", self.compact)
        self.assertIn(r"{scanGoodThreshold}{$j+D/2$}", self.compact)
        self.assertIn(r"{scanBadEndpoint}{$39>37$}", self.compact)
        self.assertEqual(33 + 8 // 2, 37)
        self.assertGreater(39, 37)


if __name__ == "__main__":
    unittest.main()
