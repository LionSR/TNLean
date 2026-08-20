#!/usr/bin/env python3
"""Tests for the deterministic QIC blueprint boundary report."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from qic_blueprint_boundary_report import boundary_report, environment_uses


class QICBlueprintBoundaryReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        (self.root / "scripts").mkdir()
        (self.root / "scripts" / "qic_layer0_modules.txt").write_text("")
        (self.root / "TNLean" / "Channel").mkdir(parents=True)
        (self.root / "TNLean" / "MPS").mkdir(parents=True)
        (self.root / "TNLean" / "Channel" / "A.lean").write_text(
            "namespace Kraus\n\ntheorem moved : True := by trivial\n\nend Kraus\n"
        )
        (self.root / "TNLean" / "MPS" / "B.lean").write_text(
            "namespace MPSTensor\n\ntheorem staying : True := by trivial\n\nend MPSTensor\n"
        )
        (self.root / "blueprint" / "src" / "chapter").mkdir(parents=True)
        (self.root / "blueprint" / "src" / "appendix").mkdir(parents=True)

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def write_blueprint(self, text: str) -> None:
        (self.root / "blueprint" / "src" / "chapter" / "ch01.tex").write_text(text)

    def test_environment_uses_parses_multiline_payload(self) -> None:
        self.write_blueprint(
            """\\begin{theorem}\\label{thm:a}
\\uses{thm:b,
  % explanation
  thm:c}
Body.
\\end{theorem}
"""
        )
        self.assertEqual(
            environment_uses(self.root / "blueprint" / "src"),
            [
                {
                    "environment": "theorem",
                    "file": "src/chapter/ch01.tex",
                    "line": 1,
                    "label": "thm:a",
                    "uses": ["thm:b", "thm:c"],
                }
            ],
        )

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_classifies_items_and_cross_boundary_edges(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}
\label{thm:qic}
\lean{Kraus.moved}
\uses{thm:tn}
\end{theorem}
\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
\uses{thm:qic}
\end{theorem}
\begin{theorem}\label{thm:mixed}
\lean{Kraus.moved, MPSTensor.staying}
\end{theorem}
\begin{theorem}\label{thm:missing}
\lean{Unknown.name}
\end{theorem}
"""
        )
        report = boundary_report(self.root)
        second_report = boundary_report(self.root)
        self.assertEqual(report, second_report)
        self.assertEqual(report["source_sha"], "a" * 40)
        self.assertEqual(report["mover_path_count"], 1)
        self.assertEqual(
            report["item_counts"],
            {"mixed": 1, "qic": 1, "tn": 1, "unresolved": 1},
        )
        self.assertEqual(report["edge_counts"], {"qic_to_tn": 1, "tn_to_qic": 1})
        self.assertEqual(
            [(edge["source"], edge["target"]) for edge in report["qic_to_tn_uses_edges"]],
            [("thm:qic", "thm:tn")],
        )
        self.assertEqual(
            [(edge["source"], edge["target"]) for edge in report["tn_to_qic_interface_edges"]],
            [("thm:tn", "thm:qic")],
        )
        self.assertEqual(json.dumps(report, sort_keys=True), json.dumps(second_report, sort_keys=True))


if __name__ == "__main__":
    unittest.main()
