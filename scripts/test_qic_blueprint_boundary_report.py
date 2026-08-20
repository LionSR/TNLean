#!/usr/bin/env python3
"""Tests for the deterministic QIC blueprint boundary report."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from qic_blueprint_boundary_report import (
    LEDGER_COLUMNS,
    blueprint_file_manifest,
    boundary_report,
    environment_uses,
    normalized_relative_path,
    read_disposition_ledger,
    tn_interface_labels,
)


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
        self.ledger = self.root / "scripts" / "qic_blueprint_label_dispositions.csv"
        self.write_ledger([])

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def write_blueprint(self, text: str, name: str = "ch01.tex") -> None:
        (self.root / "blueprint" / "src" / "chapter" / name).write_text(text)

    def write_ledger(self, rows: list[tuple[str, str, str, str, str]]) -> None:
        lines = [",".join(LEDGER_COLUMNS)]
        lines.extend(",".join(row) for row in rows)
        self.ledger.write_text("\n".join(lines) + "\n")

    def test_normalized_relative_path_accepts_windows_separators(self) -> None:
        self.assertEqual(
            normalized_relative_path(r"TNLean\Channel\Basic.lean"),
            "TNLean/Channel/Basic.lean",
        )

    def test_environment_uses_parses_all_labels_and_multiline_payload(self) -> None:
        self.write_blueprint(
            """\\begin{theorem}\\label{thm:a}
\\label{eq:a}
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
                    "labels": ["thm:a", "eq:a"],
                    "uses": ["thm:b", "thm:c"],
                }
            ],
        )

    def test_environment_uses_attaches_intervening_labels_and_proof_dependencies(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:a}
Body.
\end{theorem}
\begin{figure}
\label{fig:a}
\end{figure}
\begin{proof}\leanok
\uses{thm:b, thm:c}
Proof.
\end{proof}
\begin{theorem}\label{thm:d}
\uses{thm:e}
\end{theorem}
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
                    "labels": ["thm:a", "fig:a"],
                    "uses": ["thm:b", "thm:c"],
                },
                {
                    "environment": "theorem",
                    "file": "src/chapter/ch01.tex",
                    "line": 11,
                    "label": "thm:d",
                    "labels": ["thm:d"],
                    "uses": ["thm:e"],
                },
            ],
        )

    def test_proof_stops_at_next_statement_and_deduplicates_dependencies(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:a}
\uses{thm:x}
\end{theorem}
\begin{theorem}\label{thm:b}
\uses{thm:y}
\end{theorem}
\begin{proof}
\uses{thm:y, thm:z}
\end{proof}
"""
        )
        records = environment_uses(self.root / "blueprint" / "src")
        self.assertEqual(records[0]["uses"], ["thm:x"])
        self.assertEqual(records[1]["uses"], ["thm:y", "thm:z"])

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_proof_lean_tag_does_not_change_statement_ownership(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
\begin{proof}
\lean{MPSTensor.staying}
\end{proof}
"""
        )
        report = boundary_report(self.root)
        self.assertEqual(report["item_counts"], {"qic": 1})
        self.assertEqual(report["items"][0]["declarations"], ["Kraus.moved"])

    def test_rejects_unterminated_attached_proof(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:a}
\end{theorem}
\begin{proof}
Proof.
"""
        )
        with self.assertRaisesRegex(ValueError, "unterminated proof"):
            environment_uses(self.root / "blueprint" / "src")

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_manual_rows_and_secondary_label_resolution(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\label{eq:qic}
\lean{Kraus.moved}
\end{theorem}
\begin{remark}\label{rem:tn}
Body.
\end{remark}
\begin{proof}
\uses{eq:qic}
Proof.
\end{proof}
"""
        )
        self.write_ledger(
            [
                (
                    "rem:tn",
                    "src/chapter/ch01.tex",
                    "remark",
                    "tn",
                    "tensor-network statement",
                )
            ]
        )
        report = boundary_report(self.root)
        self.assertEqual(report["item_counts"], {"qic": 1, "tn": 1})
        self.assertEqual(report["edge_counts"], {"tn_to_qic": 1})
        self.assertEqual(report["tn_interface_labels"], ["eq:qic"])
        qic_item = next(item for item in report["items"] if item["label"] == "thm:qic")
        self.assertEqual(qic_item["labels"], ["thm:qic", "eq:qic"])
        self.assertEqual(qic_item["disposition_source"], "lean")
        tn_item = next(item for item in report["items"] if item["label"] == "rem:tn")
        self.assertEqual(tn_item["disposition_source"], "manual")

    def test_manual_ledger_validation_failures(self) -> None:
        self.write_blueprint(
            r"""\begin{remark}\label{rem:manual}
Body.
\end{remark}
"""
        )
        cases = {
            "missing": [],
            "wrong source": [
                ("rem:manual", "src/chapter/other.tex", "remark", "tn", "reason")
            ],
            "wrong environment": [
                ("rem:manual", "src/chapter/ch01.tex", "theorem", "tn", "reason")
            ],
            "stale": [
                ("rem:manual", "src/chapter/ch01.tex", "remark", "tn", "reason"),
                ("rem:stale", "src/chapter/ch01.tex", "remark", "tn", "reason"),
            ],
        }
        for name, rows in cases.items():
            with self.subTest(name=name):
                self.write_ledger(rows)
                with self.assertRaises(ValueError):
                    boundary_report(self.root)

        self.ledger.write_text(
            ",".join(LEDGER_COLUMNS)
            + "\nrem:manual,src/chapter/ch01.tex,remark,tn,reason\n"
            + "rem:manual,src/chapter/ch01.tex,remark,tn,reason\n"
        )
        with self.assertRaisesRegex(ValueError, "duplicate label"):
            read_disposition_ledger(self.ledger)

        self.write_ledger(
            [("rem:manual", "src/chapter/ch01.tex", "remark", "other", "reason")]
        )
        with self.assertRaisesRegex(ValueError, "disposition must be qic or tn"):
            read_disposition_ledger(self.ledger)

    def test_rejects_duplicate_label_within_one_environment(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
"""
        )
        with self.assertRaisesRegex(ValueError, "duplicate blueprint label"):
            boundary_report(self.root)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_external_ledger_path_is_reported(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
"""
        )
        with tempfile.TemporaryDirectory() as directory:
            external = Path(directory) / "dispositions.csv"
            external.write_text(",".join(LEDGER_COLUMNS) + "\n")
            report = boundary_report(self.root, external)
        self.assertEqual(report["disposition_ledger"], external.as_posix())

    def test_rejects_manual_row_for_tagged_item(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
"""
        )
        self.write_ledger(
            [("thm:qic", "src/chapter/ch01.tex", "theorem", "qic", "reason")]
        )
        with self.assertRaisesRegex(ValueError, "tagged item"):
            boundary_report(self.root)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_mixed_physical_files_and_deterministic_artifacts(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
\uses{thm:qic}
\end{theorem}
"""
        )
        (self.root / "blueprint" / "src" / "content.tex").write_text(
            "\\input{chapter/ch01}\n"
        )
        (self.root / "blueprint" / "src" / "web.tex").write_text(
            "\\input{content}\n"
        )
        (self.root / "blueprint" / "src" / "content_ft_mps.tex").write_text(
            "\\input{chapter/ch01}\n"
        )
        (self.root / "blueprint" / "src" / "print_ft_mps.tex").write_text(
            "\\input{content_ft_mps}\n"
        )
        first = boundary_report(self.root)
        second = boundary_report(self.root)
        self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))
        self.assertEqual(first["mixed_physical_files"], ["src/chapter/ch01.tex"])
        self.assertEqual(
            first["blueprint_files"],
            [
                "blueprint/src/chapter/ch01.tex",
                "blueprint/src/content.tex",
                "blueprint/src/web.tex",
            ],
        )
        self.assertEqual(first["tn_interface_labels"], ["thm:qic"])
        self.assertEqual(
            blueprint_file_manifest(self.root, first["items"]), first["blueprint_files"]
        )
        self.assertEqual(
            tn_interface_labels(first["uses_edges"]), first["tn_interface_labels"]
        )

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_reports_mixed_unresolved_and_cross_boundary_items(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\uses{thm:tn}
\end{theorem}
\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
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
        self.assertEqual(
            report["item_counts"],
            {"mixed": 1, "qic": 1, "tn": 1, "unresolved": 1},
        )
        self.assertEqual(report["edge_counts"], {"qic_to_tn": 1})
        self.assertEqual(
            [(edge["source"], edge["target"]) for edge in report["qic_to_tn_uses_edges"]],
            [("thm:qic", "thm:tn")],
        )


if __name__ == "__main__":
    unittest.main()
