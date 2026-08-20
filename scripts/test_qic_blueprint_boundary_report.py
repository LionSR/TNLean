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
See Equation~\eqref{eq:qic}.
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
        self.assertEqual(report["reference_edge_counts"], {"tn_to_qic": 1})
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
        with self.assertRaisesRegex(ValueError, "duplicate item_id"):
            read_disposition_ledger(self.ledger)

        self.write_ledger(
            [("rem:manual", "src/chapter/ch01.tex", "remark", "other", "reason")]
        )
        with self.assertRaisesRegex(ValueError, "disposition must be qic or tn"):
            read_disposition_ledger(self.ledger)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_unlabelled_item_requires_source_line_disposition(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{remark}
Body.
\end{remark}
"""
        )
        identifier = "@src/chapter/ch01.tex:1"
        with self.assertRaisesRegex(ValueError, f"missing manual disposition for {identifier}"):
            boundary_report(self.root)
        self.write_ledger(
            [(identifier, "src/chapter/ch01.tex", "remark", "tn", "tensor-network remark")]
        )
        report = boundary_report(self.root)
        self.assertEqual(report["environment_count"], 1)
        self.assertEqual(report["unlabelled_environment_count"], 1)
        self.assertEqual(report["item_counts"], {"tn": 1})
        self.assertEqual(report["items"][0]["label"], identifier)

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
        selected_tex = [
            path.removeprefix("blueprint/")
            for path in first["blueprint_files"]
            if path.startswith("blueprint/src/")
        ]
        self.assertEqual(
            blueprint_file_manifest(self.root, selected_tex), first["blueprint_files"]
        )
        self.assertEqual(
            tn_interface_labels(first["uses_edges"]), first["tn_interface_labels"]
        )

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_referenced_non_item_label_selects_file_without_router_downward_closure(
        self, _source_sha
    ) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
See Chapter~\ref{ch:aux}.
\end{theorem}
"""
        )
        self.write_blueprint(
            r"""\chapter{Auxiliary}\label{ch:aux}

\input{chapter/tn_only}
""",
            "router.tex",
        )
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
\end{theorem}
""",
            "tn_only.tex",
        )
        (self.root / "blueprint" / "src" / "content.tex").write_text(
            "\\input{chapter/ch01}\n\\input{chapter/router}\n"
        )
        report = boundary_report(self.root)
        self.assertEqual(report["simulated_output_errors"], [])
        self.assertIn("blueprint/src/chapter/router.tex", report["blueprint_files"])
        self.assertNotIn("blueprint/src/chapter/tn_only.tex", report["blueprint_files"])
        self.assertEqual(report["qic_to_tn_reference_edges"], [])

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_tn_non_item_prose_extends_interface_and_unknown_item_ref_is_reported(
        self, _source_sha
    ) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

The staying discussion uses Theorem~\ref{thm:qic}.

\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
See Theorem~\ref{missing:label}.
\end{theorem}
"""
        )
        report = boundary_report(self.root)
        self.assertIn("thm:qic", report["tn_interface_labels"])
        self.assertTrue(
            any("unknown reference missing:label" in error for error in report["simulated_output_errors"])
        )
        self.assertEqual(report["reference_edge_counts"].get("unclassified"), 1)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_nested_non_item_environment_is_atomic_across_comments_and_blanks(
        self, _source_sha
    ) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

\begin{figure}
Opening material.
\begin{center}
% explanatory comment

See Theorem~\ref{thm:tn}.
\end{center}
\label{fig:atomic}
\end{figure}

\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
\end{theorem}
"""
        )
        report = boundary_report(self.root)
        blocks = [
            block
            for block in report["non_item_blocks"]
            if block["file"] == "src/chapter/ch01.tex"
        ]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0]["line"], 5)
        self.assertEqual(blocks[0]["end_line"], 13)
        self.assertEqual(blocks[0]["labels"], ["fig:atomic"])
        self.assertEqual(blocks[0]["references"], ["thm:tn"])
        self.assertEqual(blocks[0]["disposition"], "tn")

    def test_rejects_non_item_environment_containing_item(self) -> None:
        self.write_blueprint(
            r"""\begin{figure}
\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
\end{figure}
"""
        )
        with self.assertRaisesRegex(
            ValueError,
            r"environment at src/chapter/ch01.tex:1-5 contains theorem-like item lines",
        ):
            boundary_report(self.root)

    def test_rejects_wrapper_spanning_two_fully_covered_items(self) -> None:
        self.write_blueprint(
            r"""\begin{samepage}\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
\begin{theorem}\label{thm:tn}
\lean{MPSTensor.staying}
\end{theorem}\end{samepage}
"""
        )
        with self.assertRaisesRegex(
            ValueError,
            r"environment at src/chapter/ch01.tex:1-6 contains theorem-like item lines",
        ):
            boundary_report(self.root)

    def test_rejects_standalone_input_inside_atomic_environment(self) -> None:
        self.write_blueprint(
            r"""\begin{figure}
\input{chapter/picture}
\end{figure}
"""
        )
        self.write_blueprint("Picture body.\n", "picture.tex")
        with self.assertRaisesRegex(
            ValueError,
            r"atomic environment at src/chapter/ch01.tex:1-3 contains "
            r"standalone \\input at line 2",
        ):
            boundary_report(self.root)

    def test_rejects_standalone_input_inside_theorem_item(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\input{chapter/picture}
\end{theorem}
"""
        )
        self.write_blueprint("Picture body.\n", "picture.tex")
        with self.assertRaisesRegex(
            ValueError,
            r"theorem-like item at src/chapter/ch01.tex:1-4 contains "
            r"standalone \\input at line 3",
        ):
            boundary_report(self.root)

    def test_rejects_unbalanced_non_item_environment(self) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

\begin{figure}
Body.
"""
        )
        with self.assertRaisesRegex(
            ValueError,
            r"unterminated environment figure opened at src/chapter/ch01.tex:5",
        ):
            boundary_report(self.root)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_unknown_non_item_reference_is_reported(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

This paragraph cites Theorem~\ref{missing:label}.
"""
        )
        report = boundary_report(self.root)
        self.assertTrue(
            any(
                "prose @src/chapter/ch01.tex:5-5 has unknown reference missing:label"
                in error
                for error in report["simulated_output_errors"]
            )
        )

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_top_level_leaf_prose_is_shared_and_recorded(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}
"""
        )
        self.write_blueprint("Shared introduction.\n", "intro.tex")
        (self.root / "blueprint" / "src" / "content.tex").write_text(
            "\\input{chapter/intro}\n\\input{chapter/ch01}\n"
        )
        report = boundary_report(self.root)
        intro = next(
            block
            for block in report["non_item_blocks"]
            if block["file"] == "src/chapter/intro.tex"
        )
        self.assertEqual(intro["disposition"], "shared")
        self.assertIn(
            "src/chapter/intro.tex", report["simulated_qic_source_files"]
        )
        self.assertIn(
            "src/chapter/intro.tex", report["simulated_tn_source_files"]
        )

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_inline_environment_remains_in_surrounding_paragraph(
        self, _source_sha
    ) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

The sentence begins on this line,
contains $J=\bigl(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\bigr)$ here,
and ends on this line.
"""
        )
        report = boundary_report(self.root)
        blocks = [
            block
            for block in report["non_item_blocks"]
            if block["file"] == "src/chapter/ch01.tex"
        ]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0]["line"], 5)
        self.assertEqual(blocks[0]["end_line"], 7)

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_non_item_environment_is_atomic_across_blank_and_comment_lines(
        self, _source_sha
    ) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
\end{theorem}

\begin{figure}
\begin{center}
QIC picture.

% explanatory comment
\end{center}
\caption{See Theorem~\ref{thm:qic}.}
\end{figure}
"""
        )
        report = boundary_report(self.root)
        figure_blocks = [
            block
            for block in report["non_item_blocks"]
            if block["file"] == "src/chapter/ch01.tex"
            and block["line"] == 5
        ]
        self.assertEqual(len(figure_blocks), 1)
        self.assertEqual(figure_blocks[0]["end_line"], 12)
        self.assertEqual(figure_blocks[0]["disposition"], "qic")
        self.assertEqual(report["simulated_output_errors"], [])

    @patch("qic_blueprint_boundary_report.source_sha", return_value="a" * 40)
    def test_percent_continued_reference_payload_is_normalized(self, _source_sha) -> None:
        self.write_blueprint(
            r"""\begin{theorem}\label{thm:qic}
\lean{Kraus.moved}
See Theorem~\ref{thm:%
  target}.
\end{theorem}
\begin{theorem}\label{thm:target}
\lean{Kraus.moved}
\end{theorem}
"""
        )
        report = boundary_report(self.root)
        self.assertEqual(report["simulated_output_errors"], [])
        self.assertEqual(
            [(edge["source"], edge["target"]) for edge in report["reference_edges"]],
            [("thm:qic", "thm:target")],
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
