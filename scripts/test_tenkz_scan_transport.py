#!/usr/bin/env python3
"""Check the source contract of the recursive scan transport schematic.

The standard tenkz sweep owns rendering, measured label separation, and event
checks. These source tests check the actual grafting incidence and scope; they
do not substitute for rendered validation.
"""
from pathlib import Path
import re
import unittest

from tenkz_blueprint_sweep import scan_units

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch24_peps_area_law_scan_transport_diagram.tex"


def atoms(picture):
    """Read one explicitly placed box per line, including its full math label."""
    found = re.findall(
        r"\\tn\[at=\((\d+),(\d+)\), name=(\w+), skin=box\]\{(.*)\}$",
        picture, re.M,
    )
    return {name: ((int(row), int(col)), label) for row, col, name, label in found}


def wire_ends(picture):
    """Read native relative endpoints without dropping their offset directions."""
    return re.findall(
        r"\\tnwire\[kind=string, stroke=dotted, dir=to, name=\w+\]"
        r"\{0\.5 (n) of (\w+)\}\{0\.5 (sw|se) of (\w+)\}", picture,
    )


def wires(picture):
    return [(start, end) for _, start, _, end in wire_ends(picture)]


class ScanTransportDiagram(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = SOURCE.read_text(encoding="utf-8")
        cls.pictures = re.findall(
            r"\\begin\{tenkz\}.*?\\end\{tenkz\}", cls.text, re.S,
        )

    def test_four_native_panels_in_two_audited_rows(self):
        self.assertEqual(len(self.pictures), 4)
        units = [unit for unit in scan_units(SOURCE.parent) if unit.path == SOURCE]
        self.assertEqual(len(units), 2)
        self.assertTrue(all(unit.display for unit in units))
        self.assertTrue(all(unit.source.count(r"\begin{tenkz}") == 2 for unit in units))
        for forbidden in (
            r"\includegraphics", r"\begin{tikzpicture}", r"\draw", r"\node",
            "check=none", "audit=off", "bbox=", r"\resizebox", r"\scalebox",
        ):
            self.assertNotIn(forbidden, self.text)

    def test_no_contraction_or_open_boundary_is_claimed(self):
        for picture in self.pictures:
            compact = re.sub(r"\s+", "", picture)
            self.assertIn("bonds=none,west=none,east=none", compact)
            self.assertNotIn("ports=", picture)
            self.assertEqual(picture.count(r"\tnwire"), len(wires(picture)))
            self.assertEqual(picture.count(r"\tn["), len(atoms(picture)))
            for start, end in wires(picture):
                self.assertIn(start, atoms(picture))
                self.assertIn(end, atoms(picture))
                self.assertGreater(atoms(picture)[start][0][0], atoms(picture)[end][0][0])

    def test_fill_preserves_tree_and_changes_only_terminal_metrics(self):
        for panel, prefix, labels in (
            (0, "fillOld", ["A_0", "A_1"]),
            (1, "fillNew", [r"\widetilde A_0", r"\widetilde A_1"]),
            (2, "chargeOld", [r"\widetilde A_0", r"\widetilde A_1"]),
        ):
            self.assertEqual(atoms(self.pictures[panel]), {
                prefix + "Root": ((1, 2), "T_k"),
                prefix + "Zero": ((3, 1), labels[0]),
                prefix + "One": ((3, 3), labels[1]),
            })
            self.assertEqual(wires(self.pictures[panel]), [
                (prefix + "Zero", prefix + "Root"),
                (prefix + "One", prefix + "Root"),
            ])

    def test_charge_grafts_the_same_choice_tree_at_both_histories(self):
        self.assertEqual(atoms(self.pictures[3]), {
            "chargeNewRoot": ((1, 4), "T_k"),
            "chargeNewChoiceZero": ((3, 2), "C"),
            "chargeNewChoiceOne": ((3, 6), "C"),
            "chargeNewZeroZero": ((5, 1), "A_{00}"),
            "chargeNewZeroOne": ((5, 3), "A_{01}"),
            "chargeNewOneZero": ((5, 5), "A_{10}"),
            "chargeNewOneOne": ((5, 7), "A_{11}"),
        })
        self.assertEqual(wires(self.pictures[3]), [
            ("chargeNewChoiceZero", "chargeNewRoot"),
            ("chargeNewChoiceOne", "chargeNewRoot"),
            ("chargeNewZeroZero", "chargeNewChoiceZero"),
            ("chargeNewZeroOne", "chargeNewChoiceZero"),
            ("chargeNewOneZero", "chargeNewChoiceOne"),
            ("chargeNewOneOne", "chargeNewChoiceOne"),
        ])

    def test_grid_reserves_space_for_labels(self):
        # This is only a coordinate-spacing contract, not a pixel-overlap test.
        for picture in self.pictures:
            positions = [pos for pos, _ in atoms(picture).values()]
            for i, (row, col) in enumerate(positions):
                for other_row, other_col in positions[i + 1:]:
                    self.assertGreaterEqual(max(abs(row - other_row), abs(col - other_col)), 2)
            self.assertNotIn(r"\tnmark", picture)

    def test_strings_have_separate_tips_outside_each_root(self):
        # tenkz's crossing police counts shared bare-center endpoints as an
        # undeclared string crossing, even when a box later hides the meeting.
        # Face addresses on these cell-backed boxes still resolve to the cell
        # center. Relative addresses are needed to separate the incoming tips.
        for picture in self.pictures:
            nodes = atoms(picture)
            tips = []
            for start_dir, start, end_dir, end in wire_ends(picture):
                self.assertEqual(start_dir, "n")
                side = "sw" if nodes[start][0][1] < nodes[end][0][1] else "se"
                self.assertEqual(end_dir, side)
                tips.extend(((start, start_dir), (end, end_dir)))
            self.assertEqual(len(tips), len(set(tips)))
            self.assertNotIn("cross=", picture)

    def test_scope_and_exact_history_relabeling(self):
        compact = re.sub(r"\s+", " ", self.text)
        for phrase in (
            "Schematic of the recursive scan trees",
            "Dotted arrows abbreviate whole evaluation paths",
            "only two histories and two choices per history are shown",
            "same fixed choice tree at every history leaf",
            r"relabels $(h,c)$ by $h\frown c$, giving $T_{k+1}$",
            "No reassociation or replacement by an independent uniform average",
            r"T_k\bigl[{C[A_{h\frown c}]}\bigr] =T_{k+1}[A_{h\frown c}]",
            r"Theorem~\ref{thm:al_scan_history_mean_tree_endpoints}",
        ):
            self.assertIn(phrase, compact)

    def test_proof_status_is_not_promoted(self):
        live = "\n".join(line for line in self.text.splitlines() if not line.lstrip().startswith("%"))
        self.assertNotIn(r"\lean{", live)
        self.assertNotIn(r"\leanok", live)
        self.assertNotIn("kernel-pending", live)
        self.assertIn("kernel-pending", self.text)
        self.assertIn("actualFillData_rootPath_one_eq_charge_zero", self.text)
        self.assertIn("charge_rootPath_one_eq_actualFillData_zero", self.text)
        self.assertIn("extendHistory h c", self.text)


if __name__ == "__main__":
    unittest.main()
