#!/usr/bin/env python3
"""Render and check regular PEPS parent and intersection diagrams."""

from __future__ import annotations

import re
import tempfile
from pathlib import Path

from tenkz_blueprint_sweep import scan_units
import tenkz_pic

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter"
# The first named atom identifies the chapter-owned equation, not a copy of it.
# Each tuple is (virtual open legs, physical open legs), in panel order.
EXPECTED = {
    "parentInverse0": [(1, 1), (1, 1), (1, 1)],
    "parentFlat0": [(0, 1), (0, 1)],
    "flatGauge0": [(2, 0), (2, 0)],
    "parentSeam": [(12, 9)],
    "intersectionCore0": [(8, 3)],
}


def main() -> int:
    units = scan_units(SOURCE)
    panels = 0
    with tempfile.TemporaryDirectory(prefix="tenkz_peps_parent_spanning_") as tmp:
        for anchor, expected in EXPECTED.items():
            matches = [u for u in units if f"name={anchor}," in u.source]
            assert len(matches) == 1, (anchor, len(matches))
            unit = matches[0]
            assert unit.display, (anchor, "equation must be audited together")
            log = tenkz_pic.unit_event_log(unit.source, Path(tmp))
            assert log is not None, (anchor, "rendering unavailable")
            source = log.read_text(encoding="utf-8")
            signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", source, re.M)
            actual = [
                (len(re.findall(r"\bopen:", s)), len(re.findall(r"\bphys:", s)))
                for s in signatures
            ]
            assert actual == expected, (anchor, actual, expected)
            assert "kernel-error|" not in source, (anchor, "kernel error")
            if anchor == "parentSeam":
                # Twelve nearest-neighbour bonds of the cut 3x3 square.
                wires = [line for line in source.splitlines()
                         if line.startswith("wire|")]
                assert sum("|origin=grid|" in line for line in wires) == 12
                assert sum("|origin=policy-leg|" in line for line in wires) == 9
                for prefix in (r"\ell_", "r_", "b_", "t_"):
                    for index in range(3):
                        assert f":${prefix}{index}$" in unit.source
                chapter = unit.path.read_text(encoding="utf-8")
                assert r"L_h(\ell_y,r_y)" in chapter
                assert r"L_{g^{-1}}(b_x,t_x)" in chapter
                assert r"\sum_{\ell,r,b,t\in G^3}" in unit.source
            panels += len(actual)
    print(f"PASS: {len(EXPECTED)} source equations render with {panels} exact typed boundaries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
