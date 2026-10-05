#!/usr/bin/env python3
"""Render and check the source-linked SCP10 invariant-boundary diagrams."""

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
    "rangeProjector": [(1, 1), (1, 1)],
    "cutLeft": [(0, 2), (0, 2)],
    "cutCoefficient": [(1, 1), (1, 1)],
    "multiplicityImage": [(4, 0), (4, 0)],
    "symmetricSite": [(4, 1), (4, 1)],
    "stripAthree": [(0, 3), (0, 3), (0, 3)],
}


def main() -> int:
    units = scan_units(SOURCE)
    panels = 0
    with tempfile.TemporaryDirectory(prefix="tenkz_peps_groundstate_") as tmp:
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
            panels += len(actual)
    print(f"PASS: {len(EXPECTED)} source equations render with {panels} exact typed boundaries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
