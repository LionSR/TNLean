#!/usr/bin/env python3
"""Render and check native orientation and invariant-closure diagrams."""

from __future__ import annotations

import re
import tempfile
from pathlib import Path

from tenkz_blueprint_sweep import scan_units
import tenkz_pic

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter"
CHAPTER = SOURCE / "ch24_peps_native_semiregular_parent.tex"
# Each anchor identifies the original chapter-owned display. The tuple is
# (open virtual legs, open physical legs), before its written boundary sum.
EXPECTED = {"nativeSite": [(4, 1)], "nativePlaquette11": [(8, 4)]}


def main() -> int:
    units = scan_units(SOURCE)
    panels = 0
    with tempfile.TemporaryDirectory(prefix="tenkz_peps_native_semiregular_") as tmp:
        for anchor, expected in EXPECTED.items():
            matches = [u for u in units if f"name={anchor}," in u.source]
            assert len(matches) == 1, (anchor, len(matches))
            unit = matches[0]
            assert unit.path.resolve() == CHAPTER.resolve(), (anchor, unit.path)
            assert unit.display, (anchor, "audit the complete source display")
            log = tenkz_pic.unit_event_log(unit.source, Path(tmp))
            assert log is not None, (anchor, "rendering unavailable")
            events = log.read_text(encoding="utf-8")
            signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
            actual = [
                (len(re.findall(r"\bopen:", s)), len(re.findall(r"\bphys:", s)))
                for s in signatures
            ]
            assert actual == expected, (anchor, actual, expected)
            assert "kernel-error|" not in events, (anchor, "kernel error")
            wires = [line for line in events.splitlines() if line.startswith("wire|")]
            if anchor == "nativeSite":
                # Head incidences enter at top and left; native tails leave
                # at right and down. The physical coefficient remains open.
                assert set(signatures[0].split(", ")) == {
                    "open:e:to", "open:n:from", "open:s:to", "open:w:from", "phys:n"
                }, (anchor, signatures)
                assert sum("|dir=from|" in line for line in wires) == 2
                assert sum("|dir=to|" in line for line in wires) == 2
                assert sum("|origin=policy-leg|" in line for line in wires) == 1
                assert not any("|origin=grid|" in line for line in wires)
                for leg in ("t", "r", "b", "l"):
                    assert f"{{$\\eta_{leg}$}}" in unit.source
                assert "U_g\\otimes U_{g^{-1}}^T" in CHAPTER.read_text(encoding="utf-8")
            else:
                # The open 2x2 region has four internal identity bonds,
                # eight unrestricted boundary labels, and four physical legs.
                assert sum("|origin=grid|" in line for line in wires) == 4
                assert sum("|origin=policy-leg|" in line for line in wires) == 4
                assert sum("|origin=port-open|" in line for line in wires) == 8
                for side in ("l", "r", "t", "b"):
                    for index in range(2):
                        assert f":$\\theta_{{{side},{index}}}$" in unit.source
                assert r"\sum_\theta c_\tau(\theta)" in unit.source
            panels += len(actual)
    print(f"PASS: {len(EXPECTED)} source displays render with {panels} exact typed boundaries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
