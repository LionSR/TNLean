#!/usr/bin/env python3
"""Contract tests for the shrink-gate meters, detectors, and gate rule."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/tenkz_shrink.py"

sys.path.insert(0, str(ROOT / "scripts"))
from tenkz_language import parse_status  # noqa: E402
import tenkz_shrink  # noqa: E402


def test_parse_status_ledgers() -> None:
    assert parse_status("kernel") == ("kernel", "")
    assert parse_status("escape") == ("escape", "")
    assert parse_status("sugar(rows={ket,op,bra})")[0] == "sugar"
    assert parse_status("alias(span; sunset=1.0)") == ("alias", "span; sunset=1.0")
    try:
        parse_status("canonical")
    except ValueError:
        pass
    else:
        raise AssertionError("legacy status word accepted")


def test_meters_shape() -> None:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "meters"], capture_output=True, text=True, check=True
    )
    data = json.loads(result.stdout)
    expected = {
        "m1_census",
        "m2_parser_paths",
        "m3_escape_usage",
        "m4_lines_per_case",
        "m5_aliases",
        "m6_overloads",
    }
    assert set(data) == expected, sorted(data)
    assert sum(data["m1_census"]["value"].values()) == 95
    for meter in data.values():
        assert meter["definition"]


def test_baseline_matches_actuals() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "meters"], capture_output=True, text=True, check=True
    )
    assert json.loads(result.stdout) == baseline


def test_gate_requires_verdicts() -> None:
    section = tenkz_shrink.latest_session_section(
        (ROOT / "docs/tenkz/SHRINK.md").read_text()
    )
    entries = tenkz_shrink.load_registry()
    corpus = tenkz_shrink.consumer_files()
    for flag in tenkz_shrink.flags(entries, corpus):
        assert flag["id"] in section, f"no Session-0 verdict for {flag['id']}"


def test_gate_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "gate"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
