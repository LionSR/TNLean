#!/usr/bin/env python3
"""Contract tests for the shrink-gate meters, detectors, and gate rule."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/tenkz_shrink.py"

sys.path.insert(0, str(ROOT / "scripts"))
from tenkz_language import Entry, check, parse_alias_payload, parse_status  # noqa: E402
from tenkz_lint import registry_alias_patterns  # noqa: E402
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


def test_alias_sunset_validation() -> None:
    assert parse_alias_payload("frame; sunset=1.0") == ("frame", "1.0")
    for payload in ("frame; sunset=", "frame; sunset=1", "frame; sunset=1.1"):
        try:
            parse_alias_payload(payload)
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid alias sunset accepted: {payload}")


def test_alias_records_include_values_and_normalize_ids() -> None:
    records = tenkz_shrink.alias_records(
        [
            Entry(
                "key",
                (
                    "picture",
                    "chain~axis",
                    "enum(east|south)",
                    "east",
                    "alias(frame; sunset=1.0)",
                    "Legacy frame spelling.",
                ),
            ),
            Entry(
                "alias",
                (
                    "connection",
                    "route=curve",
                    "route=arc",
                    "Legacy curved route. Sunset 1.0.",
                ),
            ),
        ]
    )
    assert records == [
        ("picture", "chain axis", "1.0"),
        ("connection", "route=curve", "1.0"),
    ]


def test_sugar_expansion_checks_every_token() -> None:
    entries = tenkz_shrink.load_registry()
    changed = [
        Entry(
            entry.kind,
            (*entry.fields[:4], "sugar(rows=, completely bogus=)", entry.fields[5]),
        )
        if entry.kind == "key"
        and entry.fields[0] == "picture"
        and entry.fields[1] == "physical"
        else entry
        for entry in entries
    ]
    errors = check(changed)
    assert any(
        "picture:physical expansion names non-kernel token(s): completely bogus"
        in error
        for error in errors
    ), errors


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
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    assert set(data["m1_census"]["value"]) == {
        "kernel",
        "sugar",
        "alias",
        "escape",
        "commands",
        "environments",
    }
    assert sum(data["m1_census"]["value"].values()) == sum(
        baseline["m1_census"]["value"].values()
    )
    for meter in data.values():
        assert meter["definition"]


def test_manifest_freezes_case_denominator() -> None:
    cases = tenkz_shrink.manifest_case_paths()
    assert len(cases) == 130
    assert len(set(cases)) == 130


def test_rmp_alias_patterns_use_only_alias_ledgers() -> None:
    patterns = registry_alias_patterns()
    canonical = "dot, route=arc, out=90, in=0, label=x"
    assert not any(pattern.search(canonical) for pattern in patterns)
    assert any(pattern.search("chain axis=east") for pattern in patterns)
    assert any(pattern.search("route=curve") for pattern in patterns)


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
    verdicts = tenkz_shrink.session_verdict_ids(section)
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    branch, failures = tenkz_shrink.evaluate_gate(
        entries,
        corpus,
        baseline,
        copy.deepcopy(baseline),
        verdicts,
        has_extension=False,
    )
    assert branch == "verdicts"
    assert not failures, failures


def test_gate_accepts_a_decreased_census_without_verdicts() -> None:
    entries = tenkz_shrink.load_registry()
    corpus = tenkz_shrink.consumer_files()
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    previous = copy.deepcopy(baseline)
    previous["m1_census"]["value"]["kernel"] += 1
    branch, failures = tenkz_shrink.evaluate_gate(
        entries,
        corpus,
        baseline,
        previous,
        set(),
        has_extension=False,
    )
    assert branch == "decreased"
    assert not failures


def test_prechange_ratchet_requires_extension_citation() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    current = copy.deepcopy(baseline)
    previous = copy.deepcopy(baseline)
    current["m2_parser_paths"]["value"] += 1
    errors = tenkz_shrink.ratchet_errors(
        current, previous, has_extension=False
    )
    assert errors == [
        "M2 parser paths increased without an Extension-gate: #NNNN citation"
    ]
    assert not tenkz_shrink.ratchet_errors(
        current, previous, has_extension=True
    )


def test_verdict_parser_requires_an_exact_table_row() -> None:
    section = """Agenda mentions flag:consumers:key:picture:open.

| flag | verdict |
|---|---|
| flag:consumers:key:picture:open-ended | keep; expiry 0.9 |
"""
    assert tenkz_shrink.session_verdict_ids(section) == {
        "flag:consumers:key:picture:open-ended"
    }


def test_gate_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "gate"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
