#!/usr/bin/env python3
"""Focused regression tests for the tenkz disposition checker."""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_dispositions as guard


def main() -> int:
    tombstones = (
        r"\begin{tenkzfree}\end{tenkzfree}",
        r"\tnghost{}",
        r"\tnset{tensor style=box}",
        r"\tnset{compact}",
        r"\tnwire[route=hv]{}{}",
        r"\begin{tenkz}[rows={op:none}]\end{tenkz}",
        r"\tnfuse[rows=2]{}",
        r"\tnmark[form=brace-below]{}{}",
        r"\tnspan[brace below]{2}{}",
        r"\tnspan[brace above]{2}{}",
        r"\tn[pill]{}",
        r"\tn[cluster]{}",
        r"\tn[poly=5]{}",
        r"\tnmark{(1,1)-(2,2)}{}",
    )
    for source in tombstones:
        assert guard.uses_tombstone(source), source

    accepted = (
        r"\begin{tenkz}[rows={op}, cols=2]\tn{}\end{tenkz}",
        r"\tn[box]{}",
        r"\tnfuse[span=2]{}",
        r"\tnmark[form=bracket]{}{}",
        r"\tnwire[route=orth]{}{}",
        r"\tnset{species={left,right}}",
    )
    for source in accepted:
        assert not guard.uses_tombstone(source), source
    assert guard.source_target_codes(
        r"\begin{tenkz}[physical=up]\tn[box]{}\end{tenkz}"
    ) == frozenset({"C-policy", "C-record"})
    assert guard.source_target_codes(
        r"\tnset{species={alpha,beta}}"
    ) == frozenset({"C-declare"})
    assert guard.source_target_codes(
        r"\begin{tenkzfree}\tnghost{}\end{tenkzfree}"
        r"\begin{tenkz}[physical=up]\tn{}\end{tenkz}"
    ) == frozenset({"R-free", "R-record", "C-policy"})

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        dependency = root / "dependency.inc"
        dependency.write_text(r"\begin{tenkz}\tncut{}\end{tenkz}")
        fixture = root / "fixture.tex"
        fixture.write_text(r"\input{dependency.inc}")
        expanded = guard.expanded_source(fixture)
        assert r"\tncut" in expanded
        assert guard.uses_tombstone(expanded)

        blueprint = root / "blueprint.tex"
        blueprint.write_text(
            r"\begin{tenkz}\tn{}\tnspan[brace below]{2}{}\end{tenkz}"
        )
        sources = guard.construct_sources(blueprint)
        construct = sources[("blueprint.tex", 1, "tenkz")]
        assert any(guard.uses_tombstone(source) for source in construct)

        cycle = root / "cycle.tex"
        cycle.write_text(r"\input{cycle.tex}")
        try:
            guard.expanded_source(cycle)
        except SystemExit as error:
            assert "recursive fixture input" in str(error)
        else:
            raise AssertionError("recursive input was not rejected")

        spaced = root / "spaced.tex"
        spaced.write_text(r"\begin {tenkz}\tn{}\end {tenkz}")
        assert guard.occurrences(spaced) == [(1, "tenkz")]
        assert ("spaced.tex", 1, "tenkz") in guard.construct_sources(spaced)

    fixture_inventory = guard.documented_fixtures(guard.DOCUMENT.read_text())
    assert len(fixture_inventory) == 264
    assert fixture_inventory["modes_dot_baseline.tex"][0] == "redraw"
    assert fixture_inventory["p_pitch.tex"][0] == "redraw"
    assert fixture_inventory["rev4075_alias.tex"][0] == "redraw"
    assert fixture_inventory["p_species.tex"] == (
        "codemod",
        frozenset({"C-declare"}),
    )
    _, _, blueprint_inventory, _ = guard.documented_blueprint(
        guard.DOCUMENT.read_text()
    )
    assert blueprint_inventory[("ch02_mps.tex", 54, "tenkz")] == "redraw"

    broken_total = guard.DOCUMENT.read_text().replace(
        "| **Total** | **207** |", "| **Total** | **999** |", 1
    )
    try:
        guard.parse_counter_table(
            broken_total, "| Raw construct | Occurrences |"
        )
    except SystemExit as error:
        assert "invalid total" in str(error)
    else:
        raise AssertionError("stale reconciliation total was not rejected")

    print("PASS: disposition checker detects contract and dependency regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
