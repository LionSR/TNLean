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

    fixture_inventory = guard.documented_fixtures(guard.DOCUMENT.read_text())
    assert len(fixture_inventory) == 264
    assert fixture_inventory["modes_dot_baseline.tex"][0] == "redraw"
    assert fixture_inventory["p_pitch.tex"][0] == "redraw"
    assert fixture_inventory["rev4075_alias.tex"][0] == "redraw"
    _, _, blueprint_inventory = guard.documented_blueprint(
        guard.DOCUMENT.read_text()
    )
    assert blueprint_inventory[("ch02_mps.tex", 54, "tenkz")] == "redraw"

    print("PASS: disposition checker detects contract and dependency regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
