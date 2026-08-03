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
        r"\tnmark[form={brace-below}]{}{}",
        r"\tnspan[brace below]{2}{}",
        r"\tnspan[brace above]{2}{}",
        r"\tn[cluster]{}",
        r"\tn[enclosure]{}",
        r"\tn[poly=5]{}",
        r"\tnmark{(1,1)-(2,2)}{}",
        r"\begin{tenkz}[boundary legs]\end{tenkz}",
        r"\begin{tenkz}[frame={rotate=90}]\end{tenkz}",
        r"\begin{tenkz}[frame={matrix={1,0,0,1}}]\end{tenkz}",
        r"\begin{tenkzcd}[maps]\end{tenkzcd}",
        r"\begin{tenkz}[bond dir=right]\end{tenkz}",
        r"\begin{tenkz}[up={i}]\end{tenkz}",
        r"\begin{tenkz}[down={j}]\end{tenkz}",
        r"\tnbond[none]{a}{b}",
        r"\begin{tenkz}[layer sep=2]\tn{}\end{tenkz}",
        r"\tntree[tree style=wire]{(a,b)}",
        r"\begin{tenkz}[invented key=value]\tn{}\end{tenkz}",
        r"\begin{tenkz}[invented-key=value]\tn{}\end{tenkz}",
        r"\tn[invented key=value]{}",
        r"\tndeclare{species}{x}{invented-key=}",
        r"\tndeclareatom{\tnprojector}{invented-key=}",
        r"\tngroup[form=label]{}",
        r"\tnpic[maps]{}",
        r"\tnpic[boundary legs]{}",
        "\\tntree\n[invented-key=]{(a,b)}",
    )
    for source in tombstones:
        assert guard.uses_tombstone(source), source

    accepted = (
        r"\begin{tenkz}[rows={op}, cols=2]\tn{}\end{tenkz}",
        r"\tn[box]{}",
        r"\tn[pill]{}",
        r"\tnfuse[span=2]{}",
        r"\tnmark[form=bracket]{}{}",
        r"\tnmark[form=enclosure]{{(1,1)}}{}",
        r"\tnwire[route=orth]{}{}",
        r"\tnset{species={left,right}}",
        r"\begin{tenkz}[frame={plane, basis={ket at (0,0), bra at (2,2)}}]"
        r"\end{tenkz}",
        r"\begin{tenkz}[frame={flat, basis={wire at (0,0), wire at (2,0)}}]"
        r"\end{tenkz}",
        r"\begin{tenkz}[rows={wire}, cols=2]\tn[skin=box, wide=2]{}"
        r"\tnwire[route=orth, dir=forward]{}{}\end{tenkz}",
        r"\tndeclare{species}{x}{hue=blue, base=box, pairings={up:down}}",
        r"\tngroup[frame=flat]{}",
        r"\begin{tenkz}\tn{$in=x$}\tn{weight=2}\tn{role=x}\end{tenkz}",
    )
    for source in accepted:
        assert not guard.uses_tombstone(source), source
    assert guard.source_target_codes(
        r"\begin{tenkz}[physical=up]\tn[box]{}\end{tenkz}"
    ) == frozenset({"C-policy", "C-record"})
    assert guard.source_target_codes(
        r"\tnset{species={alpha,beta}}"
    ) == frozenset({"C-declare"})
    assert guard.source_target_codes(r"\tndeclareatom{pill}") == frozenset(
        {"C-declare"}
    )
    assert guard.source_target_codes(
        r"\tndeclareatom{\tnprojector}{skin=box, ports={west:virtual}}"
    ) == frozenset({"C-declare"})
    assert guard.source_target_codes(r"\tenkzkernel") == frozenset({"C-switch"})
    for source in (
        r"\tnset{}",
        r"\tndeclare{}{}{}",
        r"\tndeclareatom{}",
        r"\tenkzkernel",
    ):
        assert guard.SETUP_COMMAND.search(source), source
    assert guard.source_target_codes(r"\tn[pill]{}") == frozenset({"C-record"})
    assert guard.source_target_codes(r"\tn[cluster={2x3}]{}") == frozenset(
        {"C-record"}
    )
    for source in (
        r"\begin{tenkz}\tn{$in=x$}\end{tenkz}",
        r"\begin{tenkz}\tn{weight=2}\end{tenkz}",
        r"\begin{tenkz}\tn{role=x}\end{tenkz}",
        r"\tngroup[frame=flat]{}",
        r"\tndeclare{species}{x}{hue=blue, base=box, pairings={up:down}}",
    ):
        assert guard.source_target_codes(source) == frozenset({"P-grid"}), source
    assert guard.source_target_codes("\\tntree\n[skin=box]{(a,b)}") == frozenset(
        {"C-tree"}
    )
    assert guard.source_target_codes(
        r"\begin{tenkzfree}\tnghost{}\end{tenkzfree}"
        r"\begin{tenkz}[physical=up]\tn{}\end{tenkz}"
    ) == frozenset({"R-free", "R-record", "C-policy"})
    assert guard.fragment_target_codes(
        r"\begin{tenkz}[physical=up]\tnspan[brace below]{2}{}\end{tenkz}"
    ) == frozenset({"C-policy", "C-record", "R-record"})

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        dependency = root / "dependency.inc"
        dependency.write_text(r"\begin{tenkz}\tncut{}\end{tenkz}")
        fixture = root / "fixture.tex"
        fixture.write_text(r"\input{dependency.inc}")
        expanded = guard.expanded_source(fixture)
        assert r"\tncut" in expanded
        assert guard.uses_tombstone(expanded)

        spaced_input = root / "spaced-input.tex"
        spaced_input.write_text(r"\input {dependency.inc}")
        assert r"\tncut" in guard.expanded_source(spaced_input)

        unbraced_input = root / "unbraced-input.tex"
        unbraced_input.write_text(r"\input dependency.inc")
        assert r"\tncut" in guard.expanded_source(unbraced_input)

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

        alias_cycle = root / "alias-cycle.tex"
        alias_cycle.write_text(r"\input{sub/../alias-cycle.tex}")
        try:
            guard.expanded_source(alias_cycle)
        except SystemExit as error:
            assert "recursive fixture input" in str(error)
        else:
            raise AssertionError("alias-path recursive input was not rejected")

        spaced = root / "spaced.tex"
        spaced.write_text(r"\begin {tenkz}\tn{}\end {tenkz}")
        assert guard.occurrences(spaced) == [(1, "tenkz")]
        assert ("spaced.tex", 1, "tenkz") in guard.construct_sources(spaced)

        multiline = root / "multiline.tex"
        multiline.write_text(
            r"\begin" "\n {tenkz}\n" r"\tn{}" "\n" r"\end" "\n {tenkz}"
        )
        normalized = guard.normalized_environment_spacing(multiline.read_text())
        assert len(normalized) == len(multiline.read_text())
        assert normalized.count("\n") == multiline.read_text().count("\n")
        assert guard.occurrences(multiline) == [(1, "tenkz")]
        assert ("multiline.tex", 1, "tenkz") in guard.construct_sources(multiline)

        equation = root / "equation.tex"
        equation.write_text(
            r"\begin{tenkzeq}\begin{tenkz}\tn{}\end{tenkz}\end{tenkzeq}"
        )
        assert guard.occurrences(equation) == [(1, "tenkzeq"), (1, "tenkz")]
        assert ("equation.tex", 1, "tenkzeq") in guard.construct_sources(equation)
        equation_source = equation.read_text()
        assert [
            construct.name for construct in guard.scan_constructs(equation_source)
        ] == ["tenkz"]
        assert [
            construct.name
            for construct in guard.scan_inventory_constructs(equation_source)
        ] == ["tenkzeq", "tenkz"]

        tree = root / "tree.tex"
        tree.write_text("\\tntree\n[skin=box]{(a,b)}")
        tree_source = tree.read_text()
        tree_sources = guard.construct_sources(tree)
        tree_key = ("tree.tex", 1, "tntree")
        assert list(tree_sources) == [tree_key]
        assert tree_sources[tree_key] == [tree_source]
        assert guard.source_target_codes(tree_source) == frozenset({"C-tree"})
        assert guard.fragment_target_codes(tree_sources[tree_key][0]) == frozenset(
            {"C-tree"}
        )

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
