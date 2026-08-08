#!/usr/bin/env python3
"""Regression checks for the exact RMP dimension owner-site inventory."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from typing import Callable

from tenkz_rmp import DEFAULT_MANIFEST, load_manifest
from tenkzlib.dimension_inventory import (
    DEFAULT_DIMENSION_INVENTORY,
    DimensionInventory,
    DimensionInventoryError,
    build_dimension_inventory_from_sources,
    collect_dimension_inventory,
    format_dimension_inventory,
    load_dimension_inventory,
    parse_dimension_inventory,
    validate_dimension_inventory,
    validate_rmp_dimension_gate,
)
from tenkzlib.dimensions import (
    CASE_DIMENSION_CEILING,
    DimensionOwner,
    DimensionOwnershipError,
)
from update_tenkz_dimension_inventory import update_dimension_inventory


ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / DEFAULT_DIMENSION_INVENTORY
SYNTHETIC_PATH = Path("tests/tenkz/rmp/synthetic/cases/synthetic-case.tex")


def _assert_exact_construct_containers(inventory: DimensionInventory) -> None:
    for case in inventory.cases:
        for construct in case.constructs:
            container = f"{construct}::{construct}"
            if case.invocations.count(container) != 1:
                raise AssertionError(
                    f"generated construct {construct!r} lacks exactly one "
                    f"container invocation {container!r}"
                )


def _build(source: str, *, path: Path = SYNTHETIC_PATH) -> DimensionInventory:
    inventory = build_dimension_inventory_from_sources({path: source})
    _assert_exact_construct_containers(inventory)
    return inventory


def _expect_error(action: Callable[[], object], phrase: str) -> str:
    try:
        action()
    except (DimensionInventoryError, DimensionOwnershipError) as exc:
        message = str(exc)
        if phrase not in message:
            raise AssertionError(
                f"expected failure containing {phrase!r}, found {message!r}"
            ) from exc
        return message
    raise AssertionError(f"expected failure containing {phrase!r}")


def _data(inventory: DimensionInventory) -> dict[str, object]:
    return json.loads(format_dimension_inventory(inventory))


def _json(data: object) -> str:
    return json.dumps(data, ensure_ascii=False) + "\n"


def test_repository_inventory() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    paths = tuple(target.case for target in targets)
    report = validate_rmp_dimension_gate(ROOT, paths)
    expected = load_dimension_inventory(INVENTORY)
    actual = collect_dimension_inventory(ROOT, paths)
    _assert_exact_construct_containers(actual)
    validate_dimension_inventory(expected, actual)
    if actual.dimension_count != report.case_count:
        raise AssertionError(
            "comment or benchmark-book dimensions entered the inventory"
        )
    if format_dimension_inventory(expected) != INVENTORY.read_text(encoding="utf-8"):
        raise AssertionError("committed dimension inventory is not canonical JSON")


def test_formatting_stability() -> None:
    compact = r"""\begin{tenkz}
\tnwire[route=arc,name={A B}]{a}{(1MM,2 true pt)}
\tnwire{a}{3mm,4 mm}
\end{tenkz}
"""
    reformatted = r"""% A comment with an ignored 99mm literal.
\begin{tenkz}
  \tnwire % formatting splice
    [ route = arc , name = {A B} ] {a} {(1 mm,2truept)}
  \tnwire{a}{3m% join a dimension unit
m,4mm}
\end{tenkz}
"""
    first = _build(compact)
    second = _build(reformatted)
    if first != second:
        raise AssertionError(
            "whitespace, comments, line movement, or unit case changed semantic sites"
        )
    if first.dimension_count != 4 or first.site_count != 2:
        raise AssertionError(f"unexpected normalized synthetic inventory: {first!r}")
    literals = tuple(
        literal
        for case in first.cases
        for site in case.sites
        for literal in site.literals
    )
    if literals != ("1mm", "2truept", "3mm", "4mm"):
        raise AssertionError(f"dimension literals were not normalized: {literals!r}")
    if any("#occurrence=" in site.site for site in first.cases[0].sites):
        raise AssertionError("unique semantic sites gained positional ordinals")

    comment_only = _build("% route length 7mm\n")
    if comment_only.case_count or comment_only.dimension_count:
        raise AssertionError("comment dimensions entered the active inventory")

    spaced_label = _build(
        r"\begin{tenkz}\tnwire{\text{A B}}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    joined_label = _build(
        r"\begin{tenkz}\tnwire{\text{AB}}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if spaced_label == joined_label:
        raise AssertionError("TeX-significant argument whitespace left site identity")
    _expect_error(
        lambda: validate_dimension_inventory(spaced_label, joined_label),
        "dimension owner site changed",
    )

    separated_control = _build(
        r"\begin{tenkz}\tnwire{\foo α}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    merged_control = _build(
        r"\begin{tenkz}\tnwire{\fooα}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if separated_control == merged_control:
        raise AssertionError("a Unicode control-word boundary left site identity")

    separated_conservative_control = _build(
        r"\begin{tenkz}\tnwire{\foo Ⅳ}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    merged_conservative_control = _build(
        r"\begin{tenkz}\tnwire{\fooⅣ}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if separated_conservative_control == merged_conservative_control:
        raise AssertionError(
            "the shared conservative control-word alphabet drifted"
        )

    comment_terminated_control = _build(
        "\\begin{tenkz}\\tnwire{\\foo% boundary\n"
        "bar}{(1mm,2mm)}\\end{tenkz}"
    )
    spaced_terminated_control = _build(
        r"\begin{tenkz}\tnwire{\foo bar}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    merged_terminated_control = _build(
        r"\begin{tenkz}\tnwire{\foobar}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if comment_terminated_control != spaced_terminated_control:
        raise AssertionError("a comment-terminated control word changed identity")
    if comment_terminated_control == merged_terminated_control:
        raise AssertionError("a comment splice merged distinct control words")

    spaced_option_value = _build(
        r"\begin{tenkz}\tnwire[name={A B}]{a}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    joined_option_value = _build(
        r"\begin{tenkz}\tnwire[name={AB}]{a}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if spaced_option_value == joined_option_value:
        raise AssertionError("whitespace inside an option value left site identity")

    nested_bracket_value = _build(
        r"\begin{tenkz}\tnwire[name=[A B]]{a}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    joined_bracket_value = _build(
        r"\begin{tenkz}\tnwire[name=[AB]]{a}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if nested_bracket_value == joined_bracket_value:
        raise AssertionError(
            "whitespace inside a nested option-value bracket left site identity"
        )

    authored_marker_first = _build(
        r"\begin{tenkz}\tnwire{<dimension>}{(1mm,0)}"
        r"\end{tenkz}"
    )
    authored_marker_second = _build(
        r"\begin{tenkz}\tnwire{1mm}{(<dimension>,0)}"
        r"\end{tenkz}"
    )
    for marker_inventory in (authored_marker_first, authored_marker_second):
        if "%3Cdimension%3E" not in marker_inventory.cases[0].sites[0].site:
            raise AssertionError("authored marker punctuation was not escaped")
        if (
            parse_dimension_inventory(format_dimension_inventory(marker_inventory))
            != marker_inventory
        ):
            raise AssertionError("escaped authored marker text did not round-trip")
    if authored_marker_first == authored_marker_second:
        raise AssertionError("authored marker text collided with a generated placeholder")
    _expect_error(
        lambda: validate_dimension_inventory(
            authored_marker_first, authored_marker_second
        ),
        "dimension owner site changed",
    )

    authored_occurrence = _build(
        r"\begin{tenkz}\tnwire{\#occurrence=1}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    if "%23occurrence=1" not in authored_occurrence.cases[0].sites[0].site:
        raise AssertionError("authored occurrence-marker punctuation was not escaped")
    if (
        parse_dimension_inventory(format_dimension_inventory(authored_occurrence))
        != authored_occurrence
    ):
        raise AssertionError("escaped authored occurrence marker did not round-trip")

    for authored_delimiter in ("/command:x", "/option:y"):
        delimiter_inventory = _build(
            r"\begin{tenkz}\tnwire{"
            + authored_delimiter
            + r"}{(1mm,2mm)}\end{tenkz}"
        )
        if (
            parse_dimension_inventory(
                format_dimension_inventory(delimiter_inventory)
            )
            != delimiter_inventory
        ):
            raise AssertionError(
                f"authored {authored_delimiter!r} forged a site-key boundary"
            )

    combined_authored_markers = _build(
        r"\begin{tenkz}\tnwire{<dimension> /command:x /option:y "
        r"\#occurrence=1}{(1mm,2mm)}\end{tenkz}"
    )
    if (
        parse_dimension_inventory(
            format_dimension_inventory(combined_authored_markers)
        )
        != combined_authored_markers
    ):
        raise AssertionError("combined authored site markers did not round-trip")


def test_owner_span_grouping() -> None:
    source = r"""\begin{tenkz}[pitch=1mm]
  \tnwire[route=arc]{\tn[label shift={2mm,5mm}]{A}}{(3mm,4mm)}
\end{tenkz}
"""
    inventory = _build(source)
    sites = inventory.cases[0].sites
    if len(sites) != 3:
        raise AssertionError(f"nested option/command sites were not split: {sites!r}")
    if tuple(site.owner for site in sites) != (
        DimensionOwner.METRIC,
        DimensionOwner.LAYOUT,
        DimensionOwner.ROUTE,
    ):
        raise AssertionError(f"narrowest owner spans were not retained: {sites!r}")
    if tuple(site.literals for site in sites) != (
        ("1mm",),
        ("2mm", "5mm"),
        ("3mm", "4mm"),
    ):
        raise AssertionError(f"owner-site literal vectors were not explicit: {sites!r}")
    if not sites[0].site.startswith(
        "tenkz@1::tenkz@1/option:tenkz/pitch="
    ):
        raise AssertionError(f"environment option lost its semantic key: {sites[0]!r}")
    if not sites[1].site.startswith(
        "tenkz@1::tenkz@1/tn@1/option:tn/labelshift="
    ):
        raise AssertionError(f"nested option lost its semantic key: {sites[1]!r}")
    if not sites[2].site.startswith(
        "tenkz@1::tenkz@1/tnwire@1/command:"
    ):
        raise AssertionError(f"command site lost its semantic key: {sites[2]!r}")
    if parse_dimension_inventory(format_dimension_inventory(inventory)) != inventory:
        raise AssertionError("generated command and option site keys did not round-trip")

    _expect_error(
        lambda: _build(r"\tnwire{a}{(1mm,2mm)}"),
        "outside a tenkz environment",
    )
    _expect_error(
        lambda: _build(r"\begin{tenkz}\foo{1mm}\end{tenkz}"),
        "cannot inventory unowned case dimension",
    )

    tn_owned = _build(
        r"\begin{tenkz}\tn[label shift=1mm]{A}\tnX{B}"
        r"\end{tenkz}"
    )
    tn_x_owned = _build(
        r"\begin{tenkz}\tn{A}\tnX[label shift=1mm]{B}"
        r"\end{tenkz}"
    )
    if tn_owned == tn_x_owned:
        raise AssertionError("moving an option between containers preserved identity")
    if "/option:tn/labelshift=" not in tn_owned.cases[0].sites[0].site:
        raise AssertionError("tn option site lost its owning container")
    if "/option:tnX/labelshift=" not in tn_x_owned.cases[0].sites[0].site:
        raise AssertionError("tnX option site lost its owning container")
    _expect_error(
        lambda: validate_dimension_inventory(tn_owned, tn_x_owned),
        "dimension owner site changed",
    )


def test_comment_terminated_control_word() -> None:
    # A `%` comment terminates a control word mid-name even though its
    # discarded endline leaves no space token in the input stream
    # (`dimensions.py`: `scan_case_dimensions` works on an offset-preserving
    # comment-stripped view and `_active_fragment` inserts a space across
    # comment gaps so control words cannot merge).  TeX reads a backslash-name
    # interrupted by a comment as the control word `\tn` followed by the
    # letters w, i, r, e on the next line, never as the merged command
    # `\tnwire`; the scanner must reproduce that reading on raw,
    # non-comment-stripped source.
    comment_terminated = (
        "\\begin{tenkz}[pitch=1mm]\n"
        "  \\tn% mid-name comment\n"
        "wire{a}{(3mm,4mm)}\n"
        "\\end{tenkz}\n"
    )
    space_terminated = (
        "\\begin{tenkz}[pitch=1mm]\n"
        "  \\tn wire{a}{(3mm,4mm)}\n"
        "\\end{tenkz}\n"
    )
    merged = (
        "\\begin{tenkz}[pitch=1mm]\n"
        "  \\tnwire{a}{(3mm,4mm)}\n"
        "\\end{tenkz}\n"
    )

    # The comment-terminated and space-terminated forms both leave the
    # (3mm,4mm) dimensions unowned (no `\tnwire` command is formed) ...
    comment_message = _expect_error(
        lambda: _build(comment_terminated),
        "cannot inventory unowned case dimension",
    )
    space_message = _expect_error(
        lambda: _build(space_terminated),
        "cannot inventory unowned case dimension",
    )
    # ... and the comment form reports the dimensions at their true source
    # line after the discarded comment endline, proving that offsets survive
    # the comment rather than collapsing into the preceding line.
    if ":3: 3mm" not in comment_message:
        raise AssertionError(
            f"comment-terminated control word lost its source line: {comment_message!r}"
        )
    if ":2: 3mm" not in space_message:
        raise AssertionError(
            f"space-terminated control word lost its source line: {space_message!r}"
        )

    # The merged control word is a genuinely different, dimension-bearing
    # command: the comment form must not spuriously merge into it.
    merged_inventory = _build(merged)
    merged_sites = merged_inventory.cases[0].sites
    if tuple(site.owner for site in merged_sites) != (
        DimensionOwner.METRIC,
        DimensionOwner.ROUTE,
    ):
        raise AssertionError(f"merged control word lost its owners: {merged_sites!r}")
    if not any(
        site.site.endswith("tnwire@1/command:\\tnwire{a}{(<dimension>,<dimension>)}")
        for site in merged_sites
    ):
        raise AssertionError(
            f"merged control word lost its dimension owner identity: {merged_sites!r}"
        )


def test_construct_ordinals_are_semantic() -> None:
    base_source = r"""\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
\end{tenkz}
"""
    base = _build(base_source)
    for construct_name, sibling_source in (
        (
            "tnpic",
            r"\tnpic[pitch=1mm]{\tn{A}}"
            r"\tnpic[pitch=2mm]{\tn{B}}",
        ),
        (
            "tntree",
            r"\tntree[pitch=1mm]{({}{})}"
            r"\tntree[pitch=2mm]{({}{})}",
        ),
    ):
        siblings = _build(sibling_source)
        if siblings.cases[0].constructs != (
            f"{construct_name}@1",
            f"{construct_name}@2",
        ):
            raise AssertionError(
                f"sibling {construct_name} constructs lost source ordinals"
            )
        if (
            parse_dimension_inventory(format_dimension_inventory(siblings))
            != siblings
        ):
            raise AssertionError(
                f"sibling {construct_name} containers did not round-trip"
            )
    for different_kind_prefix, changed_anchor in (
        (r"\tnpic{\tn{}}" + "\n", "dimension construct anchors changed"),
        (r"\tntree{({}{})}" + "\n", "dimension construct anchors changed"),
    ):
        prefixed = _build(different_kind_prefix + base_source)
        if prefixed.cases[0].sites != base.cases[0].sites:
            raise AssertionError(
                "a construct of another kind shifted semantic ordinals: "
                f"{different_kind_prefix!r}"
            )
        if prefixed.cases[0].constructs == base.cases[0].constructs:
            raise AssertionError("a dimension-free construct lacked an explicit anchor")
        _expect_error(
            lambda prefixed=prefixed: validate_dimension_inventory(base, prefixed),
            changed_anchor,
        )

    same_kind_prefix = r"\begin{tenkz}\tn{}\end{tenkz}" + "\n"
    shifted = _build(same_kind_prefix + base_source)
    if shifted == base or not shifted.cases[0].sites[0].site.startswith(
        "tenkz@2::tenkz@2/"
    ):
        raise AssertionError(
            "a dimension-free construct did not retain its ordinal identity"
        )
    if shifted.cases[0].constructs != ("tenkz@1", "tenkz@2"):
        raise AssertionError(
            f"dimension-free anchor sequence drifted: {shifted.cases[0].constructs!r}"
        )
    if parse_dimension_inventory(format_dimension_inventory(shifted)) != shifted:
        raise AssertionError("dimension-free construct anchors did not round-trip")

    first_construct = r"""\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
\end{tenkz}
\begin{tenkz}\tn{}\end{tenkz}
"""
    second_construct = r"""\begin{tenkz}\tn{}\end{tenkz}
\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
\end{tenkz}
"""
    first_inventory = _build(first_construct)
    second_inventory = _build(second_construct)
    if first_inventory == second_inventory:
        raise AssertionError("moving dimensions between constructs preserved identity")
    _expect_error(
        lambda: validate_dimension_inventory(first_inventory, second_inventory),
        "dimension invocation anchors changed",
    )

    inert_definition = r"""\def\unused{\begin{tenkz}\tn{}\end{tenkz}}
\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}
\begin{tenkz}\tn{}\end{tenkz}
"""
    active_move = r"""\begin{tenkz}\tn{}\end{tenkz}
\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}
"""
    definition_inventory = _build(inert_definition)
    moved_inventory = _build(active_move)
    if definition_inventory.cases[0].constructs != (
        "tenkz@1",
        "tenkz@2",
    ):
        raise AssertionError("an inert replacement construct consumed an anchor")
    if definition_inventory == moved_inventory:
        raise AssertionError("an inert replacement construct masked a cross-site move")
    _expect_error(
        lambda: validate_dimension_inventory(
            definition_inventory, moved_inventory
        ),
        "dimension invocation anchors changed",
    )

    inert_tnpic = _build(r"\def\unused{\tnpic{\tn{}}}" + base_source)
    if inert_tnpic != base:
        raise AssertionError("a tnpic stored in a replacement body gained an anchor")
    inert_tntree = _build(r"\def\unused{\tntree{({}{})}}" + base_source)
    if inert_tntree != base:
        raise AssertionError("a tntree stored in a replacement body gained an anchor")
    inert_end = _build(
        r"\begin{tenkz}\def\unused{\end{tenkz}}"
        r"\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    if inert_end != base:
        raise AssertionError("an inert environment end closed an active construct")

    dimension_free_owner_commands = base_source.replace(
        "  \\tnwire{a}",
        "  \\tnwire{origin}{(0,0)}\n"
        "  \\tnwire{origin}{origin}\n"
        "  \\tncut{origin}\n"
        "  \\tnwire{a}",
    )
    anchored_commands = _build(dimension_free_owner_commands)
    if anchored_commands == base:
        raise AssertionError("dimension-free owner commands lacked invocation anchors")
    if "/tnwire@3/command:" not in anchored_commands.cases[0].sites[0].site:
        raise AssertionError("a dimension-free tnwire did not consume its ordinal")
    _expect_error(
        lambda: validate_dimension_inventory(base, anchored_commands),
        "dimension invocation anchors changed",
    )

    spaced = base_source.replace(r"\begin{tenkz}", r"\begin {tenkz}")
    commented = base_source.replace(
        r"\begin{tenkz}", "\\begin% legal splice\n{tenkz}"
    )
    if _build(spaced) != base or _build(commented) != base:
        raise AssertionError("legal begin spacing or comment splice changed site keys")

    real_tnpic = r"\tnpic{\tnwire{a}{(1mm,2mm)}}"
    escaped_tnpic = r"\\tnpic{\tnwire{a}{(1mm,2mm)}}"
    _build(real_tnpic)
    _expect_error(
        lambda: _build(escaped_tnpic),
        "outside a tenkz environment",
    )

    standalone_tree = _build(r"\tntree[pitch=1mm]{({}{})}")
    if not standalone_tree.cases[0].sites[0].site.startswith(
        "tntree@1::tntree@1/option:tntree/pitch="
    ):
        raise AssertionError("a standalone tntree lacked its construct anchor")

    multiple = r"""\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
\end{tenkz}
\begin{tenkz}
  \tnwire{b}{(3mm,4mm)}
\end{tenkz}
\begin{tenkz}
  \tnwire{c}{(5mm,6mm)}
\end{tenkz}
\tnpic{\tnwire{d}{(7mm,8mm)}}
"""
    multiple_sites = _build(multiple).cases[0].sites
    prefixes = tuple(site.site.split("::", 1)[0] for site in multiple_sites)
    if prefixes != ("tenkz@1", "tenkz@2", "tenkz@3", "tnpic@1"):
        raise AssertionError(f"per-kind construct ordinals drifted: {prefixes!r}")

    nested = r"""\begin{tenkz}
  \tnwire{outer}{(1mm,2mm)}
  \begin{tenkz}
    \tnwire{inner}{(3mm,4mm)}
  \end{tenkz}
\end{tenkz}
"""
    nested_sites = _build(nested).cases[0].sites
    nested_prefixes = tuple(site.site.split("::", 1)[0] for site in nested_sites)
    if nested_prefixes != (
        "tenkz@1",
        "tenkz@1/tenkz@1",
    ):
        raise AssertionError(
            f"nested sites were not assigned to the narrowest construct: "
            f"{nested_prefixes!r}"
        )


def test_picture_scope_ancestry_is_semantic() -> None:
    grouped = _build(
        r"\begin{tenkz}"
        r"\tngroup[frame={rotate=90}]{\tnwire{a}{(1mm,2mm)}}\tn{B}"
        r"\end{tenkz}"
    )
    ungrouped = _build(
        r"\begin{tenkz}"
        r"\tngroup[frame={rotate=90}]{}\tnwire{a}{(1mm,2mm)}\tn{B}"
        r"\end{tenkz}"
    )
    if grouped.cases[0].scopes != (
        "tenkz@1",
        "tenkz@1/tngroup@1",
    ):
        raise AssertionError("tngroup did not gain hierarchical scope identity")
    if grouped.cases[0].scopes != ungrouped.cases[0].scopes:
        raise AssertionError("moving content changed unchanged tngroup scope anchors")
    if grouped == ungrouped:
        raise AssertionError("moving a dimension across tngroup preserved identity")
    if "::tenkz@1/tngroup@1/tnwire@1/" not in grouped.cases[0].sites[0].site:
        raise AssertionError("a grouped invocation lost its PICTURE ancestry")
    if "::tenkz@1/tnwire@1/" not in ungrouped.cases[0].sites[0].site:
        raise AssertionError("an ungrouped invocation gained PICTURE ancestry")
    _expect_error(
        lambda: validate_dimension_inventory(grouped, ungrouped),
        "dimension invocation anchors changed",
    )

    panel = r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    equation_panel = _build(
        r"\tenkzkernel\begin{tenkzeq}[size=m]"
        + panel
        + r"\end{tenkzeq}\tn{B}"
    )
    trailing_panel = _build(
        r"\tenkzkernel\begin{tenkzeq}[size=m]\end{tenkzeq}"
        + panel
        + r"\tn{B}"
    )
    if equation_panel.cases[0].scopes != (
        "tenkzeq@1",
        "tenkzeq@1/tenkz@1",
    ):
        raise AssertionError("tenkzeq did not own its nested PICTURE scope")
    if trailing_panel.cases[0].scopes != ("tenkzeq@1", "tenkz@1"):
        raise AssertionError("a trailing panel inherited the preceding tenkzeq scope")
    if equation_panel == trailing_panel:
        raise AssertionError("moving a panel across tenkzeq preserved identity")
    _expect_error(
        lambda: validate_dimension_inventory(equation_panel, trailing_panel),
        "dimension scope anchors changed",
    )

    nested_group = _build(
        r"\begin{tenkz}\tngroup{\tngroup{"
        r"\tnwire{a}{(1mm,2mm)}}}\end{tenkz}"
    )
    outer_group = _build(
        r"\begin{tenkz}\tngroup{\tngroup{}"
        r"\tnwire{a}{(1mm,2mm)}}\end{tenkz}"
    )
    expected_nested_scopes = (
        "tenkz@1",
        "tenkz@1/tngroup@1",
        "tenkz@1/tngroup@1/tngroup@1",
    )
    if nested_group.cases[0].scopes != expected_nested_scopes:
        raise AssertionError("nested same-name scopes lost per-parent ordinals")
    if nested_group.cases[0].scopes != outer_group.cases[0].scopes:
        raise AssertionError("moving content changed unchanged nested scope anchors")
    if nested_group == outer_group:
        raise AssertionError("moving a dimension out of a nested group preserved identity")

    first_sibling = _build(
        r"\begin{tenkz}\tngroup{\tnwire{a}{(1mm,2mm)}}"
        r"\tngroup{}\end{tenkz}"
    )
    second_sibling = _build(
        r"\begin{tenkz}\tngroup{}"
        r"\tngroup{\tnwire{a}{(1mm,2mm)}}\end{tenkz}"
    )
    expected_sibling_scopes = (
        "tenkz@1",
        "tenkz@1/tngroup@1",
        "tenkz@1/tngroup@2",
    )
    if first_sibling.cases[0].scopes != expected_sibling_scopes:
        raise AssertionError("dimension-free first sibling did not consume scope @1")
    if first_sibling.cases[0].scopes != second_sibling.cases[0].scopes:
        raise AssertionError("sibling scope anchors depended on dimension ownership")
    if first_sibling == second_sibling:
        raise AssertionError("moving a dimension between sibling scopes preserved identity")

    for body in (
        r"\tnpic{\tnwire{a}{(1mm,2mm)}}",
        r"\tntree[pitch=1mm]{({}{})}",
    ):
        nested_construct = _build(
            r"\begin{tenkz}\tngroup{" + body + r"}\end{tenkz}"
        )
        sibling_construct = _build(
            r"\begin{tenkz}\tngroup{}" + body + r"\end{tenkz}"
        )
        if nested_construct.cases[0].constructs == sibling_construct.cases[0].constructs:
            raise AssertionError("a nested command construct lost its scope ancestry")
        _expect_error(
            lambda nested_construct=nested_construct, sibling_construct=sibling_construct: (
                validate_dimension_inventory(nested_construct, sibling_construct)
            ),
            "dimension construct anchors changed",
        )

    base = _build(
        r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    inert_definition = _build(
        r"\def\unused{\tngroup{\tn{}}\begin{tenkzeq}\end{tenkzeq}}"
        r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    comment_hidden = _build(
        "% \\tngroup{\\tn{}} \\begin{tenkzeq}\\end{tenkzeq}\n"
        r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    if inert_definition != base or comment_hidden != base:
        raise AssertionError("inert PICTURE containers consumed scope anchors")

    ordinary_arguments = _build(
        r"\begin{tenkz}\tnspan{a}{b}\tncut{a}\tnprose{text}"
        r"\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    if ordinary_arguments.cases[0].scopes != ("tenkz@1",):
        raise AssertionError("ordinary brace arguments were promoted to PICTURE scopes")

    spliced_group = _build(
        "\\begin{tenkz}\\tngroup% legal splice\n"
        "{\\tnwire{a}{(1mm,2mm)}}\\end{tenkz}"
    )
    compact_group = _build(
        r"\begin{tenkz}\tngroup{\tnwire{a}{(1mm,2mm)}}"
        r"\end{tenkz}"
    )
    if spliced_group != compact_group:
        raise AssertionError("a comment splice changed PICTURE scope identity")

    for inventory in (
        grouped,
        ungrouped,
        equation_panel,
        trailing_panel,
        nested_group,
        outer_group,
        first_sibling,
        second_sibling,
    ):
        if parse_dimension_inventory(format_dimension_inventory(inventory)) != inventory:
            raise AssertionError("scope-aware inventory did not round-trip")


def test_balanced_changes_are_rejected() -> None:
    duplicate_source = r"""\begin{tenkz}
  \tnwire[route=arc]{1mm,2mm}{3mm,4mm}
  \tnwire[route=arc]{5mm,6mm}{7mm,8mm}
\end{tenkz}
"""
    duplicate = _build(duplicate_source)
    duplicate_sites = duplicate.cases[0].sites
    if not (
        "/tnwire@1/command:" in duplicate_sites[0].site
        and "/tnwire@2/command:" in duplicate_sites[1].site
    ):
        raise AssertionError(
            f"same-name commands lacked invocation ordinals: {duplicate_sites!r}"
        )
    repeated_option = _build(
        r"\begin{tenkz}[pitch=1mm,pitch=2mm]\end{tenkz}"
    )
    repeated_option_sites = repeated_option.cases[0].sites
    if [
        site.site.rsplit("#occurrence=", 1)[-1]
        for site in repeated_option_sites
    ] != ["1", "2"]:
        raise AssertionError(
            "duplicate sites within one invocation lacked local ordinals: "
            f"{repeated_option_sites!r}"
        )
    moved_duplicate = _build(
        duplicate_source.replace("1mm,2mm", "5mm,2mm").replace("5mm,6mm", "1mm,6mm")
    )
    message = _expect_error(
        lambda: validate_dimension_inventory(duplicate, moved_duplicate),
        "dimension literal vector changed",
    )
    if f"{SYNTHETIC_PATH.as_posix()}:2" not in message:
        raise AssertionError(
            f"balanced-move diagnostic lost its source line: {message}"
        )

    distinct = r"""\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
  \tnwire{b}{(3mm,4mm)}
  \tnwire{a}{5mm,6mm}
\end{tenkz}
"""
    expected = _build(distinct)
    literal_replacement = _build(distinct.replace("1mm", "9mm", 1))
    _expect_error(
        lambda: validate_dimension_inventory(expected, literal_replacement),
        "dimension literal vector changed",
    )
    cross_site_move = _build(
        distinct.replace("1mm,2mm", "3mm,2mm").replace("3mm,4mm", "1mm,4mm")
    )
    _expect_error(
        lambda: validate_dimension_inventory(expected, cross_site_move),
        "dimension literal vector changed",
    )
    site_replacement = _build(distinct.replace(r"\tnwire{a}", r"\tnwire{c}"))
    _expect_error(
        lambda: validate_dimension_inventory(expected, site_replacement),
        "dimension owner site changed",
    )
    deleted = _build(distinct.replace("  \\tnwire{a}{5mm,6mm}\n", ""))
    _expect_error(
        lambda: validate_dimension_inventory(expected, deleted),
        "dimension invocation anchors changed",
    )
    owner_balanced = _build(
        distinct.replace("1mm,2mm", "5mm,2mm").replace("5mm,6mm", "1mm,6mm")
    )
    _expect_error(
        lambda: validate_dimension_inventory(expected, owner_balanced),
        "dimension literal vector changed",
    )


def test_invocation_anchors_are_semantic() -> None:
    plain = _build(
        r"\begin{tenkz}\tn[label shift=1mm]{A}\end{tenkz}"
    )
    conjugate = _build(
        r"\begin{tenkz}\tn*[label shift=1mm]{A}\end{tenkz}"
    )
    if plain == conjugate:
        raise AssertionError("tn and conjugate tn* shared an invocation anchor")
    if "/tn@1/option:tn/" not in plain.cases[0].sites[0].site:
        raise AssertionError("plain tn option lost its semantic invocation")
    if "/tn*@1/option:tn*/" not in conjugate.cases[0].sites[0].site:
        raise AssertionError("conjugate tn option lost its semantic invocation")
    _expect_error(
        lambda: validate_dimension_inventory(plain, conjugate),
        "dimension invocation anchors changed",
    )

    first_tn = _build(
        r"\begin{tenkz}\tn[label shift=1mm]{A}\tn{B}"
        r"\end{tenkz}"
    )
    second_tn = _build(
        r"\begin{tenkz}\tn{A}\tn[label shift=1mm]{B}"
        r"\end{tenkz}"
    )
    if first_tn == second_tn:
        raise AssertionError("moving an option between tn siblings preserved identity")
    if "/tn@1/option:" not in first_tn.cases[0].sites[0].site:
        raise AssertionError("first tn sibling lost its invocation ordinal")
    if "/tn@2/option:" not in second_tn.cases[0].sites[0].site:
        raise AssertionError("second tn sibling lost its invocation ordinal")
    _expect_error(
        lambda: validate_dimension_inventory(first_tn, second_tn),
        "dimension owner site changed",
    )

    first_tnwire = _build(
        r"\begin{tenkz}\tnwire{a}{(1mm,0)}"
        r"\tnwire{a}{(0,0)}\end{tenkz}"
    )
    second_tnwire = _build(
        r"\begin{tenkz}\tnwire{a}{(0,0)}"
        r"\tnwire{a}{(1mm,0)}\end{tenkz}"
    )
    if first_tnwire == second_tnwire:
        raise AssertionError("moving a dimension between tnwire siblings preserved identity")
    if "/tnwire@1/command:" not in first_tnwire.cases[0].sites[0].site:
        raise AssertionError("first tnwire sibling lost its invocation ordinal")
    if "/tnwire@2/command:" not in second_tnwire.cases[0].sites[0].site:
        raise AssertionError("second tnwire sibling lost its invocation ordinal")
    _expect_error(
        lambda: validate_dimension_inventory(first_tnwire, second_tnwire),
        "dimension owner site changed",
    )

    base_source = (
        r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    inert_prefix = _build(
        base_source.replace(
            r"\tnwire{a}",
            r"\def\unused{\tnwire{x}{(0,0)}}\tnwire{a}",
        )
    )
    base = _build(base_source)
    if inert_prefix != base:
        raise AssertionError("an inert macro-body command consumed an invocation anchor")
    active_prefix = _build(
        base_source.replace(
            r"\tnwire{a}", r"\tnwire{x}{(0,0)}\tnwire{a}"
        )
    )
    if "/tnwire@2/command:" not in active_prefix.cases[0].sites[0].site:
        raise AssertionError("a dimension-free active command lacked an anchor")
    _expect_error(
        lambda: validate_dimension_inventory(base, active_prefix),
        "dimension invocation anchors changed",
    )

    for inventory in (
        plain,
        conjugate,
        first_tn,
        second_tn,
        first_tnwire,
        second_tnwire,
        inert_prefix,
        active_prefix,
    ):
        if parse_dimension_inventory(format_dimension_inventory(inventory)) != inventory:
            raise AssertionError("invocation-anchor inventory did not round-trip")


def test_invalid_schema_is_rejected() -> None:
    valid = _data(_build(r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"))
    valid_path = SYNTHETIC_PATH.as_posix()
    valid_case = next(iter(valid["cases"].values()))
    scope_anchors = list(valid_case["scopes"])
    anchors = list(valid_case["constructs"])
    invocation_anchors = list(valid_case["invocations"])
    row = valid_case["sites"][0]

    def case_record(
        rows: list[object],
        *,
        scopes: object = scope_anchors,
        constructs: object = anchors,
        invocations: object = invocation_anchors,
    ) -> dict[str, object]:
        return {
            "scopes": scopes,
            "constructs": constructs,
            "invocations": invocations,
            "sites": rows,
        }

    def document(
        rows: list[object],
        *,
        scopes: object = scope_anchors,
        constructs: object = anchors,
        invocations: object = invocation_anchors,
    ) -> dict[str, object]:
        return {
            "schema_version": 5,
            "cases": {
                valid_path: case_record(
                    rows,
                    scopes=scopes,
                    constructs=constructs,
                    invocations=invocations,
                )
            },
        }

    _expect_error(lambda: parse_dimension_inventory("{"), "cannot parse")
    _expect_error(
        lambda: parse_dimension_inventory(
            '{"schema_version": 5, "schema_version": 5, "cases": {}}'
        ),
        "duplicate JSON field",
    )
    for mutation, phrase in (
        ({**valid, "schema_version": 4}, "schema_version must be exactly 5"),
        ({**valid, "extra": 1}, "fields must be exactly"),
        ({"schema_version": 5, "cases": []}, ".cases must be an object"),
        (
            {"schema_version": 5, "cases": {"../escape.tex": {}}},
            "canonical repo-relative .tex path",
        ),
        (
            {"schema_version": 5, "cases": {"case.tex": {}}},
            "must be under tests/tenkz/rmp/<section>/cases/",
        ),
        (
            {"schema_version": 5, "cases": {valid_path: []}},
            "must be an object",
        ),
        (
            {"schema_version": 5, "cases": {valid_path: {"sites": [row]}}},
            "fields must be exactly",
        ),
        (document([row], scopes="tenkz@1"), ".scopes must be an array"),
        (
            document([row], constructs=[]),
            ".constructs must be a nonempty array",
        ),
        (
            document([row], invocations=[]),
            ".invocations must be a nonempty array",
        ),
        (
            document([]),
            ".sites must be a nonempty array",
        ),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
        )

    unsorted = {
        "schema_version": 5,
        "cases": {
            "tests/tenkz/rmp/z/cases/z.tex": valid_case,
            "tests/tenkz/rmp/a/cases/a.tex": valid_case,
        },
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(unsorted)),
        "canonical sorted order",
    )
    duplicate_row = {
        "schema_version": 5,
        "cases": {valid_path: case_record([row, row])},
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(duplicate_row)),
        ".site duplicates",
    )

    def row_mutation(**changes: object) -> dict[str, object]:
        result = dict(row)
        result.update(changes)
        return document([result])

    for scopes, phrase in (
        (["not-an-anchor"], "must be a scope anchor"),
        (["tnpic@1"], "must be a scope anchor"),
        (["tenkz@0"], "must be a scope anchor"),
        (["tenkz@01"], "must be a scope anchor"),
        (["tenkz@2"], "continue contiguous tenkz ordinals"),
        (
            ["tenkz@1/tngroup@1"],
            "references missing parent scope",
        ),
        (
            ["tenkz@1", "tenkz@1/tngroup@2"],
            "continue contiguous tngroup ordinals",
        ),
        (
            ["tenkz@1", "tenkz@1"],
            "continue contiguous tenkz ordinals",
        ),
    ):
        _expect_error(
            lambda scopes=scopes: parse_dimension_inventory(
                _json(document([row], scopes=scopes))
            ),
            phrase,
        )

    _expect_error(
        lambda: parse_dimension_inventory(
            _json(
                document(
                    [row],
                    scopes=["tenkz@1", "tenkz@1/tngroup@1"],
                )
            )
        ),
        "missing invocations=['tenkz@1/tngroup@1'], extra invocations=[]",
    )

    _expect_error(
        lambda: parse_dimension_inventory(
            _json(
                document(
                    [row],
                    scopes=[
                        "tenkz@1",
                        "tenkz@1/tenkz@1",
                    ],
                    invocations=[
                        *invocation_anchors,
                        "tenkz@1::tenkz@1/tenkz@1",
                    ],
                )
            )
        ),
        "missing constructs=['tenkz@1/tenkz@1'], extra constructs=[]",
    )

    for constructs, phrase in (
        (["not-an-anchor"], "must be a construct anchor"),
        (["tenkz@0"], "must be a construct anchor"),
        (["tenkz@01"], "must be a construct anchor"),
        (["tnpic@2"], "continue contiguous tnpic ordinals"),
        (
            ["tenkz@1/tnpic@2"],
            "continue contiguous tnpic ordinals",
        ),
        (
            ["tenkz@1/tenkz@1"],
            "scope construct lacks matching scope",
        ),
        (["tnpic@1/tnpic@1"], "must be a construct anchor"),
        (["tenkz@1", "tenkz@1"], "continue contiguous"),
    ):
        _expect_error(
            lambda constructs=constructs: parse_dimension_inventory(
                _json(document([row], constructs=constructs))
            ),
            phrase,
        )

    for invocations, phrase in (
        (["not-an-anchor"], "must be an invocation anchor"),
        (["tenkz@1::tenkz@0"], "must be an invocation anchor"),
        (["tenkz@1::tenkz@01"], "must be an invocation anchor"),
        (
            ["tenkz@2::tenkz@2"],
            "references missing construct anchor",
        ),
        (
            [
                "tenkz@1::tenkz@1",
                "tenkz@1::tenkz@1/tnwire@2",
            ],
            "continue contiguous tnwire ordinals",
        ),
        (
            [
                "tenkz@1::tenkz@1",
                "tenkz@1::tenkz@1",
            ],
            "duplicates scope invocation",
        ),
        (
            [
                "tenkz@1::tenkz@1",
                "tenkz@1::tenkz@1/tngroup@1",
            ],
            "extra invocations=['tenkz@1/tngroup@1']",
        ),
        (
            ["tenkz@1::tenkz@1/tnwire@1"],
            "before its container invocation",
        ),
        (
            [
                *invocation_anchors,
                "tenkz@1::tenkzeq@1",
            ],
            "must be an invocation anchor",
        ),
    ):
        _expect_error(
            lambda invocations=invocations: parse_dimension_inventory(
                _json(document([row], invocations=invocations))
            ),
            phrase,
        )

    for mutation, phrase in (
        (row_mutation(extra=True), "fields must be exactly"),
        (row_mutation(site="not-a-site"), "normalized semantic site key"),
        (
            row_mutation(site=str(row["site"]).replace("@1/", "@0/")),
            "normalized semantic site key",
        ),
        (
            row_mutation(site=str(row["site"]).replace("@1/", "@01/")),
            "normalized semantic site key",
        ),
        (
            row_mutation(site=str(row["site"]).replace("@1/", "@2/")),
            "references missing invocation anchor",
        ),
        (
            row_mutation(site=str(row["site"]).replace(r"\tnwire", r"\tnunknown")),
            "command skeleton is not a dimension owner",
        ),
        (
            row_mutation(site=str(row["site"]).replace(r"\tnwire", r"\tnwire*")),
            "command skeleton is not a dimension owner",
        ),
        (
            row_mutation(site=str(row["site"]).replace("<dimension>", "1mm", 1)),
            "normalized dimension placeholders",
        ),
        (
            row_mutation(site=str(row["site"]).replace("<dimension>", "<raw>")),
            "normalized dimension placeholders",
        ),
        (
            row_mutation(site=str(row["site"]) + "#occurrence=0"),
            "normalized dimension placeholders",
        ),
        (row_mutation(owner="benchmark-book layout"), "active case dimension"),
        (row_mutation(owner="unknown"), "is not a dimension owner"),
        (row_mutation(owner="composition/layout"), "owner implied by its site command"),
        (row_mutation(literals=[]), "must be a nonempty array"),
        (
            row_mutation(literals=["1mm"]),
            "dimension count does not match its literal vector",
        ),
        (row_mutation(literals=["1 MM"]), "normalized absolute TeX dimension"),
        (row_mutation(literals=["1em"]), "normalized absolute TeX dimension"),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
        )

    option_data = _data(_build(r"\begin{tenkz}[pitch=1mm]\end{tenkz}"))
    parse_dimension_inventory(_json(option_data))
    option_row = next(iter(option_data["cases"].values()))["sites"][0]
    invalid_container_data = _data(
        _build(r"\begin{tenkz}[pitch=1mm]\end{tenkz}")
    )
    invalid_container_row = next(
        iter(invalid_container_data["cases"].values())
    )["sites"][0]
    invalid_container_row["site"] = str(invalid_container_row["site"]).replace(
        "tenkz/pitch=", "tn/pitch="
    )
    _expect_error(
        lambda: parse_dimension_inventory(_json(invalid_container_data)),
        "not owned by its container",
    )
    option_row["owner"] = "composition/layout"
    _expect_error(
        lambda: parse_dimension_inventory(_json(option_data)),
        "owner implied by its site command",
    )

    mismatched_command_data = _data(
        _build(r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}")
    )
    mismatched_case = next(iter(mismatched_command_data["cases"].values()))
    mismatched_case["invocations"][1] = (
        "tenkz@1::tenkz@1/tncut@1"
    )
    mismatched_case["sites"][0]["site"] = str(
        mismatched_case["sites"][0]["site"]
    ).replace("/tnwire@1/", "/tncut@1/")
    _expect_error(
        lambda: parse_dimension_inventory(_json(mismatched_command_data)),
        "command skeleton does not match its invocation",
    )

    sibling_construct_data = _data(
        _build(
            r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
            r"\begin{tenkz}\tnwire{b}{(3mm,4mm)}\end{tenkz}"
        )
    )
    sibling_case = next(iter(sibling_construct_data["cases"].values()))
    sibling_invocation = "tenkz@2::tenkz@2/tnwire@1"
    forged_invocation = "tenkz@1::tenkz@2/tnwire@1"
    sibling_index = sibling_case["invocations"].index(sibling_invocation)
    sibling_case["invocations"][sibling_index] = forged_invocation
    sibling_case["sites"][1]["site"] = str(
        sibling_case["sites"][1]["site"]
    ).replace(sibling_invocation, forged_invocation, 1)
    _expect_error(
        lambda: parse_dimension_inventory(_json(sibling_construct_data)),
        "narrowest compatible scope construct",
    )

    for nested_source in (
        r"\begin{tenkz}\begin{tenkz}"
        r"\tnwire{a}{(1mm,2mm)}\end{tenkz}\end{tenkz}",
        r"\begin{tenkz}\tngroup{\tnpic{"
        r"\tnwire{a}{(1mm,2mm)}}}\end{tenkz}",
    ):
        nested_inventory = _build(nested_source)
        if (
            parse_dimension_inventory(
                format_dimension_inventory(nested_inventory)
            )
            != nested_inventory
        ):
            raise AssertionError("a valid nested construct relationship was rejected")

    late_enclosing_construct = _data(
        _build(
            r"\begin{tenkz}\begin{tenkz}"
            r"\tnwire{a}{(1mm,2mm)}\end{tenkz}\end{tenkz}"
        )
    )
    late_enclosing_case = next(
        iter(late_enclosing_construct["cases"].values())
    )
    late_enclosing_case["constructs"].reverse()
    _expect_error(
        lambda: parse_dimension_inventory(_json(late_enclosing_construct)),
        "enclosing construct 'tenkz@1' must precede nested construct",
    )

    late_construct_container = _data(
        _build(r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}")
    )
    late_container_case = next(
        iter(late_construct_container["cases"].values())
    )
    late_container_case["invocations"][0:2] = reversed(
        late_container_case["invocations"][0:2]
    )
    _expect_error(
        lambda: parse_dimension_inventory(_json(late_construct_container)),
        "depends on construct 'tenkz@1' before its container invocation",
    )

    late_parent_scope = _data(
        _build(
            r"\begin{tenkz}\tngroup{\tnwire{a}{(1mm,2mm)}}"
            r"\end{tenkz}"
        )
    )
    late_parent_case = next(iter(late_parent_scope["cases"].values()))
    late_parent_case["invocations"][1:3] = reversed(
        late_parent_case["invocations"][1:3]
    )
    _expect_error(
        lambda: parse_dimension_inventory(_json(late_parent_scope)),
        "depends on represented parent scope 'tenkz@1/tngroup@1' "
        "before its invocation",
    )

    empty_picture_scope = _build(
        r"\begin{tenkz}\begin{tenkz}\end{tenkz}"
        r"\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    )
    if (
        parse_dimension_inventory(
            format_dimension_inventory(empty_picture_scope)
        )
        != empty_picture_scope
    ):
        raise AssertionError("a valid empty picture scope was rejected")

    empty_scope_only_containers = _build(
        r"\tenkzkernel\begin{tenkzeq}[size=m]\end{tenkzeq}"
        r"\begin{tenkz}\tngroup{}\tnwire{a}{(1mm,2mm)}"
        r"\end{tenkz}"
    )
    scope_only_anchors = set(empty_scope_only_containers.cases[0].scopes) - set(
        empty_scope_only_containers.cases[0].constructs
    )
    if scope_only_anchors != {
        "tenkzeq@1",
        "tenkz@1/tngroup@1",
    }:
        raise AssertionError(
            "empty tngroup or tenkzeq did not remain a scope-only container: "
            f"{scope_only_anchors!r}"
        )
    if (
        parse_dimension_inventory(
            format_dimension_inventory(empty_scope_only_containers)
        )
        != empty_scope_only_containers
    ):
        raise AssertionError("a valid empty scope-only container was rejected")

    unique_ordinal = row_mutation(site=str(row["site"]) + "#occurrence=1")
    _expect_error(
        lambda: parse_dimension_inventory(_json(unique_ordinal)),
        "unique site has a duplicate ordinal",
    )
    base = str(row["site"])
    bad_ordinals = {
        "schema_version": 5,
        "cases": {
            valid_path: case_record(
                [
                    {**row, "site": base + "#occurrence=1"},
                    {**row, "site": base + "#occurrence=3"},
                ]
            )
        },
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(bad_ordinals)),
        "duplicate site ordinals",
    )

    whitespace_data = _data(
        _build(
            r"\begin{tenkz}\tnwire{\text{A B}}{(1mm,2mm)}"
            r"\end{tenkz}"
        )
    )
    parse_dimension_inventory(_json(whitespace_data))
    whitespace_row = next(iter(whitespace_data["cases"].values()))["sites"][0]
    whitespace_row["site"] = str(whitespace_row["site"]).replace("A B", "A  B")
    _expect_error(
        lambda: parse_dimension_inventory(_json(whitespace_data)),
        "normalized semantic site key",
    )


def test_case_paths_are_regular_and_unaliased() -> None:
    source = r"\begin{tenkz}\tnwire{a}{(1mm,2mm)}\end{tenkz}"
    case_path = Path("tests/tenkz/rmp/synthetic/cases/synthetic-case.tex")
    with tempfile.TemporaryDirectory(prefix="tenkz-dimension-path-") as tmp:
        tmp_path = Path(tmp)
        repo = tmp_path / "repo"
        case = repo / case_path
        case.parent.mkdir(parents=True)
        case.write_text(source, encoding="utf-8")
        if collect_dimension_inventory(repo, (case_path,)).dimension_count != 2:
            raise AssertionError("a regular exact case path did not inventory")

        outside = tmp_path / "outside.tex"
        outside.write_text(source, encoding="utf-8")
        case.unlink()
        case.symlink_to(outside)
        _expect_error(
            lambda: collect_dimension_inventory(repo, (case_path,)),
            "contains a symlink",
        )

        parent_repo = tmp_path / "parent-repo"
        rmp_root = parent_repo / "tests" / "tenkz" / "rmp"
        rmp_root.mkdir(parents=True)
        outside_section = tmp_path / "outside-section"
        outside_case = outside_section / "cases" / case_path.name
        outside_case.parent.mkdir(parents=True)
        outside_case.write_text(source, encoding="utf-8")
        (rmp_root / "synthetic").symlink_to(
            outside_section, target_is_directory=True
        )
        _expect_error(
            lambda: collect_dimension_inventory(parent_repo, (case_path,)),
            "contains a symlink",
        )


def test_updater_is_safe_and_idempotent() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    paths = tuple(target.case for target in targets)
    committed = INVENTORY.read_text(encoding="utf-8")
    expected = load_dimension_inventory(INVENTORY)
    expected_counts = (
        f"cases {expected.case_count} | scopes {expected.scope_count} | "
        f"constructs {expected.construct_count} | "
        f"invocations {expected.invocation_count} | "
        f"sites {expected.site_count} | "
        f"dimensions {expected.dimension_count}"
    )
    with tempfile.TemporaryDirectory(prefix="tenkz-dimension-inventory-") as tmp:
        tmp_path = Path(tmp)
        repository_copy = tmp_path / "repository-dimension-ownership.json"
        repository_copy.write_text(committed, encoding="utf-8")
        messages: list[str] = []
        if update_dimension_inventory(
            ROOT, paths, repository_copy, emit=messages.append
        ):
            raise AssertionError("idempotent updater rewrote the canonical inventory")
        if repository_copy.read_text(encoding="utf-8") != committed:
            raise AssertionError("idempotent updater changed inventory bytes")
        if not any(expected_counts in item for item in messages):
            raise AssertionError(f"updater did not print exact counts: {messages!r}")

        # The live corpus owns zero dimensions and the ceilings are frozen
        # there; the synthetic fixture still exercises the updater machinery,
        # so it borrows a fixture-sized ceiling and restores the zero ratchet.
        import tenkzlib.dimensions as _dims
        _saved_ceiling = _dims.CASE_DIMENSION_CEILING
        _saved_owner_ceilings = _dims.CASE_OWNER_CEILINGS
        _dims.CASE_DIMENSION_CEILING = 5
        _dims.CASE_OWNER_CEILINGS = {
            DimensionOwner.METRIC: 0,
            DimensionOwner.FRAME: 0,
            DimensionOwner.ROUTE: 4,
            DimensionOwner.LAYOUT: 1,
        }
        fake_repo = tmp_path / "repo"
        case_path = Path("tests/tenkz/rmp/synthetic/cases/reviewed-deletion.tex")
        case = fake_repo / case_path
        case.parent.mkdir(parents=True)
        before_source = r"""\begin{tenkz}\tn{}\end{tenkz}
\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
  \tnwire{b}{(3mm,4mm)}
  \tn[label shift=5mm]{x}
\end{tenkz}
"""
        after_source = r"""\begin{tenkz}\tn{}\end{tenkz}
\begin{tenkz}
  \tnwire{a}{(1mm,2mm)}
  \tn[label shift=5mm]{x}
\end{tenkz}
"""
        case.write_text(before_source, encoding="utf-8")
        book = fake_repo / "docs/tenkz/rmp-benchmark.tex"
        style = fake_repo / "docs/tenkz/tenkzrmpbenchmark.sty"
        book.parent.mkdir(parents=True)
        book.write_text(" ".join(["1pt"] * 4), encoding="utf-8")
        style.write_text(" ".join(["1pt"] * 24), encoding="utf-8")
        baseline = _build(before_source, path=case_path)
        if baseline.cases[0].scopes != ("tenkz@1", "tenkz@2"):
            raise AssertionError("updater fixture lost its PICTURE scope anchors")
        if baseline.cases[0].constructs != ("tenkz@1", "tenkz@2"):
            raise AssertionError("updater fixture lost its dimension-free anchor")
        if baseline.cases[0].invocations != (
            "tenkz@1::tenkz@1",
            "tenkz@1::tenkz@1/tn@1",
            "tenkz@2::tenkz@2",
            "tenkz@2::tenkz@2/tnwire@1",
            "tenkz@2::tenkz@2/tnwire@2",
            "tenkz@2::tenkz@2/tn@1",
        ):
            raise AssertionError("updater fixture lost invocation anchors")
        if not any(
            "/option:tn/labelshift=" in site.site
            for site in baseline.cases[0].sites
        ):
            raise AssertionError("updater fixture lost its option-container identity")
        destination = tmp_path / "synthetic-dimension-ownership.json"
        baseline_text = format_dimension_inventory(baseline)
        destination.write_text(baseline_text, encoding="utf-8")

        stale = _data(baseline)
        stale_sites = stale["cases"][case_path.as_posix()]["sites"]
        stale_sites[0]["literals"][0] = "999mm"
        stale_text = _json(stale)
        destination.write_text(stale_text, encoding="utf-8")
        messages.clear()
        if not update_dimension_inventory(
            fake_repo, (case_path,), destination, emit=messages.append
        ):
            raise AssertionError("updater did not repair a reviewed literal change")
        if destination.read_text(encoding="utf-8") != baseline_text:
            raise AssertionError("updater did not restore canonical inventory bytes")
        if not any(item.startswith("--- ") and "999mm" in item for item in messages):
            raise AssertionError(
                f"updater did not print its literal diff: {messages!r}"
            )

        destination.write_text(stale_text, encoding="utf-8")
        _expect_error(
            lambda: update_dimension_inventory(
                fake_repo,
                (case_path,),
                destination,
                check=True,
                emit=lambda _: None,
            ),
            "inventory is stale",
        )
        if destination.read_text(encoding="utf-8") != stale_text:
            raise AssertionError("--check modified a stale inventory")

        destination.write_text("{\n", encoding="utf-8")
        malformed = destination.read_bytes()
        _expect_error(
            lambda: update_dimension_inventory(
                ROOT, paths, destination, emit=lambda _: None
            ),
            "cannot parse",
        )
        if destination.read_bytes() != malformed:
            raise AssertionError("updater overwrote a malformed old inventory")

        destination.write_text(baseline_text, encoding="utf-8")
        before = destination.read_bytes()
        repeat_count = _dims.CASE_DIMENSION_CEILING // baseline.dimension_count + 1
        _expect_error(
            lambda: update_dimension_inventory(
                fake_repo,
                tuple(case_path for _ in range(repeat_count)),
                destination,
                emit=lambda _: None,
            ),
            "case dimensions increased",
        )
        if destination.read_bytes() != before:
            raise AssertionError("updater wrote before aggregate ceilings passed")

        destination.write_text(stale_text, encoding="utf-8")
        message = _expect_error(
            lambda: validate_rmp_dimension_gate(
                fake_repo, (case_path,), inventory_path=destination
            ),
            "dimension literal vector changed",
        )
        if "tests/tenkz/rmp/" not in message or ":" not in message:
            raise AssertionError(
                f"production gate diagnostic lost source context: {message}"
            )

        destination.write_text(baseline_text, encoding="utf-8")
        case.write_text(after_source, encoding="utf-8")
        messages.clear()
        if not update_dimension_inventory(
            fake_repo,
            (case_path,),
            destination,
            emit=messages.append,
        ):
            raise AssertionError("explicit updater did not record a reviewed deletion")
        updated = load_dimension_inventory(destination)
        if updated.site_count != 2 or updated.dimension_count != 3:
            raise AssertionError(f"reviewed deletion wrote wrong counts: {updated!r}")
        if not any("sites 2 | dimensions 3" in item for item in messages):
            raise AssertionError(
                f"reviewed deletion did not print counts: {messages!r}"
            )
        _dims.CASE_DIMENSION_CEILING = _saved_ceiling
        _dims.CASE_OWNER_CEILINGS = _saved_owner_ceilings


def main() -> int:
    test_repository_inventory()
    test_formatting_stability()
    test_owner_span_grouping()
    test_comment_terminated_control_word()
    test_construct_ordinals_are_semantic()
    test_picture_scope_ancestry_is_semantic()
    test_balanced_changes_are_rejected()
    test_invocation_anchors_are_semantic()
    test_invalid_schema_is_rejected()
    test_case_paths_are_regular_and_unaliased()
    test_updater_is_safe_and_idempotent()
    print("PASS: exact RMP dimension owner-site inventory")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
