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


def _build(source: str, *, path: Path = SYNTHETIC_PATH) -> DimensionInventory:
    return build_dimension_inventory_from_sources({path: source})


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
    validate_dimension_inventory(expected, actual)
    if actual.dimension_count != report.case_count:
        raise AssertionError(
            "comment or benchmark-book dimensions entered the inventory"
        )
    if format_dimension_inventory(expected) != INVENTORY.read_text(encoding="utf-8"):
        raise AssertionError("committed dimension inventory is not canonical JSON")


def test_formatting_stability() -> None:
    compact = r"""\begin{tenkzfree}
\tnput[dot]{a}{(1MM,2 true pt)}{}
\tnjoin{a}{3mm,4 mm}
\end{tenkzfree}
"""
    reformatted = r"""% A comment with an ignored 99mm literal.
\begin{tenkzfree}
  \tnput % formatting splice
    [dot] {a} { ( 1 mm , 2truept ) } {}
  \tnjoin{a}{3m% join a dimension unit
    m,
    4mm}
\end{tenkzfree}
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


def test_owner_span_grouping() -> None:
    source = r"""\begin{tenkzfree}[pitch=1mm]
  \tnput[dot]{a}{(3mm,4mm)}{\tn[label shift={2mm,5mm}]{A}}
\end{tenkzfree}
"""
    inventory = _build(source)
    sites = inventory.cases[0].sites
    if len(sites) != 3:
        raise AssertionError(f"nested option/command sites were not split: {sites!r}")
    if tuple(site.owner for site in sites) != (
        DimensionOwner.METRIC,
        DimensionOwner.LAYOUT,
        DimensionOwner.LAYOUT,
    ):
        raise AssertionError(f"narrowest owner spans were not retained: {sites!r}")
    if tuple(site.literals for site in sites) != (
        ("1mm",),
        ("3mm", "4mm"),
        ("2mm", "5mm"),
    ):
        raise AssertionError(f"owner-site literal vectors were not explicit: {sites!r}")
    if not sites[0].site.startswith("tenkzfree@1/option:"):
        raise AssertionError(f"environment option lost its semantic key: {sites[0]!r}")
    if not sites[1].site.startswith("tenkzfree@1/command:"):
        raise AssertionError(f"command site lost its semantic key: {sites[1]!r}")
    if not sites[2].site.startswith("tenkzfree@1/option:"):
        raise AssertionError(f"nested option lost its semantic key: {sites[2]!r}")

    _expect_error(
        lambda: _build(r"\tnput{a}{(1mm,2mm)}{}"),
        "outside a tenkz environment",
    )
    _expect_error(
        lambda: _build(r"\begin{tenkzfree}\foo{1mm}\end{tenkzfree}"),
        "cannot inventory unowned case dimension",
    )


def test_construct_ordinals_are_semantic() -> None:
    base_source = r"""\begin{tenkzfree}
  \tnput{a}{(1mm,2mm)}{}
\end{tenkzfree}
"""
    base = _build(base_source)
    dimension_free_prefixes = (
        r"\tnpic{\tn{}}" + "\n",
        r"\begin{tenkzfree}\tn{}\end{tenkzfree}" + "\n",
        r"\begin{tenkz}\tn{}\end{tenkz}" + "\n",
    )
    for prefix in dimension_free_prefixes:
        if _build(prefix + base_source) != base:
            raise AssertionError(
                f"dimension-free construct shifted semantic ordinals: {prefix!r}"
            )

    dimension_free_owner_commands = base_source.replace(
        "  \\tnput{a}",
        "  \\tnput{origin}{(0,0)}{}\n"
        "  \\tnjoin{origin}{origin}\n"
        "  \\tnwire{origin}{origin}\n"
        "  \\tnedge{origin}{origin}\n"
        "  \\tnarrow{origin}{origin}\n"
        "  \\tnput{a}",
    )
    if _build(dimension_free_owner_commands) != base:
        raise AssertionError("dimension-free owner commands changed the inventory")

    spaced = base_source.replace(r"\begin{tenkzfree}", r"\begin {tenkzfree}")
    commented = base_source.replace(
        r"\begin{tenkzfree}", "\\begin% legal splice\n{tenkzfree}"
    )
    if _build(spaced) != base or _build(commented) != base:
        raise AssertionError("legal begin spacing or comment splice changed site keys")

    multiple = r"""\begin{tenkzfree}
  \tnput{a}{(1mm,2mm)}{}
\end{tenkzfree}
\begin{tenkzfree}
  \tnput{b}{(3mm,4mm)}{}
\end{tenkzfree}
\begin{tenkz}
  \tnput{c}{(5mm,6mm)}{}
\end{tenkz}
\tnpic{\tnput{d}{(7mm,8mm)}{}}
"""
    multiple_sites = _build(multiple).cases[0].sites
    prefixes = tuple(site.site.split("/", 1)[0] for site in multiple_sites)
    if prefixes != ("tenkzfree@1", "tenkzfree@2", "tenkz@1", "tnpic@1"):
        raise AssertionError(f"per-kind construct ordinals drifted: {prefixes!r}")

    nested = r"""\begin{tenkzfree}
  \tnput{outer}{(1mm,2mm)}{}
  \begin{tenkzfree}
    \tnput{inner}{(3mm,4mm)}{}
  \end{tenkzfree}
\end{tenkzfree}
"""
    nested_sites = _build(nested).cases[0].sites
    nested_prefixes = tuple(site.site.split("/", 1)[0] for site in nested_sites)
    if nested_prefixes != ("tenkzfree@1", "tenkzfree@2"):
        raise AssertionError(
            f"nested sites were not assigned to the narrowest construct: "
            f"{nested_prefixes!r}"
        )


def test_balanced_changes_are_rejected() -> None:
    duplicate_source = r"""\begin{tenkzfree}
  \tnjoin[fused]{1mm,2mm}{3mm,4mm}
  \tnjoin[fused]{5mm,6mm}{7mm,8mm}
\end{tenkzfree}
"""
    duplicate = _build(duplicate_source)
    duplicate_sites = duplicate.cases[0].sites
    if [site.site.rsplit("#occurrence=", 1)[-1] for site in duplicate_sites] != [
        "1",
        "2",
    ]:
        raise AssertionError(
            f"duplicate skeletons did not gain local ordinals: {duplicate_sites!r}"
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

    distinct = r"""\begin{tenkzfree}
  \tnput{a}{(1mm,2mm)}{}
  \tnput{b}{(3mm,4mm)}{}
  \tnjoin{a}{5mm,6mm}
\end{tenkzfree}
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
    site_replacement = _build(distinct.replace(r"\tnput{a}", r"\tnput{c}"))
    _expect_error(
        lambda: validate_dimension_inventory(expected, site_replacement),
        "dimension owner site changed",
    )
    deleted = _build(distinct.replace("  \\tnjoin{a}{5mm,6mm}\n", ""))
    _expect_error(
        lambda: validate_dimension_inventory(expected, deleted),
        "dimension site count changed",
    )
    owner_balanced = _build(
        distinct.replace("1mm,2mm", "5mm,2mm").replace("5mm,6mm", "1mm,6mm")
    )
    _expect_error(
        lambda: validate_dimension_inventory(expected, owner_balanced),
        "dimension literal vector changed",
    )


def test_invalid_schema_is_rejected() -> None:
    valid = _data(_build(r"\begin{tenkzfree}\tnput{a}{(1mm,2mm)}{}\end{tenkzfree}"))
    valid_path = SYNTHETIC_PATH.as_posix()
    _expect_error(lambda: parse_dimension_inventory("{"), "cannot parse")
    _expect_error(
        lambda: parse_dimension_inventory(
            '{"schema_version": 2, "schema_version": 2, "cases": {}}'
        ),
        "duplicate JSON field",
    )
    for mutation, phrase in (
        ({**valid, "schema_version": 1}, "schema_version must be exactly 2"),
        ({**valid, "extra": 1}, "fields must be exactly"),
        ({"schema_version": 2, "cases": []}, ".cases must be an object"),
        (
            {"schema_version": 2, "cases": {"../escape.tex": []}},
            "canonical repo-relative .tex path",
        ),
        (
            {"schema_version": 2, "cases": {"case.tex": []}},
            "must be under tests/tenkz/rmp/<section>/cases/",
        ),
        (
            {"schema_version": 2, "cases": {valid_path: []}},
            "must be a nonempty array",
        ),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
        )

    row = next(iter(valid["cases"].values()))[0]
    unsorted = {
        "schema_version": 2,
        "cases": {
            "tests/tenkz/rmp/z/cases/z.tex": [row],
            "tests/tenkz/rmp/a/cases/a.tex": [row],
        },
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(unsorted)),
        "canonical sorted order",
    )
    duplicate_row = {
        "schema_version": 2,
        "cases": {valid_path: [row, row]},
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(duplicate_row)),
        ".site duplicates",
    )

    def row_mutation(**changes: object) -> dict[str, object]:
        result = dict(row)
        result.update(changes)
        return {
            "schema_version": 2,
            "cases": {valid_path: [result]},
        }

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
            "construct ordinals must be contiguous",
        ),
        (
            row_mutation(site=str(row["site"]).replace(r"\tnput", r"\tnunknown")),
            "command skeleton is not a dimension owner",
        ),
        (
            row_mutation(site=str(row["site"]).replace(r"\tnput", r"\tnput*")),
            "command skeleton is not a dimension owner",
        ),
        (
            row_mutation(site=str(row["site"]).replace("<dimension>", "1mm", 1)),
            "normalized dimension placeholders",
        ),
        (
            row_mutation(site=str(row["site"]) + "#occurrence=0"),
            "normalized dimension placeholders",
        ),
        (row_mutation(owner="benchmark-book layout"), "active case dimension"),
        (row_mutation(owner="unknown"), "is not a dimension owner"),
        (row_mutation(owner="route/string"), "owner implied by its site command"),
        (row_mutation(literals=[]), "must be a nonempty array"),
        (row_mutation(literals=["1 MM"]), "normalized absolute TeX dimension"),
        (row_mutation(literals=["1em"]), "normalized absolute TeX dimension"),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
        )

    option_data = _data(_build(r"\begin{tenkzfree}[pitch=1mm]\end{tenkzfree}"))
    parse_dimension_inventory(_json(option_data))
    option_row = next(iter(option_data["cases"].values()))[0]
    option_row["owner"] = "composition/layout"
    _expect_error(
        lambda: parse_dimension_inventory(_json(option_data)),
        "owner implied by its site command",
    )

    unique_ordinal = row_mutation(site=str(row["site"]) + "#occurrence=1")
    _expect_error(
        lambda: parse_dimension_inventory(_json(unique_ordinal)),
        "unique site has a duplicate ordinal",
    )
    base = str(row["site"])
    bad_ordinals = {
        "schema_version": 2,
        "cases": {
            valid_path: [
                {**row, "site": base + "#occurrence=1"},
                {**row, "site": base + "#occurrence=3"},
            ]
        },
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(bad_ordinals)),
        "duplicate site ordinals",
    )


def test_updater_is_safe_and_idempotent() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    paths = tuple(target.case for target in targets)
    committed = INVENTORY.read_text(encoding="utf-8")
    expected = load_dimension_inventory(INVENTORY)
    expected_counts = (
        f"cases {expected.case_count} | sites {expected.site_count} | "
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

        fake_repo = tmp_path / "repo"
        case_path = Path("tests/tenkz/rmp/synthetic/cases/reviewed-deletion.tex")
        case = fake_repo / case_path
        case.parent.mkdir(parents=True)
        before_source = r"""\begin{tenkzfree}
  \tnput{a}{(1mm,2mm)}{}
  \tnput{b}{(3mm,4mm)}{}
\end{tenkzfree}
"""
        after_source = r"""\begin{tenkzfree}
  \tnput{a}{(1mm,2mm)}{}
\end{tenkzfree}
"""
        case.write_text(before_source, encoding="utf-8")
        book = fake_repo / "docs/tenkz/rmp-benchmark.tex"
        style = fake_repo / "docs/tenkz/tenkzrmpbenchmark.sty"
        book.parent.mkdir(parents=True)
        book.write_text(" ".join(["1pt"] * 4), encoding="utf-8")
        style.write_text(" ".join(["1pt"] * 24), encoding="utf-8")
        baseline = _build(before_source, path=case_path)
        destination = tmp_path / "synthetic-dimension-ownership.json"
        baseline_text = format_dimension_inventory(baseline)
        destination.write_text(baseline_text, encoding="utf-8")

        stale = _data(baseline)
        stale_sites = stale["cases"][case_path.as_posix()]
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
        repeat_count = CASE_DIMENSION_CEILING // baseline.dimension_count + 1
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
        if updated.site_count != 1 or updated.dimension_count != 2:
            raise AssertionError(f"reviewed deletion wrote wrong counts: {updated!r}")
        if not any("sites 1 | dimensions 2" in item for item in messages):
            raise AssertionError(
                f"reviewed deletion did not print counts: {messages!r}"
            )


def main() -> int:
    test_repository_inventory()
    test_formatting_stability()
    test_owner_span_grouping()
    test_construct_ordinals_are_semantic()
    test_balanced_changes_are_rejected()
    test_invalid_schema_is_rejected()
    test_updater_is_safe_and_idempotent()
    print("PASS: exact RMP dimension owner-site inventory")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
