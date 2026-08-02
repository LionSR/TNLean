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
from tenkzlib.dimensions import DimensionOwner, DimensionOwnershipError
from update_tenkz_dimension_inventory import update_dimension_inventory


ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / DEFAULT_DIMENSION_INVENTORY
SYNTHETIC_PATH = Path("tests/tenkz/rmp/synthetic-case.tex")


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
    if (
        actual.case_count,
        actual.site_count,
        actual.dimension_count,
    ) != (32, 422, 926):
        raise AssertionError(
            "exact dimension inventory counts drifted: "
            f"cases={actual.case_count}, sites={actual.site_count}, "
            f"dimensions={actual.dimension_count}"
        )
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
  \tnput[dot,pitch=2mm]{a}{(3mm,4mm)}{}
\end{tenkzfree}
"""
    inventory = _build(source)
    sites = inventory.cases[0].sites
    if len(sites) != 3:
        raise AssertionError(f"nested option/command sites were not split: {sites!r}")
    if tuple(site.owner for site in sites) != (
        DimensionOwner.METRIC,
        DimensionOwner.METRIC,
        DimensionOwner.LAYOUT,
    ):
        raise AssertionError(f"narrowest owner spans were not retained: {sites!r}")
    if tuple(site.literals for site in sites) != (
        ("1mm",),
        ("2mm",),
        ("3mm", "4mm"),
    ):
        raise AssertionError(f"owner-site literal vectors were not explicit: {sites!r}")
    if not sites[0].site.startswith("tenkzfree@1/option:"):
        raise AssertionError(f"environment option lost its semantic key: {sites[0]!r}")
    if not sites[2].site.startswith("tenkzfree@1/command:"):
        raise AssertionError(f"command site lost its semantic key: {sites[2]!r}")

    _expect_error(
        lambda: _build(r"\tnput{a}{(1mm,2mm)}{}"),
        "outside a tenkz environment",
    )
    _expect_error(
        lambda: _build(r"\begin{tenkzfree}\foo{1mm}\end{tenkzfree}"),
        "cannot inventory unowned case dimension",
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
            "must be a nonempty array",
        ),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
        )

    row = next(iter(valid["cases"].values()))[0]
    unsorted = {
        "schema_version": 2,
        "cases": {"z.tex": [row], "a.tex": [row]},
    }
    _expect_error(
        lambda: parse_dimension_inventory(_json(unsorted)),
        "canonical sorted order",
    )
    duplicate_row = {
        "schema_version": 2,
        "cases": {"case.tex": [row, row]},
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
            "cases": {"case.tex": [result]},
        }

    for mutation, phrase in (
        (row_mutation(extra=True), "fields must be exactly"),
        (row_mutation(site="not-a-site"), "normalized semantic site key"),
        (row_mutation(owner="benchmark-book layout"), "active case dimension"),
        (row_mutation(owner="unknown"), "is not a dimension owner"),
        (row_mutation(literals=[]), "must be a nonempty array"),
        (row_mutation(literals=["1 MM"]), "normalized absolute TeX dimension"),
        (row_mutation(literals=["1em"]), "normalized absolute TeX dimension"),
    ):
        _expect_error(
            lambda mutation=mutation: parse_dimension_inventory(_json(mutation)), phrase
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
            "case.tex": [
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
    with tempfile.TemporaryDirectory(prefix="tenkz-dimension-inventory-") as tmp:
        destination = Path(tmp) / "dimension-ownership.json"
        destination.write_text(committed, encoding="utf-8")
        messages: list[str] = []
        if update_dimension_inventory(ROOT, paths, destination, emit=messages.append):
            raise AssertionError("idempotent updater rewrote the canonical inventory")
        if destination.read_text(encoding="utf-8") != committed:
            raise AssertionError("idempotent updater changed inventory bytes")
        if not any(
            "cases 32 | sites 422 | dimensions 926" in item for item in messages
        ):
            raise AssertionError(f"updater did not print exact counts: {messages!r}")

        stale = json.loads(committed)
        first_sites = next(iter(stale["cases"].values()))
        first_sites[0]["literals"][0] = "999mm"
        stale_text = _json(stale)
        destination.write_text(stale_text, encoding="utf-8")
        messages.clear()
        if not update_dimension_inventory(
            ROOT, paths, destination, emit=messages.append
        ):
            raise AssertionError("updater did not repair a reviewed literal change")
        if destination.read_text(encoding="utf-8") != committed:
            raise AssertionError("updater did not restore canonical inventory bytes")
        if not any(item.startswith("--- ") and "999mm" in item for item in messages):
            raise AssertionError(
                f"updater did not print its literal diff: {messages!r}"
            )

        destination.write_text(stale_text, encoding="utf-8")
        _expect_error(
            lambda: update_dimension_inventory(
                ROOT, paths, destination, check=True, emit=lambda _: None
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

        destination.write_text(committed, encoding="utf-8")
        before = destination.read_bytes()
        dimension_path = load_dimension_inventory(INVENTORY).cases[0].path
        _expect_error(
            lambda: update_dimension_inventory(
                ROOT, (*paths, dimension_path), destination, emit=lambda _: None
            ),
            "case dimensions increased",
        )
        if destination.read_bytes() != before:
            raise AssertionError("updater wrote before aggregate ceilings passed")

        destination.write_text(stale_text, encoding="utf-8")
        message = _expect_error(
            lambda: validate_rmp_dimension_gate(
                ROOT, paths, inventory_path=destination
            ),
            "dimension literal vector changed",
        )
        if "tests/tenkz/rmp/" not in message or ":" not in message:
            raise AssertionError(
                f"production gate diagnostic lost source context: {message}"
            )

        fake_repo = Path(tmp) / "repo"
        case_path = Path("tests/tenkz/rmp/cases/reviewed-deletion.tex")
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
        deletion_inventory = Path(tmp) / "reviewed-deletion.json"
        deletion_inventory.write_text(
            format_dimension_inventory(
                build_dimension_inventory_from_sources({case_path: before_source})
            ),
            encoding="utf-8",
        )
        case.write_text(after_source, encoding="utf-8")
        messages.clear()
        if not update_dimension_inventory(
            fake_repo,
            (case_path,),
            deletion_inventory,
            emit=messages.append,
        ):
            raise AssertionError("explicit updater did not record a reviewed deletion")
        updated = load_dimension_inventory(deletion_inventory)
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
    test_balanced_changes_are_rejected()
    test_invalid_schema_is_rejected()
    test_updater_is_safe_and_idempotent()
    print("PASS: exact RMP dimension owner-site inventory")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
