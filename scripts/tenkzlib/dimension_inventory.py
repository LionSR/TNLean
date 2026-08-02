"""Freeze exact semantic sites for active RMP physical dimensions."""

from __future__ import annotations

import json
import re
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Iterable, Mapping

from tenkzlib.dimensions import (
    DIMENSION_RE,
    DimensionOwner,
    DimensionReport,
    collect_dimension_report,
    scan_case_dimension_sites,
    validate_dimension_report,
)
from tenkzlib.texcase import scan_constructs, strip_comments


DIMENSION_INVENTORY_SCHEMA_VERSION = 2
DEFAULT_DIMENSION_INVENTORY = Path("tests/tenkz/rmp/dimension-ownership.json")
_SITE_FIELDS = {"site", "owner", "literals"}
_ACTIVE_OWNERS = {
    DimensionOwner.METRIC,
    DimensionOwner.FRAME,
    DimensionOwner.ROUTE,
    DimensionOwner.LAYOUT,
}
_SITE_KEY_RE = re.compile(
    r"(?:tenkz|tenkzcd|tenkzfree|tenkzlattice|tenkzplanes|tnpic)"
    r"@[1-9][0-9]*/(?:command|option):.+"
)
_DUPLICATE_SUFFIX_RE = re.compile(r"^(.*)#occurrence=([1-9][0-9]*)$")


class DimensionInventoryError(ValueError):
    """The exact RMP dimension inventory is absent, invalid, or stale."""


@dataclass(frozen=True)
class DimensionInventorySite:
    """One normalized owner-site vector, with an ephemeral source line."""

    site: str
    owner: DimensionOwner
    literals: tuple[str, ...]
    line: int | None = field(default=None, compare=False)


@dataclass(frozen=True)
class DimensionInventoryCase:
    """Ordered dimension-bearing sites in one source case."""

    path: Path
    sites: tuple[DimensionInventorySite, ...]


@dataclass(frozen=True)
class DimensionInventory:
    """Versioned, case-grouped exact active-dimension inventory."""

    cases: tuple[DimensionInventoryCase, ...]
    source_end_lines: tuple[tuple[Path, int], ...] = field(
        default=(), compare=False, repr=False
    )

    @property
    def case_count(self) -> int:
        return len(self.cases)

    @property
    def site_count(self) -> int:
        return sum(len(case.sites) for case in self.cases)

    @property
    def dimension_count(self) -> int:
        return sum(len(site.literals) for case in self.cases for site in case.sites)


def normalize_dimension_literal(literal: str) -> str:
    """Normalize only lexical TeX-unit spelling, retaining the authored value."""
    return re.sub(r"\s+", "", literal).lower()


def _site_skeleton(source: str) -> str:
    replaced = DIMENSION_RE.sub("<dimension>", source)
    return re.sub(r"\s+", "", replaced)


def _case_inventory(path: Path, source: str) -> DimensionInventoryCase | None:
    owner_sites = scan_case_dimension_sites(path, source)
    if not owner_sites:
        return None
    constructs = scan_constructs(strip_comments(source))
    labelled_constructs = tuple(enumerate(constructs, 1))
    base_rows: list[tuple[str, DimensionOwner, tuple[str, ...], int]] = []
    for owner_site in owner_sites:
        candidates = [
            (ordinal, construct)
            for ordinal, construct in labelled_constructs
            if construct.start <= owner_site.offset < construct.end
        ]
        if not candidates:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: dimension owner site is "
                "outside a tenkz environment"
            )
        ordinal, construct = min(
            candidates, key=lambda item: item[1].end - item[1].start
        )
        skeleton = _site_skeleton(owner_site.source)
        if not skeleton:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: empty dimension site skeleton"
            )
        base_site = f"{construct.name}@{ordinal}/{owner_site.kind}:{skeleton}"
        literals = tuple(
            normalize_dimension_literal(occurrence.literal)
            for occurrence in owner_site.occurrences
        )
        base_rows.append((base_site, owner_site.owner, literals, owner_site.line))

    totals = Counter(row[0] for row in base_rows)
    seen: Counter[str] = Counter()
    sites: list[DimensionInventorySite] = []
    for base_site, owner, literals, line in base_rows:
        seen[base_site] += 1
        site = base_site
        if totals[base_site] > 1:
            site += f"#occurrence={seen[base_site]}"
        sites.append(DimensionInventorySite(site, owner, literals, line))
    return DimensionInventoryCase(path, tuple(sites))


def build_dimension_inventory_from_sources(
    sources: Mapping[Path, str],
) -> DimensionInventory:
    """Build an inventory from repo-relative case sources."""
    canonical_sources: list[tuple[Path, str]] = []
    seen: set[Path] = set()
    for path, source in sources.items():
        canonical = _canonical_case_path(path.as_posix(), "source path")
        if canonical in seen:
            raise DimensionInventoryError(
                f"duplicate dimension source path: {canonical.as_posix()}"
            )
        if not isinstance(source, str):
            raise DimensionInventoryError(
                f"dimension source {canonical.as_posix()} must be text"
            )
        seen.add(canonical)
        canonical_sources.append((canonical, source))
    canonical_sources.sort(key=lambda item: item[0].as_posix())

    cases: list[DimensionInventoryCase] = []
    source_end_lines: list[tuple[Path, int]] = []
    for path, source in canonical_sources:
        source_end_lines.append((path, source.count("\n") + 1))
        case = _case_inventory(path, source)
        if case is not None:
            cases.append(case)
    return DimensionInventory(tuple(cases), tuple(source_end_lines))


def collect_dimension_inventory(
    repo: Path, case_paths: Iterable[Path]
) -> DimensionInventory:
    """Read each manifest case and build its exact active-dimension sites."""
    paths = tuple(case_paths)
    if len(set(paths)) != len(paths):
        raise DimensionInventoryError(
            "manifest contains duplicate dimension case paths"
        )
    sources: dict[Path, str] = {}
    for path in paths:
        canonical = _canonical_case_path(path.as_posix(), "manifest case path")
        try:
            sources[canonical] = (repo / canonical).read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            raise DimensionInventoryError(
                f"cannot read dimension case {canonical.as_posix()}: {exc}"
            ) from exc
    return build_dimension_inventory_from_sources(sources)


def _canonical_case_path(raw: str, field_name: str) -> Path:
    if not isinstance(raw, str) or not raw:
        raise DimensionInventoryError(f"{field_name} must be a nonempty string")
    pure = PurePosixPath(raw)
    if (
        pure.is_absolute()
        or ".." in pure.parts
        or pure.as_posix() != raw
        or pure.suffix != ".tex"
    ):
        raise DimensionInventoryError(
            f"{field_name} must be a canonical repo-relative .tex path: {raw!r}"
        )
    return Path(*pure.parts)


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DimensionInventoryError(f"duplicate JSON field: {key!r}")
        result[key] = value
    return result


def _exact_fields(
    value: object, expected: set[str], field_name: str
) -> dict[str, object]:
    if not isinstance(value, dict):
        raise DimensionInventoryError(f"{field_name} must be an object")
    actual = set(value)
    if actual != expected:
        raise DimensionInventoryError(
            f"{field_name} fields must be exactly {', '.join(sorted(expected))}; "
            f"found {', '.join(sorted(actual)) or 'none'}"
        )
    return value


def _validate_duplicate_ordinals(
    path: Path, sites: tuple[DimensionInventorySite, ...]
) -> None:
    parsed: list[tuple[str, int | None]] = []
    for site in sites:
        match = _DUPLICATE_SUFFIX_RE.fullmatch(site.site)
        parsed.append(
            (match.group(1), int(match.group(2)))
            if match is not None
            else (site.site, None)
        )
    totals = Counter(base for base, _ in parsed)
    seen: Counter[str] = Counter()
    for base, ordinal in parsed:
        seen[base] += 1
        if totals[base] == 1 and ordinal is not None:
            raise DimensionInventoryError(
                f"{path.as_posix()}: unique site has a duplicate ordinal: {base}"
            )
        if totals[base] > 1 and ordinal != seen[base]:
            raise DimensionInventoryError(
                f"{path.as_posix()}: duplicate site ordinals for {base!r} must be "
                f"1 through {totals[base]} in source order"
            )


def parse_dimension_inventory(
    text: str, *, source_name: str = "dimension inventory"
) -> DimensionInventory:
    """Parse and strictly validate one version-2 inventory document."""
    try:
        raw = json.loads(text, object_pairs_hook=_unique_object)
    except json.JSONDecodeError as exc:
        raise DimensionInventoryError(
            f"cannot parse {source_name} as JSON: {exc}"
        ) from exc
    root = _exact_fields(raw, {"schema_version", "cases"}, source_name)
    schema_version = root["schema_version"]
    if (
        not isinstance(schema_version, int)
        or isinstance(schema_version, bool)
        or schema_version != DIMENSION_INVENTORY_SCHEMA_VERSION
    ):
        raise DimensionInventoryError(
            f"{source_name} schema_version must be exactly "
            f"{DIMENSION_INVENTORY_SCHEMA_VERSION}"
        )
    raw_cases = root["cases"]
    if not isinstance(raw_cases, dict):
        raise DimensionInventoryError(f"{source_name}.cases must be an object")
    if list(raw_cases) != sorted(raw_cases):
        raise DimensionInventoryError(
            f"{source_name}.cases paths must be in canonical sorted order"
        )

    cases: list[DimensionInventoryCase] = []
    for raw_path, raw_sites in raw_cases.items():
        path = _canonical_case_path(raw_path, f"{source_name}.cases path")
        if not isinstance(raw_sites, list) or not raw_sites:
            raise DimensionInventoryError(
                f"{source_name}.cases[{raw_path!r}] must be a nonempty array"
            )
        sites: list[DimensionInventorySite] = []
        site_names: set[str] = set()
        for index, raw_site in enumerate(raw_sites, 1):
            where = f"{source_name}.cases[{raw_path!r}][{index}]"
            fields = _exact_fields(raw_site, _SITE_FIELDS, where)
            site_name = fields["site"]
            if (
                not isinstance(site_name, str)
                or _SITE_KEY_RE.fullmatch(site_name) is None
                or any(character.isspace() for character in site_name)
            ):
                raise DimensionInventoryError(
                    f"{where}.site must be a normalized semantic site key"
                )
            if site_name in site_names:
                raise DimensionInventoryError(f"{where}.site duplicates {site_name!r}")
            site_names.add(site_name)
            raw_owner = fields["owner"]
            try:
                owner = DimensionOwner(raw_owner)
            except (TypeError, ValueError) as exc:
                raise DimensionInventoryError(
                    f"{where}.owner is not a dimension owner: {raw_owner!r}"
                ) from exc
            if owner not in _ACTIVE_OWNERS:
                raise DimensionInventoryError(
                    f"{where}.owner must describe an active case dimension"
                )
            raw_literals = fields["literals"]
            if not isinstance(raw_literals, list) or not raw_literals:
                raise DimensionInventoryError(
                    f"{where}.literals must be a nonempty array"
                )
            literals: list[str] = []
            for literal_index, literal in enumerate(raw_literals, 1):
                literal_where = f"{where}.literals[{literal_index}]"
                if (
                    not isinstance(literal, str)
                    or DIMENSION_RE.fullmatch(literal) is None
                    or normalize_dimension_literal(literal) != literal
                ):
                    raise DimensionInventoryError(
                        f"{literal_where} must be a normalized absolute TeX dimension"
                    )
                literals.append(literal)
            sites.append(DimensionInventorySite(site_name, owner, tuple(literals)))
        case_sites = tuple(sites)
        _validate_duplicate_ordinals(path, case_sites)
        cases.append(DimensionInventoryCase(path, case_sites))
    return DimensionInventory(tuple(cases))


def load_dimension_inventory(path: Path) -> DimensionInventory:
    """Read a required exact inventory, rejecting every I/O or schema failure."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise DimensionInventoryError(
            f"cannot read dimension inventory {path}: {exc}"
        ) from exc
    return parse_dimension_inventory(text, source_name=path.as_posix())


def format_dimension_inventory(inventory: DimensionInventory) -> str:
    """Serialize compact one-row-per-site canonical JSON."""
    lines = [
        "{",
        f'  "schema_version": {DIMENSION_INVENTORY_SCHEMA_VERSION},',
        '  "cases": {',
    ]
    for case_index, case in enumerate(inventory.cases):
        case_comma = "," if case_index + 1 < len(inventory.cases) else ""
        path_json = json.dumps(case.path.as_posix(), ensure_ascii=False)
        lines.append(f"    {path_json}: [")
        for site_index, site in enumerate(case.sites):
            site_comma = "," if site_index + 1 < len(case.sites) else ""
            row = {
                "site": site.site,
                "owner": site.owner.value,
                "literals": list(site.literals),
            }
            lines.append(
                "      "
                + json.dumps(row, ensure_ascii=False, separators=(", ", ": "))
                + site_comma
            )
        lines.append(f"    ]{case_comma}")
    lines.extend(("  }", "}"))
    return "\n".join(lines) + "\n"


def _stored_site(site: DimensionInventorySite) -> tuple[str, str, tuple[str, ...]]:
    return site.site, site.owner.value, site.literals


def _source_location(
    inventory: DimensionInventory, path: Path, site: DimensionInventorySite | None
) -> str:
    if site is not None and site.line is not None:
        return f"{path.as_posix()}:{site.line}"
    end_lines = dict(inventory.source_end_lines)
    if path in end_lines:
        return f"{path.as_posix()}:{end_lines[path]} (end of source)"
    return path.as_posix()


def validate_dimension_inventory(
    expected: DimensionInventory, actual: DimensionInventory
) -> None:
    """Reject the first path, site, owner, or literal-vector difference."""
    expected_cases = {case.path: case for case in expected.cases}
    actual_cases = {case.path: case for case in actual.cases}
    for path in sorted(
        set(expected_cases) | set(actual_cases), key=lambda item: item.as_posix()
    ):
        expected_case = expected_cases.get(path)
        actual_case = actual_cases.get(path)
        if expected_case is None:
            first = actual_case.sites[0] if actual_case is not None else None
            raise DimensionInventoryError(
                f"dimension inventory has no case for new source site at "
                f"{_source_location(actual, path, first)}"
            )
        if actual_case is None:
            raise DimensionInventoryError(
                f"dimension inventory expects {len(expected_case.sites)} site(s) in "
                f"{_source_location(actual, path, None)}, but the source has none"
            )
        limit = min(len(expected_case.sites), len(actual_case.sites))
        for index in range(limit):
            expected_site = expected_case.sites[index]
            actual_site = actual_case.sites[index]
            if _stored_site(expected_site) == _stored_site(actual_site):
                continue
            location = _source_location(actual, path, actual_site)
            if (
                expected_site.site == actual_site.site
                and expected_site.owner is actual_site.owner
            ):
                raise DimensionInventoryError(
                    f"dimension literal vector changed at {location} for "
                    f"{actual_site.site}: expected {list(expected_site.literals)!r}, "
                    f"found {list(actual_site.literals)!r}"
                )
            raise DimensionInventoryError(
                f"dimension owner site changed at {location} (site {index + 1}): "
                f"expected {_stored_site(expected_site)!r}, "
                f"found {_stored_site(actual_site)!r}"
            )
        if len(expected_case.sites) != len(actual_case.sites):
            actual_site = (
                actual_case.sites[limit] if limit < len(actual_case.sites) else None
            )
            raise DimensionInventoryError(
                f"dimension site count changed at "
                f"{_source_location(actual, path, actual_site)}: expected "
                f"{len(expected_case.sites)}, found {len(actual_case.sites)}"
            )


def validate_rmp_dimension_gate(
    repo: Path,
    case_paths: Iterable[Path],
    *,
    inventory_path: Path | None = None,
) -> DimensionReport:
    """Run aggregate ownership and exact-site checks as one production gate."""
    paths = tuple(case_paths)
    report = collect_dimension_report(repo, paths)
    validate_dimension_report(report)
    actual = collect_dimension_inventory(repo, paths)
    path = inventory_path or repo / DEFAULT_DIMENSION_INVENTORY
    expected = load_dimension_inventory(path)
    validate_dimension_inventory(expected, actual)
    return report


def format_dimension_inventory_counts(inventory: DimensionInventory) -> str:
    """Return stable counts for updater and review output."""
    return (
        f"cases {inventory.case_count} | sites {inventory.site_count} | "
        f"dimensions {inventory.dimension_count}"
    )
