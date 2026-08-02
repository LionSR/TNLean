"""Classify and ratchet physical dimensions in the source-first RMP corpus."""

from __future__ import annotations

import json
import re
from collections import Counter
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Iterable, Mapping

from tenkzlib.texcase import match_group, strip_comments


class DimensionOwner(str, Enum):
    """The semantic boundary that owns a physical dimension."""

    METRIC = "metric"
    FRAME = "projection/frame"
    ROUTE = "route/string"
    LAYOUT = "composition/layout"
    BOOK_LAYOUT = "benchmark-book layout"


@dataclass(frozen=True)
class DimensionOccurrence:
    """One authored absolute TeX dimension and its classified owner."""

    path: Path
    line: int
    literal: str
    owner: DimensionOwner | None
    site: str | None
    in_comment: bool
    offset: int


@dataclass(frozen=True)
class DimensionReport:
    """All case and separately allowlisted book-layout dimensions."""

    cases: tuple[DimensionOccurrence, ...]
    book: tuple[DimensionOccurrence, ...]
    approved_cases: Mapping[tuple[str, str, str, str], int]

    @property
    def case_counts(self) -> Counter[DimensionOwner]:
        return Counter(
            occurrence.owner
            for occurrence in self.cases
            if not occurrence.in_comment and occurrence.owner is not None
        )

    @property
    def case_count(self) -> int:
        return sum(not occurrence.in_comment for occurrence in self.cases)

    @property
    def comment_count(self) -> int:
        return sum(occurrence.in_comment for occurrence in self.cases)

    @property
    def case_inventory(self) -> Counter[tuple[str, str, str, str]]:
        return case_dimension_inventory(self.cases)

    @property
    def book_counts(self) -> Counter[Path]:
        return Counter(occurrence.path for occurrence in self.book)


class DimensionOwnershipError(ValueError):
    """An RMP physical dimension escaped its owner or a ratchet increased."""


# Relative font spacing such as ``1em`` is deliberately outside this physical
# dimension contract.  Absolute TeX units, their legal whitespace, and TeX's
# optional ``true`` prefix are caught even when a future case stops using
# millimetres.  The one lexical ambiguity, English prose using ``in`` as a
# preposition, is resolved only while scanning comments below.
DIMENSION_RE = re.compile(
    r"(?<![0-9_.])"
    r"[-+]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)"
    r"(?:\s*true)?\s*"
    r"(?:pt|pc|bp|cm|mm|dd|cc|sp|in)\b",
    flags=re.IGNORECASE,
)

CASE_DIMENSION_CEILING = 926
CASE_OWNER_CEILINGS: Mapping[DimensionOwner, int] = {
    DimensionOwner.METRIC: 0,
    DimensionOwner.FRAME: 0,
    DimensionOwner.ROUTE: 396,
    DimensionOwner.LAYOUT: 530,
}
CASE_COMMENT_CEILING = 0
BOOK_LAYOUT_ALLOWLIST: Mapping[Path, int] = {
    Path("docs/tenkz/rmp-benchmark.tex"): 4,
    Path("docs/tenkz/tenkzrmpbenchmark.sty"): 24,
}
CASE_DIMENSION_INVENTORY = Path("tests/tenkz/rmp/dimension-ownership.json")

_COMMAND_OWNERS: Mapping[str, DimensionOwner] = {
    "tnput": DimensionOwner.LAYOUT,
    "tnjoin": DimensionOwner.ROUTE,
    "tnwire": DimensionOwner.ROUTE,
    "tnedge": DimensionOwner.ROUTE,
    "tnarrow": DimensionOwner.ROUTE,
}
_COMMAND_RE = re.compile(r"\\(" + "|".join(_COMMAND_OWNERS) + r")\b")
_OPTION_OWNER_RE = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"(?P<key>sheet\s+vector|row\s+vector|col\s+vector|pitch)\s*=",
    flags=re.IGNORECASE,
)
_FRAME_KEYS = {"sheet vector", "row vector", "col vector"}

_COMMENT_OWNER_PATTERNS: tuple[tuple[DimensionOwner, re.Pattern[str]], ...] = (
    (
        DimensionOwner.METRIC,
        re.compile(
            r"\b(?:pitch(?:es)?|metrics?|spacings?|distances?)\b",
            re.IGNORECASE,
        ),
    ),
    (
        DimensionOwner.FRAME,
        re.compile(
            r"\b(?:sheet vectors?|row vectors?|col vectors?|projections?|frames?|"
            r"offsets?|shifts?|shifted|moves?|moved|displacements?|displaced)\b",
            re.IGNORECASE,
        ),
    ),
    (
        DimensionOwner.ROUTE,
        re.compile(
            r"\\tn(?:join|wire|edge|arrow)\b(?:\s+path)?|\b(?:routes?|strings?)\b",
            re.IGNORECASE,
        ),
    ),
    (
        DimensionOwner.LAYOUT,
        re.compile(
            r"\\tnput\b|\b(?:compositions?|layouts?|widths?|heights?|lengths?|"
            r"radii|radiuses?|diameters?|wide|tall|long|thick)\b",
            re.IGNORECASE,
        ),
    ),
)


@dataclass(frozen=True)
class _OwnerSpan:
    start: int
    end: int
    owner: DimensionOwner
    site: str


def _skip_space(source: str, position: int) -> int:
    while position < len(source) and source[position].isspace():
        position += 1
    return position


def _command_spans(source: str) -> list[_OwnerSpan]:
    spans: list[_OwnerSpan] = []
    for ordinal, command in enumerate(_COMMAND_RE.finditer(source), start=1):
        position = _skip_space(source, command.end())
        if source[position : position + 1] == "[":
            closed = match_group(source, position, "[", "]")
            if closed < 0:
                continue
            position = _skip_space(source, closed)
        while source[position : position + 1] == "{":
            closed = match_group(source, position, "{", "}")
            if closed < 0:
                break
            position = _skip_space(source, closed)
        spans.append(
            _OwnerSpan(
                command.start(),
                position,
                _COMMAND_OWNERS[command.group(1)],
                f"command:{command.group(1)}:{ordinal}",
            )
        )
    return spans


def _option_value_end(source: str, position: int) -> int:
    position = _skip_space(source, position)
    if source[position : position + 1] == "{":
        closed = match_group(source, position, "{", "}")
        return len(source) if closed < 0 else closed
    depths = {"{": 0, "[": 0, "(": 0}
    closing = {"}": "{", "]": "[", ")": "("}
    index = position
    while index < len(source):
        character = source[index]
        if character == "\\":
            index += 2
            continue
        if character in depths:
            depths[character] += 1
        elif character in closing:
            opener = closing[character]
            if depths[opener] == 0:
                return index
            depths[opener] -= 1
        elif character == "," and not any(depths.values()):
            return index
        index += 1
    return index


def _option_spans(source: str) -> list[_OwnerSpan]:
    spans: list[_OwnerSpan] = []
    for ordinal, option in enumerate(_OPTION_OWNER_RE.finditer(source), start=1):
        key = re.sub(r"\s+", " ", option.group("key").lower())
        owner = (
            DimensionOwner.FRAME if key in _FRAME_KEYS else DimensionOwner.METRIC
        )
        spans.append(
            _OwnerSpan(
                option.end(),
                _option_value_end(source, option.end()),
                owner,
                f"option:{key}:{ordinal}",
            )
        )
    return spans


def _comment_ranges(source: str) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    line_start = 0
    for line in source.splitlines(keepends=True):
        index = 0
        while index < len(line):
            if line[index] == "\\":
                index += 2
                continue
            if line[index] == "%":
                ranges.append((line_start + index, line_start + len(line)))
                break
            index += 1
        line_start += len(line)
    return ranges


def _comment_owner(comment: str) -> DimensionOwner | None:
    lowered = re.sub(r"\s+", " ", comment.lower())
    for owner, pattern in _COMMENT_OWNER_PATTERNS:
        if pattern.search(lowered):
            return owner
    return None


def _comment_measurement_owner_before(
    source: str,
    comment_start: int,
    occurrence_start: int,
) -> DimensionOwner | None:
    """Return an owner only for a measurement phrase immediately before a value."""
    prefix = re.sub(r"\s+", " ", source[comment_start:occurrence_start].lower())
    suffix = re.compile(r"\s*(?:=|is|equals?|measures?)?\s*$", re.IGNORECASE)
    for owner, pattern in _COMMENT_OWNER_PATTERNS:
        if any(suffix.fullmatch(prefix[match.end() :]) for match in pattern.finditer(prefix)):
            return owner
    return None


def _comment_inch_followed_by_prose(
    source: str,
    occurrence: re.Match[str],
    comment_end: int,
) -> bool:
    if re.search(r"in\s*$", occurrence.group(0), flags=re.IGNORECASE) is None:
        return False
    tail = source[occurrence.end() : comment_end]
    return re.match(r"\s+(?!plus\b|minus\b)[A-Za-z]", tail, re.IGNORECASE) is not None


def scan_case_dimensions(path: Path, source: str) -> tuple[DimensionOccurrence, ...]:
    """Classify every absolute dimension in one case source."""
    active = strip_comments(source)
    owner_spans = _option_spans(active) + _command_spans(active)
    # A semantic option value is more specific than its containing command.
    owner_spans.sort(key=lambda span: span.end - span.start)
    comments = _comment_ranges(source)
    occurrences: list[DimensionOccurrence] = []
    site_counts: Counter[str] = Counter()
    for match in DIMENSION_RE.finditer(source):
        comment_range = next(
            (span for span in comments if span[0] <= match.start() < span[1]),
            None,
        )
        if comment_range is not None:
            comment = source[comment_range[0] : comment_range[1]]
            owner = _comment_owner(comment)
            if _comment_inch_followed_by_prose(source, match, comment_range[1]):
                # A later owner word can belong to prose ("3 in the layout").
                # Require a local measurement phrase before an ambiguous inch.
                owner = _comment_measurement_owner_before(
                    source, comment_range[0], match.start()
                )
                if owner is None:
                    continue
            in_comment = True
            site = "comment"
        else:
            owner_span = next(
                (
                    span
                    for span in owner_spans
                    if span.start <= match.start() < span.end
                ),
                None,
            )
            owner = None if owner_span is None else owner_span.owner
            if owner_span is None:
                site = None
            else:
                site_counts[owner_span.site] += 1
                site = (
                    f"{owner_span.site}:dimension:{site_counts[owner_span.site]}"
                )
            in_comment = False
        occurrences.append(
            DimensionOccurrence(
                path=path,
                line=source.count("\n", 0, match.start()) + 1,
                literal=match.group(0),
                owner=owner,
                site=site,
                in_comment=in_comment,
                offset=match.start(),
            )
        )
    return tuple(occurrences)


def scan_book_dimensions(path: Path, source: str) -> tuple[DimensionOccurrence, ...]:
    """Record separately allowlisted benchmark-book layout dimensions."""
    return tuple(
        DimensionOccurrence(
            path=path,
            line=source.count("\n", 0, match.start()) + 1,
            literal=match.group(0),
            owner=DimensionOwner.BOOK_LAYOUT,
            site="benchmark-book",
            in_comment=False,
            offset=match.start(),
        )
        for match in DIMENSION_RE.finditer(strip_comments(source))
    )


def _normalize_literal(literal: str) -> str:
    return re.sub(r"\s+", "", literal.lower())


def case_dimension_inventory(
    occurrences: Iterable[DimensionOccurrence],
) -> Counter[tuple[str, str, str, str]]:
    """Count active dimensions by path, semantic owner, and normalized literal."""
    return Counter(
        (
            occurrence.path.as_posix(),
            occurrence.owner.value,
            occurrence.site or "unclassified",
            _normalize_literal(occurrence.literal),
        )
        for occurrence in occurrences
        if not occurrence.in_comment and occurrence.owner is not None
    )


def read_dimension_inventory(repo: Path) -> Counter[tuple[str, str, str, str]]:
    """Read the reviewed active-dimension inventory committed with the corpus."""
    path = repo / CASE_DIMENSION_INVENTORY
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise DimensionOwnershipError(
            f"cannot read dimension inventory {path}: {exc}"
        ) from exc
    try:
        payload = json.loads(source)
    except json.JSONDecodeError as exc:
        raise DimensionOwnershipError(
            f"invalid dimension inventory JSON: {path}: {exc}"
        ) from exc
    if (
        not isinstance(payload, dict)
        or payload.get("version") != 1
        or not isinstance(payload.get("occurrences"), list)
    ):
        raise DimensionOwnershipError(f"invalid dimension inventory schema: {path}")
    inventory: Counter[tuple[str, str, str, str]] = Counter()
    for row in payload["occurrences"]:
        if (
            not isinstance(row, list)
            or len(row) != 5
            or not all(isinstance(value, str) for value in row[:4])
            or not isinstance(row[4], int)
            or row[4] <= 0
        ):
            raise DimensionOwnershipError(f"invalid dimension inventory row: {row!r}")
        key = (row[0], row[1], row[2], row[3])
        if key in inventory:
            raise DimensionOwnershipError(f"duplicate dimension inventory row: {key!r}")
        inventory[key] = row[4]
    return inventory


def write_dimension_inventory(
    path: Path,
    inventory: Mapping[tuple[str, str, str, str], int],
) -> None:
    """Write a deterministic inventory for intentional ratchet review."""
    rows = [
        json.dumps([source, owner, site, literal, count])
        for (source, owner, site, literal), count in sorted(inventory.items())
    ]
    body = ",\n".join(f"    {row}" for row in rows)
    path.write_text(
        '{\n  "version": 1,\n  "occurrences": [\n'
        + body
        + "\n  ]\n}\n",
        encoding="utf-8",
    )


def collect_dimension_report(
    repo: Path, case_paths: Iterable[Path]
) -> DimensionReport:
    """Read the manifest-owned cases and the fixed benchmark-book allowlist."""
    cases: list[DimensionOccurrence] = []
    for relative in case_paths:
        source = (repo / relative).read_text(encoding="utf-8")
        cases.extend(scan_case_dimensions(relative, source))
    book: list[DimensionOccurrence] = []
    for relative in BOOK_LAYOUT_ALLOWLIST:
        source = (repo / relative).read_text(encoding="utf-8")
        book.extend(scan_book_dimensions(relative, source))
    return DimensionReport(
        tuple(cases),
        tuple(book),
        read_dimension_inventory(repo),
    )


def _location(occurrence: DimensionOccurrence) -> str:
    return f"{occurrence.path.as_posix()}:{occurrence.line}: {occurrence.literal}"


def validate_dimension_report(report: DimensionReport) -> None:
    """Reject unowned dimensions and any increase above the frozen ratchets."""
    problems: list[str] = []
    unowned = [
        occurrence
        for occurrence in report.cases
        if not occurrence.in_comment and occurrence.owner is None
    ]
    if unowned:
        problems.append(
            "unowned case dimension(s): "
            + ", ".join(_location(occurrence) for occurrence in unowned)
        )
    added = report.case_inventory - Counter(report.approved_cases)
    removed = Counter(report.approved_cases) - report.case_inventory
    if added:
        problems.append(
            "unapproved case dimension(s): "
            + ", ".join(
                f"{path}: {literal} ({owner}, {site}, {count})"
                for (path, owner, site, literal), count in sorted(added.items())
            )
        )
    if removed:
        problems.append(
            "dimension inventory retains removed occurrence(s): "
            + ", ".join(
                f"{path}: {literal} ({owner}, {site}, {count})"
                for (path, owner, site, literal), count in sorted(removed.items())
            )
        )
    if report.case_count > CASE_DIMENSION_CEILING:
        problems.append(
            f"case dimensions increased to {report.case_count} "
            f"(ceiling {CASE_DIMENSION_CEILING})"
        )
    counts = report.case_counts
    for owner, ceiling in CASE_OWNER_CEILINGS.items():
        if counts[owner] > ceiling:
            problems.append(
                f"{owner.value} dimensions increased to {counts[owner]} "
                f"(ceiling {ceiling})"
            )
    if report.comment_count > CASE_COMMENT_CEILING:
        problems.append(
            f"comment dimensions increased to {report.comment_count} "
            f"(ceiling {CASE_COMMENT_CEILING})"
        )
    book_counts = report.book_counts
    for path, allowed in BOOK_LAYOUT_ALLOWLIST.items():
        actual = book_counts[path]
        if actual != allowed:
            problems.append(
                f"{path.as_posix()} has {actual} benchmark-book layout "
                f"dimensions (allowlist requires exactly {allowed})"
            )
    unexpected_book_paths = set(book_counts).difference(BOOK_LAYOUT_ALLOWLIST)
    if unexpected_book_paths:
        problems.append(
            "unexpected benchmark-book dimension path(s): "
            + ", ".join(sorted(path.as_posix() for path in unexpected_book_paths))
        )
    if problems:
        raise DimensionOwnershipError("\n".join(problems))


def format_dimension_report(report: DimensionReport) -> str:
    """Return the stable one-line ownership summary used by the RMP driver."""
    counts = report.case_counts
    return (
        f"RMP dimensions: cases {report.case_count} | "
        f"metric {counts[DimensionOwner.METRIC]} | "
        f"projection/frame {counts[DimensionOwner.FRAME]} | "
        f"route/string {counts[DimensionOwner.ROUTE]} | "
        f"composition/layout {counts[DimensionOwner.LAYOUT]} | "
        f"comments {report.comment_count} | "
        f"benchmark-book layout {len(report.book)}"
    )
