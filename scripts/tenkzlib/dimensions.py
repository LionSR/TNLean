"""Classify and ratchet physical dimensions in the source-first RMP corpus."""

from __future__ import annotations

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
    in_comment: bool
    offset: int


@dataclass(frozen=True)
class DimensionReport:
    """All case and separately allowlisted book-layout dimensions."""

    cases: tuple[DimensionOccurrence, ...]
    book: tuple[DimensionOccurrence, ...]

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
    r"(?:pt|pc|bp|cm|mm|dd|cc|sp|in)",
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


@dataclass(frozen=True)
class _CommandGrammar:
    """The public xparse shape relevant to dimension ownership."""

    owner: DimensionOwner
    positional_group_counts: tuple[int, ...]
    accepts_star: bool = False
    accepts_options: bool = True


# Keep these arities in lockstep with the public definitions.  "tnwire" is
# the one conditional grammar: a closed wire takes no ends, while every other
# wire takes two.  The scanner does not validate invocations, but it must never
# claim more brace groups than a valid invocation can consume.
_COMMAND_GRAMMARS: Mapping[str, _CommandGrammar] = {
    "tnput": _CommandGrammar(DimensionOwner.LAYOUT, (3,)),       # O{} m m m
    "tnjoin": _CommandGrammar(DimensionOwner.ROUTE, (2,)),      # O{} m m
    "tnwire": _CommandGrammar(DimensionOwner.ROUTE, (0, 2)),    # O{} or O{} m m
    "tnedge": _CommandGrammar(DimensionOwner.ROUTE, (1,)),      # O{} m
    "tnarrow": _CommandGrammar(                                 # s O{} m
        DimensionOwner.ROUTE, (1,), accepts_star=True
    ),
}
_COMMAND_RE = re.compile(r"\\(" + "|".join(_COMMAND_GRAMMARS) + r")\b")
_OPTION_OWNER_RE = re.compile(
    r"\s*(?P<key>sheet\s+vector|row\s+vector|col\s+vector|pitch)\s*=",
    flags=re.IGNORECASE,
)
_OPTION_ENVIRONMENT_RE = re.compile(
    r"\\begin\s*\{\s*tenkz(?:cd|eq|free|lattice|planes)?\s*\}"
)
_OPTION_BRACKET_COMMAND_RE = re.compile(r"\\(?:tnpic|tntree)\b")
_OPTION_BRACE_COMMAND_RE = re.compile(r"\\tnset\b")
_FRAME_KEYS = {"sheet vector", "row vector", "col vector"}


@dataclass(frozen=True)
class _OwnerSpan:
    start: int
    end: int
    owner: DimensionOwner


@dataclass(frozen=True)
class _ActiveSource:
    """Comment-free TeX input plus original offsets for every retained byte."""

    text: str
    offsets: tuple[int, ...]


def _active_source(source: str) -> _ActiveSource:
    """Remove TeX comments as token splices while retaining source locations."""
    characters: list[str] = []
    offsets: list[int] = []
    index = 0
    while index < len(source):
        character = source[index]
        if character == "\\":
            characters.append(character)
            offsets.append(index)
            index += 1
            if index < len(source):
                characters.append(source[index])
                offsets.append(index)
                index += 1
            continue
        if character == "%":
            newline = source.find("\n", index)
            if newline < 0:
                break
            index = newline + 1
            # TeX discards the commented endline and ignores indentation at
            # the start of the next input line.  Tokens on the two physical
            # lines can therefore form one numeric/unit literal.
            while index < len(source) and source[index] in " \t":
                index += 1
            continue
        characters.append(character)
        offsets.append(index)
        index += 1
    return _ActiveSource("".join(characters), tuple(offsets))


def _skip_space(source: str, position: int) -> int:
    while position < len(source) and source[position].isspace():
        position += 1
    return position


def _is_control_word_start(source: str, position: int) -> bool:
    """Whether this backslash starts a TeX control word rather than ``\\``."""
    run_length = 1
    while position >= run_length and source[position - run_length] == "\\":
        run_length += 1
    return run_length % 2 == 1


def _command_spans(source: str) -> list[_OwnerSpan]:
    spans: list[_OwnerSpan] = []
    for command in _COMMAND_RE.finditer(source):
        if not _is_control_word_start(source, command.start()):
            continue
        grammar = _COMMAND_GRAMMARS[command.group(1)]
        position = _skip_space(source, command.end())
        if grammar.accepts_star and source[position : position + 1] == "*":
            position = _skip_space(source, position + 1)
        if grammar.accepts_options and source[position : position + 1] == "[":
            closed = match_group(source, position, "[", "]")
            if closed < 0:
                continue
            position = _skip_space(source, closed)
        for _ in range(max(grammar.positional_group_counts)):
            if source[position : position + 1] != "{":
                break
            closed = match_group(source, position, "{", "}")
            if closed < 0:
                break
            position = _skip_space(source, closed)
        spans.append(
            _OwnerSpan(
                command.start(), position, grammar.owner
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


def _option_group_spans(
    source: str, start: int, end: int
) -> list[_OwnerSpan]:
    spans: list[_OwnerSpan] = []
    segment_start = start
    depths = {"{": 0, "[": 0, "(": 0}
    closing = {"}": "{", "]": "[", ")": "("}
    segments: list[tuple[int, int]] = []
    index = start
    while index < end:
        character = source[index]
        if character == "\\":
            index += 2
            continue
        if character in depths:
            depths[character] += 1
        elif character in closing:
            opener = closing[character]
            depths[opener] = max(0, depths[opener] - 1)
        elif character == "," and not any(depths.values()):
            segments.append((segment_start, index))
            segment_start = index + 1
        index += 1
    segments.append((segment_start, end))
    for segment_start, segment_end in segments:
        option = _OPTION_OWNER_RE.match(source, segment_start, segment_end)
        if option is None:
            continue
        key = re.sub(r"\s+", " ", option.group("key").lower())
        owner = (
            DimensionOwner.FRAME if key in _FRAME_KEYS else DimensionOwner.METRIC
        )
        value_end = min(segment_end, _option_value_end(source, option.end()))
        spans.append(_OwnerSpan(option.end(), value_end, owner))
    return spans


def _option_spans(source: str) -> list[_OwnerSpan]:
    spans: list[_OwnerSpan] = []
    containers = (
        (_OPTION_ENVIRONMENT_RE, "[", "]"),
        (_OPTION_BRACKET_COMMAND_RE, "[", "]"),
        (_OPTION_BRACE_COMMAND_RE, "{", "}"),
    )
    for pattern, opener, closer in containers:
        for container in pattern.finditer(source):
            if not _is_control_word_start(source, container.start()):
                continue
            position = _skip_space(source, container.end())
            if source[position : position + 1] != opener:
                continue
            closed = match_group(source, position, opener, closer)
            if closed < 0:
                continue
            spans.extend(_option_group_spans(source, position + 1, closed - 1))
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
    if re.search(r"\b(?:pitch|metric|spacing|distance)\b", lowered):
        return DimensionOwner.METRIC
    if re.search(
        r"\b(?:sheet vector|row vector|col vector|projection|frame|offset)\b",
        lowered,
    ):
        return DimensionOwner.FRAME
    if re.search(r"\\tn(?:join|wire|edge|arrow)\b|\b(?:route|string)\b", lowered):
        return DimensionOwner.ROUTE
    if re.search(
        r"\\tnput\b|\b(?:composition|layout|width|height|length|radius|"
        r"diameter|wide|tall|long|thick)\b",
        lowered,
    ):
        return DimensionOwner.LAYOUT
    return None


def _comment_dimension_is_measurement(
    source: str,
    occurrence: re.Match[str],
    comment_start: int,
    comment_end: int,
) -> bool:
    """Reject unit-like prefixes in prose and disambiguate the word ``in``."""
    literal = occurrence.group(0).lower().rstrip()
    prefix = source[comment_start : occurrence.start()]
    suffix = source[occurrence.end() : comment_end]
    # In comments, a unit prefix inside an ordinary word (``3 special`` or
    # ``2 pts``) is prose. Active TeX keeps TeX's prefix interpretation.
    if re.match(r"[A-Za-z]", suffix):
        return False
    if not literal.endswith("in"):
        return True
    # A compact ``1in`` token or TeX's explicit ``true`` prefix is
    # unambiguously dimensional.  Only the spaced English-looking ``1 in``
    # form needs semantic context.
    if "true" in literal or re.search(r"\s+in$", literal) is None:
        return True
    # This is intentionally narrower than ``_comment_owner``: it asks whether
    # a local phrase governs this value, not whether the comment mentions an
    # owner somewhere. Thus "Figure 3 in the layout" remains prose.
    if re.search(
        r"(?:\\tn(?:join|wire|edge|arrow)\s+path|"
        r"\b(?:pitch(?:es)?|spacings?|distances?|clearances?|widths?|heights?|"
        r"lengths?|radii|radiuses?|diameters?|offsets?|routes?|strings?))"
        r"(?:(?:\s+(?:is|was|equals|measures|of))|(?:\s*[:=]))?\s*$",
        prefix,
        flags=re.IGNORECASE,
    ) is not None:
        return True
    if re.search(
        r"\b(?:(?:shifted|moved|translated|displaced)(?:\s+by)?|"
        r"measured|measures)\s*$",
        prefix,
        flags=re.IGNORECASE,
    ) is not None:
        return True
    return re.match(
        r"\s*(?:wide|tall|long|thick|high|deep|leftward|rightward|"
        r"north|south|east|west|upward|downward)\b",
        suffix,
        flags=re.IGNORECASE,
    ) is not None


def scan_case_dimensions(path: Path, source: str) -> tuple[DimensionOccurrence, ...]:
    """Classify every absolute dimension in one case source."""
    active = _active_source(source)
    # Dimension scanners consume ordinary character tokens across a commented
    # endline.  TeX control words do not: the percent terminates ``\tn`` in
    # ``\tn%...\nput``.  Keep ownership on an offset-preserving blanked view
    # while the numeric/unit recognizer uses the collapsed mapped view above.
    owner_source = strip_comments(source)
    owner_spans = _option_spans(owner_source) + _command_spans(owner_source)
    # A semantic option value is more specific than its containing command.
    owner_spans.sort(key=lambda span: span.end - span.start)
    comments = _comment_ranges(source)
    occurrences: list[DimensionOccurrence] = []
    for match in DIMENSION_RE.finditer(active.text):
        offset = active.offsets[match.start()]
        owner = next(
            (
                span.owner
                for span in owner_spans
                if span.start <= offset < span.end
            ),
            None,
        )
        occurrences.append(
            DimensionOccurrence(
                path=path,
                line=source.count("\n", 0, offset) + 1,
                literal=match.group(0),
                owner=owner,
                in_comment=False,
                offset=offset,
            )
        )
    for match in DIMENSION_RE.finditer(source):
        comment_range = next(
            (span for span in comments if span[0] <= match.start() < span[1]),
            None,
        )
        if comment_range is None or not _comment_dimension_is_measurement(
            source, match, comment_range[0], comment_range[1]
        ):
            continue
        comment = source[comment_range[0] : comment_range[1]]
        occurrences.append(
            DimensionOccurrence(
                path=path,
                line=source.count("\n", 0, match.start()) + 1,
                literal=match.group(0),
                owner=_comment_owner(comment),
                in_comment=True,
                offset=match.start(),
            )
        )
    return tuple(sorted(occurrences, key=lambda occurrence: occurrence.offset))


def scan_book_dimensions(path: Path, source: str) -> tuple[DimensionOccurrence, ...]:
    """Record separately allowlisted benchmark-book layout dimensions."""
    active = _active_source(source)
    return tuple(
        DimensionOccurrence(
            path=path,
            line=source.count("\n", 0, active.offsets[match.start()]) + 1,
            literal=match.group(0),
            owner=DimensionOwner.BOOK_LAYOUT,
            in_comment=False,
            offset=active.offsets[match.start()],
        )
        for match in DIMENSION_RE.finditer(active.text)
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
    return DimensionReport(tuple(cases), tuple(book))


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
