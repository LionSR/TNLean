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

    owner: DimensionOwner | None
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
    # Typed containers below are ownership barriers, not blanket LAYOUT
    # owners.  Their recognized physical option values receive narrower
    # spans; arbitrary dimensions in an object label/body remain unowned and
    # cannot inherit an enclosing route owner.
    "tnpic": _CommandGrammar(None, (1,)),                        # O{} m
    "tntree": _CommandGrammar(None, (1,)),                       # O{} m
    "tn": _CommandGrammar(None, (1,), accepts_star=True),        # s O{} m
    "tnX": _CommandGrammar(None, (1,)),                          # O{} m
    "tnfuse": _CommandGrammar(None, (1,)),                       # O{} m
    "tnsite": _CommandGrammar(None, (1,)),                       # O{} m
    "tndots": _CommandGrammar(None, (0,)),                       # O{}
    "tnghost": _CommandGrammar(                                 # m
        None, (1,), accepts_options=False
    ),
    "tnskip": _CommandGrammar(                                  # no arguments
        None, (0,), accepts_options=False
    ),
    "tnspan": _CommandGrammar(None, (2,)),                       # O{} m m
    "tncut": _CommandGrammar(None, (1,)),                        # O{} m
    "tnregion": _CommandGrammar(None, (1,)),                     # O{} m
    "tnset": _CommandGrammar(                                   # m
        None, (1,), accepts_options=False
    ),
    "tndeclareatom": _CommandGrammar(                           # m m
        None, (2,), accepts_options=False
    ),
    "tnmark": _CommandGrammar(None, (2,)),                       # O{} m m
    "tngroup": _CommandGrammar(None, (1,)),                      # O{} m
    "tndeclare": _CommandGrammar(                               # m m m
        None, (3,), accepts_options=False
    ),
    # Kernel sugar has no sanctioned physical value.  Keep it neutral rather
    # than letting its endpoints inherit an enclosing composition owner.
    "tnbond": _CommandGrammar(None, (2,)),                       # O{} m m
    "tnprose": _CommandGrammar(                                 # m
        None, (1,), accepts_options=False
    ),
    "tenkzkernel": _CommandGrammar(                             # no arguments
        None, (0,), accepts_options=False
    ),
}
# This is the physical subset of the public option registry, not the current
# corpus vocabulary.  Plane rise/slant and sheet sep are dimensionless ratios;
# out/in are angles.  Keeping key spelling and owner in one table prevents a
# future public length from being recognized lexically but assigned by a
# second, drifting owner list.  Every physical-key allowlist below must be a
# subset of this mapping; ``_validate_physical_option_key_sets`` enforces that
# invariant at import time.
_PHYSICAL_OPTION_KEY_OWNERS: Mapping[str, DimensionOwner] = {
    "pitch": DimensionOwner.METRIC,
    "radius": DimensionOwner.METRIC,
    "column sep": DimensionOwner.METRIC,
    "row sep": DimensionOwner.METRIC,
    "col vector": DimensionOwner.FRAME,
    "row vector": DimensionOwner.FRAME,
    "sheet vector": DimensionOwner.FRAME,
    "label shift": DimensionOwner.LAYOUT,
}


def _option_key_pattern(key: str) -> str:
    """Return a regex spelling of one space-normalized public option key."""
    return r"\s+".join(re.escape(word) for word in key.split())


_OPTION_OWNER_RE = re.compile(
    r"\s*(?P<key>"
    + "|".join(
        _option_key_pattern(key)
        for key in sorted(_PHYSICAL_OPTION_KEY_OWNERS, key=len, reverse=True)
    )
    + r")\s*=",
)
_OPTION_ENVIRONMENT_KEYS: Mapping[str, frozenset[str]] = {
    "tenkz": frozenset({"pitch"}),
    "tenkzcd": frozenset({"pitch", "radius", "column sep", "row sep"}),
    "tenkzfree": frozenset({"pitch"}),
    "tenkzlattice": frozenset(
        {"pitch", "col vector", "row vector", "sheet vector"}
    ),
    "tenkzplanes": frozenset(
        {"pitch", "col vector", "row vector", "sheet vector"}
    ),
}


@dataclass(frozen=True)
class _EnvironmentToken:
    """One active ``\\begin`` or ``\\end`` token and its pairing key."""

    kind: str
    name: str | None
    match_name: str
    start: int
    end: int


_PUBLIC_ENVIRONMENTS = frozenset((*_OPTION_ENVIRONMENT_KEYS, "tenkzeq"))
# A source-only scan cannot recover arbitrary catcode changes.  Treat Unicode
# letters plus LaTeX/expl3's conventional ``@``, ``:``, and ``_`` letters as
# one conservative control-word alphabet: refusing to split an ambiguous
# spelling is safer than assigning dimensions to a shorter public command.
_STATIC_CONTROL_WORD_NAME_RE = re.compile(r"(?:[^\W\d_]|[@:_])+")
_TEX_CONTROL_WORD_END = r"(?![^\W\d_]|[@:_])"
_ENVIRONMENT_CONTROL_RE = re.compile(
    r"\\(begin|end)" + _TEX_CONTROL_WORD_END
)
_PRIMITIVE_DEFINITION_RE = re.compile(
    r"\\(?:def|gdef|edef|xdef)" + _TEX_CONTROL_WORD_END
)
_LATEX_COMMAND_DEFINITION_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand|DeclareRobustCommand)"
    + _TEX_CONTROL_WORD_END
)
_LATEX_ENVIRONMENT_DEFINITION_RE = re.compile(
    r"\\(?:newenvironment|renewenvironment|provideenvironment)"
    + _TEX_CONTROL_WORD_END
)
_DOCUMENT_COMMAND_DEFINITION_RE = re.compile(
    r"\\(?:New|Renew|Provide|Declare)(?:Expandable)?DocumentCommand"
    + _TEX_CONTROL_WORD_END
)
_DOCUMENT_ENVIRONMENT_DEFINITION_RE = re.compile(
    r"\\(?:New|Renew|Provide|Declare)DocumentEnvironment"
    + _TEX_CONTROL_WORD_END
)
_ENVIRONMENT_NAME_RE = re.compile(r"[A-Za-z@:_][A-Za-z0-9@:_*.-]*")
_CSNAME_SPACE_RE = re.compile(r"\\space" + _TEX_CONTROL_WORD_END)


@dataclass(frozen=True)
class _OptionCommandGrammar:
    """Physical keys accepted by one bracket-option command."""

    accepts_star: bool
    physical_keys: frozenset[str]


_OPTION_BRACKET_COMMANDS: Mapping[str, _OptionCommandGrammar] = {
    # Picture/tree explicitly forward pitch; the three cell commands consume
    # label shift through /tenkz/cell.  Do not infer option families from the
    # registry's broad object scope: /tenkz/site rejects label shift today,
    # while tndots has no option slot in the public grammar.  Leaving both out
    # keeps malformed or undocumented dimensions unowned.
    "tnpic": _OptionCommandGrammar(False, frozenset({"pitch"})),
    "tntree": _OptionCommandGrammar(False, frozenset({"pitch"})),
    "tn": _OptionCommandGrammar(True, frozenset({"label shift"})),
    "tnX": _OptionCommandGrammar(False, frozenset({"label shift"})),
    "tnfuse": _OptionCommandGrammar(False, frozenset({"label shift"})),
}
_OPTION_BRACKET_COMMAND_RE = re.compile(
    r"\\("
    + "|".join(
        sorted(_OPTION_BRACKET_COMMANDS, key=len, reverse=True)
    )
    + r")"
    + _TEX_CONTROL_WORD_END
)
_OPTION_BRACE_COMMAND_RE = re.compile(r"\\tnset" + _TEX_CONTROL_WORD_END)
_SETUP_PHYSICAL_KEYS = frozenset({"pitch"})
_DECLARE_ATOM_RE = re.compile(r"\\tndeclareatom" + _TEX_CONTROL_WORD_END)
_KERNEL_DECLARE_RE = re.compile(r"\\tndeclare" + _TEX_CONTROL_WORD_END)


def _validate_physical_option_key_sets() -> None:
    """Reject allowlists that lack a corresponding physical-key owner."""
    key_sets = [
        *_OPTION_ENVIRONMENT_KEYS.values(),
        *(grammar.physical_keys for grammar in _OPTION_BRACKET_COMMANDS.values()),
        _SETUP_PHYSICAL_KEYS,
    ]
    unknown = set().union(*key_sets).difference(_PHYSICAL_OPTION_KEY_OWNERS)
    if unknown:
        raise RuntimeError(
            "physical option keys lack dimension owners: "
            f"{sorted(unknown)!r}"
        )


_validate_physical_option_key_sets()


@dataclass(frozen=True)
class _OwnerSpan:
    start: int
    end: int
    owner: DimensionOwner | None
    is_quarantine: bool = False


@dataclass(frozen=True)
class _ActiveSource:
    """Comment-free TeX input plus original offsets for every retained byte."""

    text: str
    offsets: tuple[int, ...]


@dataclass(frozen=True)
class _MandatoryArgument:
    """One xparse ``m`` argument and its complete source extent."""

    content_start: int
    content_end: int
    end: int


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


def _is_static_control_word_letter(character: str) -> bool:
    """Recognize a conservative letter across common LaTeX catcode modes."""
    return _STATIC_CONTROL_WORD_NAME_RE.fullmatch(character) is not None


def _control_sequence_name(source: str) -> str | None:
    """Return one literal control-sequence token, if ``source`` is exactly one."""
    if len(source) < 2 or source[0] != "\\":
        return None
    name = source[1:]
    if _is_static_control_word_letter(name[0]):
        if all(_is_static_control_word_letter(character) for character in name):
            return name
        return None
    return name if len(name) == 1 else None


def _csname_spelling(source: str, *, expand_space: bool) -> str:
    """Normalize the statically reproducible part of a ``\\csname`` spelling.

    Environment dispatch expands its token-list argument, so canonical
    ``\\space`` tokens become ordinary spaces before ``\\csname`` ignores
    them.  Kernel declaration names are first stringified with
    ``\\tl_to_str:n`` and therefore request whitespace removal only.
    """
    if expand_space:
        source = _CSNAME_SPACE_RE.sub(" ", source)
    return re.sub(r"\s+", "", _active_source(source).text)


def _following_mandatory_arguments(
    source: str, position: int, count: int
) -> list[_MandatoryArgument] | None:
    """Return following xparse ``m`` arguments, braced or one-token."""
    arguments: list[_MandatoryArgument] = []
    for _ in range(count):
        position = _skip_space(source, position)
        if position >= len(source):
            return None
        if source[position] == "{":
            closed = match_group(source, position, "{", "}")
            if closed < 0:
                return None
            argument = _MandatoryArgument(
                position + 1, closed - 1, closed
            )
        elif source[position] == "\\":
            if position + 1 >= len(source):
                return None
            token_end = position + 2
            if _is_static_control_word_letter(source[position + 1]):
                while token_end < len(source) and _is_static_control_word_letter(
                    source[token_end]
                ):
                    token_end += 1
            argument = _MandatoryArgument(position, token_end, token_end)
        elif (
            source[position] == "#"
            and position + 1 < len(source)
            and source[position + 1].isdigit()
        ):
            # Inside a macro replacement, ``#1`` denotes the substituted
            # parameter token list. Keep the marker and parameter number
            # together so an unbraced expandable argument is fail-closed.
            argument = _MandatoryArgument(position, position + 2, position + 2)
        else:
            argument = _MandatoryArgument(position, position + 1, position + 1)
        arguments.append(argument)
        position = argument.end
    return arguments


def _top_level_comma_segments(source: str) -> list[tuple[int, int]]:
    """Split a PGF list where only braces protect commas."""
    brace_depth = 0
    segments: list[tuple[int, int]] = []
    segment_start = 0
    index = 0
    while index < len(source):
        character = source[index]
        if character == "\\":
            index += 2
            continue
        if character == "{":
            brace_depth += 1
        elif character == "}":
            brace_depth = max(0, brace_depth - 1)
        elif character == "," and brace_depth == 0:
            segments.append((segment_start, index))
            segment_start = index + 1
        index += 1
    segments.append((segment_start, len(source)))
    return segments


def _environment_scope_spans(
    tokens: Iterable[_EnvironmentToken],
    names: frozenset[str] | None = None,
) -> list[tuple[int, int]]:
    """Depth-match selected environment tokens into lexical scopes."""
    openings: dict[str, list[_EnvironmentToken]] = {}
    spans: list[tuple[int, int]] = []
    for token in tokens:
        if (
            names is not None
            and token.name is not None
            and token.name not in names
        ):
            continue
        if token.kind == "begin":
            openings.setdefault(token.match_name, []).append(token)
        elif openings.get(token.match_name):
            opening = openings[token.match_name].pop()
            spans.append((opening.start, token.end))
    for stack in openings.values():
        spans.extend((opening.start, -1) for opening in stack)
    return spans


def _declared_atom_commands(
    source: str,
    owner_source: str,
    execution_mask_spans: Iterable[tuple[int, int]] = (),
) -> frozenset[str]:
    """Return dynamic spellings as neutral, source-wide barriers.

    Whether ``NewDocumentCommand`` succeeds depends on TeX's ambient control
    sequence table, which a source-only scanner cannot reconstruct.  Dynamic
    declarations therefore never grant dimension ownership here. Declarations
    stored inside known execution-mask spans are not executed and are excluded.
    """
    execution_mask_spans = tuple(execution_mask_spans)
    names: set[str] = set()
    for declaration in _DECLARE_ATOM_RE.finditer(owner_source):
        if (
            not _is_control_word_start(owner_source, declaration.start())
            or _position_in_spans(
                declaration.start(), execution_mask_spans
            )
        ):
            continue
        arguments = _following_mandatory_arguments(
            owner_source, declaration.end(), 2
        )
        if arguments is None:
            continue
        name_source = owner_source[
            arguments[0].content_start : arguments[0].content_end
        ].strip()
        name = _control_sequence_name(name_source)
        if name is not None:
            names.add(name)
    for declaration in _KERNEL_DECLARE_RE.finditer(owner_source):
        if (
            not _is_control_word_start(owner_source, declaration.start())
            or _position_in_spans(
                declaration.start(), execution_mask_spans
            )
        ):
            continue
        arguments = _following_mandatory_arguments(
            owner_source, declaration.end(), 3
        )
        if arguments is None:
            continue
        class_name = _active_source(
            source[
                arguments[0].content_start : arguments[0].content_end
            ]
        ).text.strip()
        if class_name != "atom":
            continue
        command_name = _csname_spelling(
            source[
                arguments[1].content_start : arguments[1].content_end
            ],
            expand_space=False,
        ).strip()
        if command_name.startswith("\\"):
            command_name = command_name[1:]
        if (
            _STATIC_CONTROL_WORD_NAME_RE.fullmatch(command_name) is not None
            or len(command_name) == 1
        ):
            names.add(command_name)
    return frozenset(names)


def _command_spans(
    source: str,
    declared_commands: Iterable[str],
    ignored_control_spans: Iterable[tuple[int, int]] = (),
) -> list[_OwnerSpan]:
    ignored_control_spans = tuple(ignored_control_spans)
    grammars = dict(_COMMAND_GRAMMARS)
    # Dynamic spellings are source-wide neutral barriers even though a source
    # scan cannot know whether an ambient-name collision rejected a declaration.
    # Their invocation extent still follows the declared public ``O{} m`` grammar.
    dynamic_names = frozenset(declared_commands).difference(grammars)
    command_names = frozenset(grammars).union(dynamic_names)
    pattern = re.compile(
        r"\\("
        + "|".join(
            re.escape(name)
            + (
                _TEX_CONTROL_WORD_END
                if _STATIC_CONTROL_WORD_NAME_RE.fullmatch(name) is not None
                else ""
            )
            for name in sorted(command_names, key=len, reverse=True)
        )
        + r")"
    )
    commands = [
        command
        for command in pattern.finditer(source)
        if _is_control_word_start(source, command.start())
        and not _position_in_spans(
            command.start(), ignored_control_spans
        )
    ]
    # Parse dynamic atoms first. Their exact public grammar is ``O{} m``;
    # command tokens consumed by the one label must not be rescanned, while a
    # later brace-delimited sibling remains active input.
    dynamic_spans: list[_OwnerSpan] = []
    for command in commands:
        name = command.group(1)
        if name not in dynamic_names or any(
            span.start <= command.start() < span.end
            for span in dynamic_spans
        ):
            continue
        position = _skip_space(source, command.end())
        if source[position : position + 1] == "[":
            closed = match_group(source, position, "[", "]")
            if closed < 0:
                position = len(source)
            else:
                position = _skip_space(source, closed)
        if position < len(source):
            arguments = _following_mandatory_arguments(source, position, 1)
            position = (
                len(source)
                if arguments is None
                else _skip_space(source, arguments[0].end)
            )
        dynamic_spans.append(
            _OwnerSpan(command.start(), position, None, True)
        )

    spans = list(dynamic_spans)
    for command in commands:
        name = command.group(1)
        if name in dynamic_names or any(
            span.start <= command.start() < span.end
            for span in dynamic_spans
        ):
            continue
        grammar = grammars[name]
        span_owner = grammar.owner
        is_quarantine = False
        position = _skip_space(source, command.end())
        if grammar.accepts_star and source[position : position + 1] == "*":
            position = _skip_space(source, position + 1)
        if grammar.accepts_options and source[position : position + 1] == "[":
            closed = match_group(source, position, "[", "]")
            if closed < 0:
                position = len(source)
                span_owner = None
                is_quarantine = True
            else:
                position = _skip_space(source, closed)
        for _ in range(max(grammar.positional_group_counts)):
            if source[position : position + 1] != "{":
                break
            closed = match_group(source, position, "{", "}")
            if closed < 0:
                position = len(source)
                span_owner = None
                is_quarantine = True
                break
            position = _skip_space(source, closed)
        spans.append(
            _OwnerSpan(
                command.start(), position, span_owner, is_quarantine
            )
        )
    return spans


def _option_value_end(source: str, position: int) -> int:
    position = _skip_space(source, position)
    if source[position : position + 1] == "{":
        closed = match_group(source, position, "{", "}")
        return len(source) if closed < 0 else closed
    brace_depth = 0
    index = position
    while index < len(source):
        character = source[index]
        if character == "\\":
            index += 2
            continue
        if character == "{":
            brace_depth += 1
        elif character == "}":
            if brace_depth == 0:
                return index
            brace_depth -= 1
        elif character == "," and brace_depth == 0:
            return index
        index += 1
    return index


def _option_group_spans(
    source: str,
    start: int,
    end: int,
    allowed_keys: frozenset[str] | None = None,
) -> list[_OwnerSpan]:
    """Classify one option group using TeX-spliced tokens and source offsets."""
    spans: list[_OwnerSpan] = []
    active = _active_source(source[start:end])
    option_source = active.text
    for segment_start, segment_end in _top_level_comma_segments(option_source):
        option = _OPTION_OWNER_RE.match(
            option_source, segment_start, segment_end
        )
        if option is None:
            continue
        key = re.sub(r"\s+", " ", option.group("key")).strip()
        if allowed_keys is not None and key not in allowed_keys:
            continue
        owner = _PHYSICAL_OPTION_KEY_OWNERS[key]
        value_end = min(
            segment_end, _option_value_end(option_source, option.end())
        )
        if option.end() >= len(active.offsets):
            source_start = end
        else:
            source_start = start + active.offsets[option.end()]
        if value_end <= option.end():
            source_end = source_start
        elif value_end > len(active.offsets):
            source_end = end
        else:
            source_end = start + active.offsets[value_end - 1] + 1
        spans.append(_OwnerSpan(source_start, source_end, owner))
    return spans


def _macro_replacement_spans(
    source: str,
    ignored_control_spans: Iterable[tuple[int, int]] = (),
) -> list[tuple[int, int]]:
    """Return definition extents whose tokens are inert until invocation."""
    ignored_control_spans = tuple(ignored_control_spans)
    spans: list[tuple[int, int]] = []
    definitions = sorted(
        (
            *(
                (definition.start(), "primitive", definition)
                for definition in _PRIMITIVE_DEFINITION_RE.finditer(source)
            ),
            *(
                (definition.start(), "latex command", definition)
                for definition in _LATEX_COMMAND_DEFINITION_RE.finditer(source)
            ),
            *(
                (definition.start(), "latex environment", definition)
                for definition in _LATEX_ENVIRONMENT_DEFINITION_RE.finditer(
                    source
                )
            ),
            *(
                (definition.start(), "xparse command", definition)
                for definition in _DOCUMENT_COMMAND_DEFINITION_RE.finditer(source)
            ),
            *(
                (definition.start(), "xparse environment", definition)
                for definition in _DOCUMENT_ENVIRONMENT_DEFINITION_RE.finditer(
                    source
                )
            ),
        ),
        key=lambda candidate: candidate[0],
    )

    def quarantine_unclosed_mandatory(
        position: int, definition_start: int
    ) -> None:
        position = _skip_space(source, position)
        if (
            source[position : position + 1] == "{"
            and match_group(source, position, "{", "}") < 0
        ):
            spans.append((definition_start, len(source)))

    for _, definition_kind, definition in definitions:
        if (
            not _is_control_word_start(source, definition.start())
            or _position_in_spans(
                definition.start(), ignored_control_spans
            )
            or any(
                start <= definition.start() < end for start, end in spans
            )
        ):
            continue
        if definition_kind == "primitive":
            position = definition.end()
            body_found = False
            while position < len(source):
                character = source[position]
                if character == "\\":
                    arguments = _following_mandatory_arguments(
                        source, position, 1
                    )
                    if arguments is None:
                        break
                    position = arguments[0].end
                    continue
                if (
                    character == "#"
                    and position + 1 < len(source)
                    and (
                        source[position + 1].isdigit()
                        or source[position + 1] == "#"
                    )
                ):
                    # Parameter markers belong to the definition header.
                    position += 2
                    continue
                if character == "#":
                    position += 1
                    continue
                if character != "{":
                    position += 1
                    continue
                closed = match_group(source, position, "{", "}")
                spans.append(
                    (
                        definition.start(),
                        len(source) if closed < 0 else closed,
                    )
                )
                body_found = True
                break
            if not body_found:
                spans.append((definition.start(), len(source)))
        elif definition_kind.startswith("latex"):
            position = _skip_space(source, definition.end())
            if source[position : position + 1] == "*":
                position = _skip_space(source, position + 1)
            names = _following_mandatory_arguments(source, position, 1)
            if names is None:
                quarantine_unclosed_mandatory(position, definition.start())
                continue
            position = _skip_space(source, names[0].end)
            malformed_option = False
            for _ in range(2):
                if source[position : position + 1] != "[":
                    break
                closed = match_group(source, position, "[", "]")
                if closed < 0:
                    spans.append((definition.start(), len(source)))
                    malformed_option = True
                    break
                position = _skip_space(source, closed)
            if malformed_option:
                continue
            body_count = 2 if definition_kind.endswith("environment") else 1
            bodies: list[_MandatoryArgument] = []
            for _ in range(body_count):
                following = _following_mandatory_arguments(
                    source, position, 1
                )
                if following is None:
                    quarantine_unclosed_mandatory(
                        position, definition.start()
                    )
                    break
                body = following[0]
                bodies.append(body)
                position = body.end
            if len(bodies) == body_count:
                spans.append((definition.start(), bodies[-1].end))
        else:
            position = definition.end()
            arguments: list[_MandatoryArgument] = []
            argument_count = (
                4 if definition_kind.endswith("environment") else 3
            )
            for _ in range(argument_count):
                following = _following_mandatory_arguments(
                    source, position, 1
                )
                if following is None:
                    quarantine_unclosed_mandatory(
                        position, definition.start()
                    )
                    break
                argument = following[0]
                arguments.append(argument)
                position = argument.end
            if len(arguments) == argument_count:
                spans.append((definition.start(), arguments[-1].end))
    return spans


def _position_in_spans(
    position: int, spans: Iterable[tuple[int, int]]
) -> bool:
    """Whether a source position lies inside any half-open span."""
    return any(start <= position < end for start, end in spans)


def _environment_tokens(
    source: str,
    owner_source: str,
    execution_mask_spans: Iterable[tuple[int, int]] | None = None,
) -> list[_EnvironmentToken]:
    """Parse simple environment names without joining split control words."""
    tokens: list[_EnvironmentToken] = []
    if execution_mask_spans is None:
        execution_mask_spans = _macro_replacement_spans(owner_source)
    execution_mask_spans = tuple(execution_mask_spans)
    for control in _ENVIRONMENT_CONTROL_RE.finditer(owner_source):
        if (
            not _is_control_word_start(owner_source, control.start())
            or _position_in_spans(control.start(), execution_mask_spans)
        ):
            continue
        arguments = _following_mandatory_arguments(
            owner_source, control.end(), 1
        )
        if arguments is None:
            continue
        argument = arguments[0]
        # LaTeX dispatch expands the name in ``\csname``.  Model canonical
        # spaces exactly; unresolved control sequences cannot safely grant a
        # public option owner, but matching spellings still form a neutral
        # quarantine so their bodies cannot inherit an enclosing owner.
        spelling = _csname_spelling(
            source[argument.content_start : argument.content_end],
            expand_space=True,
        )
        if _ENVIRONMENT_NAME_RE.fullmatch(spelling) is not None:
            name: str | None = spelling
            match_name = f"static:{spelling}"
        elif "\\" in spelling or "#" in spelling:
            name = None
            match_name = f"unresolved:{spelling}"
        else:
            continue
        tokens.append(
            _EnvironmentToken(
                control.group(1),
                name,
                match_name,
                control.start(),
                argument.end,
            )
        )
    return tokens


def _environment_spans(
    source: str,
    owner_source: str,
    execution_mask_spans: Iterable[tuple[int, int]] | None = None,
) -> list[_OwnerSpan]:
    """Return neutral barriers for public environments and malformed controls."""
    if execution_mask_spans is None:
        execution_mask_spans = _macro_replacement_spans(owner_source)
    execution_mask_spans = tuple(execution_mask_spans)
    tokens = _environment_tokens(
        source, owner_source, execution_mask_spans
    )
    spans = [
        _OwnerSpan(
            start,
            len(source) if end < 0 else end,
            None,
            end < 0,
        )
        for start, end in _environment_scope_spans(
            tokens, _PUBLIC_ENVIRONMENTS
        )
    ]
    # An unclosed environment-name argument cannot be resolved to a public
    # name, but it still consumes the remainder as one malformed control.
    for control in _ENVIRONMENT_CONTROL_RE.finditer(owner_source):
        if (
            not _is_control_word_start(owner_source, control.start())
            or _position_in_spans(control.start(), execution_mask_spans)
        ):
            continue
        position = _skip_space(owner_source, control.end())
        if owner_source[position : position + 1] != "{":
            continue
        if match_group(owner_source, position, "{", "}") < 0:
            spans.append(_OwnerSpan(control.start(), len(source), None, True))
    # Every environment that already participates in the barrier contract
    # needs the same fail-closed option boundary, even when its options have
    # no physical keys or its expandable name remains unresolved.
    for container in tokens:
        if (
            container.kind != "begin"
            or (
                container.name is not None
                and container.name not in _PUBLIC_ENVIRONMENTS
            )
        ):
            continue
        position = _skip_space(owner_source, container.end)
        if owner_source[position : position + 1] != "[":
            continue
        if match_group(owner_source, position, "[", "]") < 0:
            spans.append(_OwnerSpan(container.start, len(source), None, True))
    return spans


def _option_spans(
    source: str,
    owner_source: str,
    execution_mask_spans: Iterable[tuple[int, int]] | None = None,
) -> list[_OwnerSpan]:
    """Find public option containers without joining split control words."""
    if execution_mask_spans is None:
        execution_mask_spans = _macro_replacement_spans(owner_source)
    execution_mask_spans = tuple(execution_mask_spans)
    spans: list[_OwnerSpan] = []
    for container in _environment_tokens(
        source, owner_source, execution_mask_spans
    ):
        if (
            container.kind != "begin"
            or container.name not in _OPTION_ENVIRONMENT_KEYS
        ):
            continue
        position = _skip_space(owner_source, container.end)
        if owner_source[position : position + 1] != "[":
            continue
        closed = match_group(owner_source, position, "[", "]")
        if closed < 0:
            continue
        spans.extend(
            _option_group_spans(
                source,
                position + 1,
                closed - 1,
                _OPTION_ENVIRONMENT_KEYS[container.name],
            )
        )
    containers = (
        (_OPTION_BRACKET_COMMAND_RE, "[", "]"),
        (_OPTION_BRACE_COMMAND_RE, "{", "}"),
    )
    for pattern, opener, closer in containers:
        for container in pattern.finditer(owner_source):
            if (
                not _is_control_word_start(owner_source, container.start())
                or _position_in_spans(
                    container.start(), execution_mask_spans
                )
            ):
                continue
            position = _skip_space(owner_source, container.end())
            allowed_keys: frozenset[str] | None = None
            if pattern is _OPTION_BRACKET_COMMAND_RE:
                grammar = _OPTION_BRACKET_COMMANDS[container.group(1)]
                allowed_keys = grammar.physical_keys
                if (
                    grammar.accepts_star
                    and owner_source[position : position + 1] == "*"
                ):
                    position = _skip_space(owner_source, position + 1)
            elif pattern is _OPTION_BRACE_COMMAND_RE:
                allowed_keys = _SETUP_PHYSICAL_KEYS
            if owner_source[position : position + 1] != opener:
                continue
            closed = match_group(owner_source, position, opener, closer)
            if closed < 0:
                continue
            spans.extend(
                _option_group_spans(
                    source, position + 1, closed - 1, allowed_keys
                )
            )
    return spans


@dataclass(frozen=True)
class _ExecutionContext:
    """Stable definition, command, and shared execution-mask spans."""

    replacement_spans: tuple[tuple[int, int], ...]
    command_spans: tuple[_OwnerSpan, ...]
    mask_spans: tuple[tuple[int, int], ...]


def _execution_context(source: str, owner_source: str) -> _ExecutionContext:
    """Resolve mutually dependent masks by finite-state convergence."""
    declared_commands = _declared_atom_commands(source, owner_source)
    state = (declared_commands, (), ())
    seen = {state}
    # Every span boundary is a source offset.  The cycle check normally reaches
    # the fixed point in two or three rounds; this finite bound is a final guard.
    for _ in range(len(owner_source) + 2):
        declared_commands, replacement_spans, _ = state
        command_spans = tuple(
            _command_spans(
                owner_source, declared_commands, replacement_spans
            )
        )
        command_quarantines = tuple(
            (span.start, span.end)
            for span in command_spans
            if span.is_quarantine
        )
        next_replacement_spans = tuple(
            _macro_replacement_spans(
                owner_source, command_quarantines
            )
        )
        visible_declared_commands = _declared_atom_commands(
            source,
            owner_source,
            next_replacement_spans + command_quarantines,
        )
        # Recompute exactly: a declaration hidden by a transient replacement
        # span can become visible after the command quarantine that caused that
        # span stabilizes. Repeated full states below make genuine cycles fail
        # closed instead of silently retaining either side of the ambiguity.
        next_declared_commands = visible_declared_commands
        next_state = (
            next_declared_commands,
            next_replacement_spans,
            command_quarantines,
        )
        if next_state == state:
            return _ExecutionContext(
                next_replacement_spans,
                command_spans,
                next_replacement_spans + command_quarantines,
            )
        if next_state in seen:
            raise DimensionOwnershipError(
                "tenkz execution masks did not converge"
            )
        seen.add(next_state)
        state = next_state
    raise DimensionOwnershipError(
        "tenkz execution masks exceeded their source bound"
    )


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
    if re.search(
        r"\\tn(?:join|wire|edge|arrow)"
        + _TEX_CONTROL_WORD_END
        + r"|\b(?:route|string)\b",
        lowered,
    ):
        return DimensionOwner.ROUTE
    if re.search(
        r"\\tnput"
        + _TEX_CONTROL_WORD_END
        + r"|\b(?:composition|layout|width|height|length|radius|diameter|wide|"
        r"tall|long|thick)\b",
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
    context = _execution_context(source, owner_source)
    owner_spans = (
        _option_spans(source, owner_source, context.mask_spans)
        + list(context.command_spans)
        + _environment_spans(
            source, owner_source, context.mask_spans
        )
        + [
            _OwnerSpan(start, end, None, True)
            for start, end in context.replacement_spans
        ]
    )
    # A semantic option value is more specific than its containing command.
    # A malformed remainder has no trustworthy nested grammar, however, so
    # its neutral quarantine must win over every shorter span inside it.
    owner_spans.sort(
        key=lambda span: (
            0 if span.is_quarantine else 1,
            span.end - span.start,
        )
    )
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
