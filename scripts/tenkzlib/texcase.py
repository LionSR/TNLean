"""Shared comment stripping and construct scanning for tenkz TeX sources."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable


_STATIC_CONTROL_WORD_NAME_RE = re.compile(r"(?:[^\W\d_]|[@:_])+")
PICTURE_ENVIRONMENT_NAMES = frozenset(
    {"tenkz", "tenkzcd", "tenkzfree", "tenkzlattice", "tenkzplanes"}
)
DRAWING_COMMAND_NAMES = frozenset({"tnpic", "tntree"})
DRAWING_CONSTRUCT_NAMES = PICTURE_ENVIRONMENT_NAMES | DRAWING_COMMAND_NAMES
PICTURE_EVENT_CONSTRUCT_NAMES = PICTURE_ENVIRONMENT_NAMES | {"tnpic"}


@dataclass
class Construct:
    name: str
    start: int
    end: int
    body: str
    line: int
    body_start: int


def is_control_word_start(source: str, position: int) -> bool:
    """Whether this backslash starts a TeX control word rather than ``\\``."""
    run_length = 1
    while position >= run_length and source[position - run_length] == "\\":
        run_length += 1
    return run_length % 2 == 1


def is_static_control_word_letter(character: str) -> bool:
    """Recognize a conservative letter across common LaTeX catcode modes."""
    return _STATIC_CONTROL_WORD_NAME_RE.fullmatch(character) is not None


def is_static_control_word_name(name: str) -> bool:
    """Whether a complete static spelling is one conservative control word."""
    return _STATIC_CONTROL_WORD_NAME_RE.fullmatch(name) is not None


def strip_comments(source: str) -> str:
    """Blank unescaped TeX comments while preserving offsets and lines."""
    output: list[str] = []
    for line in source.split("\n"):
        buffer = list(line)
        index = 0
        while index < len(buffer):
            if buffer[index] == "\\":
                index += 2
                continue
            if buffer[index] == "%":
                for tail in range(index, len(buffer)):
                    buffer[tail] = " "
                break
            index += 1
        output.append("".join(buffer))
    return "\n".join(output)


def match_group(
    source: str, index: int, open_character: str, close_character: str
) -> int:
    """Return the offset after a comment- and brace-aware group, or -1."""
    group_depth = 0
    brace_depth = 0
    while index < len(source):
        character = source[index]
        if character == "\\":
            index += 2
            continue
        if character == "%":
            newline = source.find("\n", index)
            if newline < 0:
                return -1
            index = newline + 1
            continue
        if character == open_character and (
            open_character == "{" or brace_depth == 0
        ):
            group_depth += 1
        elif character == close_character and (
            close_character == "}" or brace_depth == 0
        ):
            group_depth -= 1
            if group_depth == 0:
                return index + 1
        elif character == "{":
            brace_depth += 1
        elif character == "}":
            brace_depth -= 1
            if brace_depth < 0:
                return -1
        index += 1
    return -1


def following_group_span(
    source: str, position: int, opener: str, closer: str
) -> tuple[str, int] | None:
    """Return a following group's contents and ending offset."""
    while position < len(source) and source[position].isspace():
        position += 1
    if source[position : position + 1] != opener:
        return None
    end = match_group(source, position, opener, closer)
    if end == -1:
        return None
    return source[position + 1 : end - 1], end


def following_group(
    source: str, position: int, opener: str, closer: str
) -> str | None:
    """Return the contents of a group following optional whitespace."""
    group = following_group_span(source, position, opener, closer)
    return group[0] if group is not None else None


def top_level_options(options: str) -> list[tuple[str, str | None]]:
    """Parse one comma-separated option group without splitting nested values."""
    start = 0
    depths = {"{": 0, "[": 0, "(": 0}
    closing = {"}": "{", "]": "[", ")": "("}
    parts: list[str] = []
    index = 0
    while index < len(options):
        character = options[index]
        if character == "\\":
            index += 2
            continue
        if character in depths:
            depths[character] += 1
        elif character in closing:
            opener = closing[character]
            depths[opener] = max(0, depths[opener] - 1)
        elif character == "," and not any(depths.values()):
            parts.append(options[start:index])
            start = index + 1
        index += 1
    parts.append(options[start:])
    result: list[tuple[str, str | None]] = []
    for part in parts:
        key, separator, value = part.partition("=")
        key = re.sub(r"\s+", " ", key.strip())
        if key:
            result.append((key, value.strip() if separator else None))
    return result


def _find_env_end(
    source: str,
    name: str,
    position: int,
    ignored_control_spans: Iterable[tuple[int, int]] = (),
) -> re.Match[str] | None:
    """Find the depth-matched closing token for a tenkz environment."""
    ignored_control_spans = tuple(ignored_control_spans)
    token_pattern = re.compile(
        r"\\(begin|end)\s*\{" + re.escape(name) + r"\}"
    )
    depth = 1
    for token in token_pattern.finditer(source, position):
        if not is_control_word_start(source, token.start()):
            continue
        if any(start <= token.start() < end for start, end in ignored_control_spans):
            continue
        depth += 1 if token.group(1) == "begin" else -1
        if depth == 0:
            return token
    return None


def scan_constructs(
    source: str,
    ignored_control_spans: Iterable[tuple[int, int]] = (),
) -> list[Construct]:
    """Return drawing constructs in source order.

    Comments are blanked internally so offsets remain coordinates in the input
    while TeX-legal comment and whitespace splices around environment groups
    are recognized consistently by every caller.  A standalone ``tntree`` is
    a drawing construct but emits ``tree|picture=0``, not a picture event.
    """
    source = strip_comments(source)
    ignored_control_spans = tuple(ignored_control_spans)
    constructs: list[Construct] = []
    environment_pattern = re.compile(
        r"\\begin\s*\{("
        + "|".join(
            re.escape(name)
            for name in sorted(
                PICTURE_ENVIRONMENT_NAMES, key=len, reverse=True
            )
        )
        + r")\}"
    )
    for match in environment_pattern.finditer(source):
        if not is_control_word_start(source, match.start()):
            continue
        if any(start <= match.start() < end for start, end in ignored_control_spans):
            continue
        name = match.group(1)
        end_match = _find_env_end(
            source, name, match.end(), ignored_control_spans
        )
        end = end_match.end() if end_match else len(source)
        body_start = match.end()
        if source[body_start : body_start + 1] == "[":
            closed = match_group(source, body_start, "[", "]")
            if closed != -1:
                body_start = closed
        body_end = end_match.start() if end_match else len(source)
        constructs.append(
            Construct(
                name,
                match.start(),
                end,
                source[body_start:body_end],
                source.count("\n", 0, match.start()) + 1,
                body_start,
            )
        )
    command_pattern = re.compile(
        r"\\("
        + "|".join(
            re.escape(name)
            for name in sorted(DRAWING_COMMAND_NAMES, key=len, reverse=True)
        )
        + r")"
    )
    for match in command_pattern.finditer(source):
        if not is_control_word_start(source, match.start()):
            continue
        if (
            match.end() < len(source)
            and is_static_control_word_letter(source[match.end()])
        ):
            continue
        if any(start <= match.start() < end for start, end in ignored_control_spans):
            continue
        name = match.group(1)
        index = match.end()
        while index < len(source) and source[index] in " \t\n":
            index += 1
        if source[index : index + 1] == "[":
            closed = match_group(source, index, "[", "]")
            if closed == -1:
                continue
            index = closed
            while index < len(source) and source[index] in " \t\n":
                index += 1
        if source[index : index + 1] != "{":
            continue
        closed = match_group(source, index, "{", "}")
        if closed == -1:
            continue
        constructs.append(
            Construct(
                name,
                match.start(),
                closed,
                source[index + 1 : closed - 1],
                source.count("\n", 0, match.start()) + 1,
                index + 1,
            )
        )
    constructs.sort(key=lambda construct: construct.start)
    return constructs


def scan_picture_event_constructs(
    source: str,
    ignored_control_spans: Iterable[tuple[int, int]] = (),
) -> list[Construct]:
    """Return exactly the constructs that emit ``picture`` events."""
    return [
        construct
        for construct in scan_constructs(source, ignored_control_spans)
        if construct.name in PICTURE_EVENT_CONSTRUCT_NAMES
    ]
