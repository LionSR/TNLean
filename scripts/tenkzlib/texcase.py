"""Shared comment stripping and construct scanning for tenkz TeX sources."""

from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass
class Construct:
    name: str
    start: int
    end: int
    body: str
    line: int
    body_start: int


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


def _find_env_end(
    source: str, name: str, position: int
) -> re.Match[str] | None:
    """Find the depth-matched closing token for a tenkz environment."""
    token_pattern = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for token in token_pattern.finditer(source, position):
        depth += 1 if token.group(1) == "begin" else -1
        if depth == 0:
            return token
    return None


def scan_constructs(source: str) -> list[Construct]:
    """Return picture-producing constructs in source order."""
    constructs: list[Construct] = []
    environment_pattern = re.compile(
        r"\\begin\{(tenkz(?:eq|cd|lattice|free|planes)?)\}"
    )
    for match in environment_pattern.finditer(source):
        name = match.group(1)
        end_match = _find_env_end(source, name, match.end())
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
    for match in re.finditer(r"\\tnpic\b", source):
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
                "tnpic",
                match.start(),
                closed,
                source[index + 1 : closed - 1],
                source.count("\n", 0, match.start()) + 1,
                index + 1,
            )
        )
    constructs.sort(key=lambda construct: construct.start)
    return constructs
