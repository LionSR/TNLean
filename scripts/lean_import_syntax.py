"""Shared lexical helpers for one-line Lean import-only files."""

from __future__ import annotations

import re

NAME_SEGMENT = r"[A-Za-z_][A-Za-z0-9_']*"
MODULE_NAME = rf"{NAME_SEGMENT}(?:\.{NAME_SEGMENT})*"
IMPORT_COMMAND_RE = re.compile(rf"import\s+({MODULE_NAME})")


def strip_lean_comments(source: str) -> tuple[str, str | None]:
    """Remove nested block and line comments, or return a parse error."""
    output: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        pair = source[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    output.append("\n")
                index += 1
        elif pair == "/-":
            block_depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            if newline == -1:
                index = len(source)
            else:
                output.append("\n")
                index = newline + 1
        else:
            output.append(source[index])
            index += 1
    if block_depth:
        return "".join(output), "unterminated block comment"
    return "".join(output), None


def pure_import_modules(source: str) -> tuple[list[str], str | None]:
    """Return modules in a nonempty import-only source, or its rejection reason."""
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return [], error
    commands = [line.strip() for line in uncommented.splitlines() if line.strip()]
    if not commands:
        return [], "file contains no import commands"
    modules: list[str] = []
    for line_number, command in enumerate(commands, start=1):
        match = IMPORT_COMMAND_RE.fullmatch(command)
        if match is None:
            return [], (
                "contains non-import Lean code after comments are removed "
                f"(command {line_number}: {command!r})"
            )
        modules.append(match.group(1))
    return modules, None
