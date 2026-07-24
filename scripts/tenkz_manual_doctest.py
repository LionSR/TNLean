#!/usr/bin/env python3
"""Compile every displayed tenkz manual example as a standalone document."""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from tenkzlib.texcase import match_group, strip_comments


ROOT = Path(__file__).resolve().parents[1]
MANUAL_DIR = ROOT / "docs" / "tenkz"
MANUAL = MANUAL_DIR / "manual2.tex"
CHAPTERS = ROOT / "docs" / "tenkz" / "chapters2"
REGISTRY = ROOT / "tex" / "tenkz" / "tenkz-language-registry.tex"
REFERENCE = CHAPTERS / "generated-language-reference.tex"
DISPLAY_ENVIRONMENTS = ("tnexample", "tnmultiples", "Verbatim")
TEX_PRIMITIVE_CONDITIONALS = (
    "if", "ifcat", "ifnum", "ifdim", "ifodd", "ifvmode", "ifhmode",
    "ifmmode", "ifinner", "ifvoid", "ifhbox", "ifvbox", "ifx", "ifeof",
    "iftrue", "iffalse", "ifcase", "ifdefined", "ifcsname", "iffontchar",
    "ifincsname",
)
LATEX_CORE_CONDITIONAL_FALLBACK = ("if@twocolumn",)


@cache
def _latex_format_conditionals() -> tuple[str, ...]:
    known = set(LATEX_CORE_CONDITIONAL_FALLBACK)
    if not shutil.which("kpsewhich") or not shutil.which("xelatex"):
        return tuple(sorted(known))
    lookup = subprocess.run(
        ["kpsewhich", "latex.ltx"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        timeout=15,
    )
    source = Path(lookup.stdout.strip())
    if lookup.returncode != 0 or not source.is_file():
        return tuple(sorted(known))
    candidates = sorted(
        set(re.findall(r"\\(if[A-Za-z@]+)", source.read_text(encoding="utf-8")))
    )
    with tempfile.TemporaryDirectory(prefix="tenkz-format-conditionals-") as tmp:
        work = Path(tmp)
        probe = work / "probe.tex"
        lines = [r"\documentclass{article}"]
        lines.extend(
            rf"\typeout{{TENKZ-COND-{index}="
            rf"\expandafter\meaning\csname {name}\endcsname}}"
            for index, name in enumerate(candidates)
        )
        lines.append(r"\stop")
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        result = subprocess.run(
            [
                "xelatex",
                "-interaction=batchmode",
                f"-output-directory={work}",
                probe.as_posix(),
            ],
            text=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=30,
        )
        log = work / "probe.log"
        if result.returncode != 0 or not log.is_file():
            return tuple(sorted(known))
        meanings = {
            int(index): meaning.strip()
            for index, meaning in re.findall(
                r"^TENKZ-COND-(\d+)=(.*)$",
                log.read_text(encoding="utf-8", errors="replace"),
                re.MULTILINE,
            )
        }
    primitive_meanings = {rf"\{name}" for name in TEX_PRIMITIVE_CONDITIONALS}
    known.update(
        name
        for index, name in enumerate(candidates)
        if meanings.get(index) in primitive_meanings
    )
    return tuple(sorted(known))


@dataclass(frozen=True)
class Example:
    label: str
    source: Path
    line: int
    document: str
    coverage_marker: str | None = None


def _is_escaped(text: str, offset: int) -> bool:
    backslashes = 0
    cursor = offset - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


def _strip_tex_comments(text: str) -> str:
    return strip_comments(text)


def _skip_space_and_comments(text: str, offset: int) -> int:
    while offset < len(text):
        if text[offset].isspace():
            offset += 1
        elif text[offset] == "%" and not _is_escaped(text, offset):
            newline = text.find("\n", offset)
            if newline < 0:
                return len(text)
            offset = newline + 1
        else:
            break
    return offset


def _read_optional_argument(text: str, offset: int) -> tuple[int, str | None]:
    offset = _skip_space_and_comments(text, offset)
    if offset == len(text) or text[offset] != "[":
        return offset, None
    end = match_group(text, offset, "[", "]")
    if end < 0:
        raise ValueError("unterminated or unbalanced optional environment argument")
    return end, _strip_tex_comments(text[offset + 1 : end - 1])


def _split_top_level(text: str) -> list[str]:
    pieces: list[str] = []
    start = 0
    brace_depth = 0
    for index, character in enumerate(text):
        escaped = _is_escaped(text, index)
        if character == "{" and not escaped:
            brace_depth += 1
        elif character == "}" and not escaped:
            brace_depth -= 1
        elif character == "," and brace_depth == 0:
            pieces.append(text[start:index].strip())
            start = index + 1
        if brace_depth < 0:
            raise ValueError("unbalanced option group")
    if brace_depth:
        raise ValueError("unbalanced option group")
    pieces.append(text[start:].strip())
    return pieces


def _read_braced(text: str, offset: int) -> tuple[int, str]:
    while offset < len(text) and text[offset].isspace():
        offset += 1
    if offset == len(text) or text[offset] != "{":
        raise ValueError("expected braced group")
    end = match_group(text, offset, "{", "}")
    if end < 0:
        raise ValueError("unterminated braced group")
    return end, text[offset + 1 : end - 1]


def _multiple_variants(options: str | None) -> list[tuple[str, str]]:
    if options is None:
        raise ValueError("tnmultiples requires a variants option")
    variants_value = None
    for option in _split_top_level(options):
        key, separator, value = option.partition("=")
        if separator and key.strip() == "variants":
            variants_value = value.strip()
            break
    if variants_value is None:
        raise ValueError("tnmultiples requires a variants option")
    end, variants_group = _read_braced(variants_value, 0)
    if variants_value[end:].strip():
        raise ValueError("unexpected text after tnmultiples variants")

    variants: list[tuple[str, str]] = []
    for entry in _split_top_level(variants_group):
        offset, label = _read_braced(entry, 0)
        offset, style = _read_braced(entry, offset)
        if entry[offset:].strip():
            raise ValueError("unexpected text after tnmultiples variant")
        variants.append((label, style))
    if not variants:
        raise ValueError("tnmultiples variants list is empty")
    return variants


@cache
def _registry_vocabulary() -> tuple[list[str], list[str]]:
    registry = strip_comments(REGISTRY.read_text(encoding="utf-8"))
    commands = re.findall(
        r"\\__tenkz_language_registry_command:nnnnn\s*\{([^{}]+)\}", registry
    )
    environments = re.findall(
        r"\\__tenkz_language_registry_environment:nnnn\s*\{([^{}]+)\}", registry
    )
    return commands, environments


def _is_tenkz_verbatim(body: str, source_dir: Path) -> bool:
    commands, environments = _registry_vocabulary()
    environment_pattern = "|".join(re.escape(environment) for environment in environments)
    packages, _ = _extract_usepackages(body, source_dir)
    scan = _mask_nonexecuted_tokens(strip_comments(body))
    environment_matches = re.finditer(
        rf"\\begin\{{(?:{environment_pattern})\}}", scan
    )
    return bool(
        any("tenkz" in _package_names(package) for package in packages)
        or any(_has_executable_command(body, command) for command in commands)
        or any(not _is_escaped(scan, match.start()) for match in environment_matches)
    )


def _is_commented(text: str, offset: int) -> bool:
    line_start = text.rfind("\n", 0, offset) + 1
    line = text[line_start:offset]
    for index, character in enumerate(line):
        if character == "%" and not _is_escaped(line, index):
            return True
    return False


def _find_uncommented(text: str, marker: str, offset: int) -> int:
    while True:
        found = text.find(marker, offset)
        if found < 0 or not _is_commented(text, found):
            return found
        offset = found + len(marker)


def _find_control_word(text: str, name: str, offset: int) -> int:
    pattern = re.compile(rf"\\{re.escape(name)}(?![A-Za-z@])")
    while match := pattern.search(text, offset):
        if not _is_commented(text, match.start()) and not _is_escaped(
            text, match.start()
        ):
            return match.start()
        offset = match.end()
    return -1


def _mask_inline_verbatim(text: str) -> str:
    masked = list(text)
    offset = 0
    verb_pattern = re.compile(r"\\verb(?![A-Za-z@])")
    while match := verb_pattern.search(text, offset):
        start = match.start()
        if _is_escaped(text, start):
            offset = match.end()
            continue
        delimiter_offset = start + len(r"\verb")
        if delimiter_offset < len(text) and text[delimiter_offset] == "*":
            delimiter_offset += 1
        if delimiter_offset >= len(text):
            break
        delimiter = text[delimiter_offset]
        if delimiter.isspace() or delimiter.isalnum():
            offset = delimiter_offset
            continue
        line_end = text.find("\n", delimiter_offset + 1)
        if line_end < 0:
            line_end = len(text)
        end = text.find(delimiter, delimiter_offset + 1, line_end)
        if end < 0:
            offset = delimiter_offset + 1
            continue
        for index in range(start, end + 1):
            if masked[index] != "\n":
                masked[index] = " "
        offset = end + 1
    return "".join(masked)


def _usepackage_ranges(body: str, source_dir: Path) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    offset = 0
    marker = r"\usepackage"
    executable = _mask_inert_tex(body, source_dir)
    scan_body = _mask_nonexecuted_tokens(executable)
    while (start := _find_control_word(scan_body, "usepackage", offset)) >= 0:
        cursor = _skip_space_and_comments(body, start + len(marker))
        if cursor < len(body) and body[cursor] == "[":
            cursor, _ = _read_optional_argument(body, cursor)
        cursor = _skip_space_and_comments(body, cursor)
        end, _ = _read_braced(body, cursor)
        ranges.append((start, end))
        offset = end
    return ranges


def _extract_usepackages(body: str, source_dir: Path) -> tuple[list[str], str]:
    ranges = _usepackage_ranges(body, source_dir)
    packages = [body[start:end].strip() for start, end in ranges]
    chunks: list[str] = []
    offset = 0
    for start, end in ranges:
        chunks.append(body[offset:start])
        chunks.append("\n" * body[start:end].count("\n"))
        offset = end
    chunks.append(body[offset:])
    return packages, "".join(chunks)


def _package_names(declaration: str) -> list[str]:
    cursor = _skip_space_and_comments(declaration, len(r"\usepackage"))
    if cursor < len(declaration) and declaration[cursor] == "[":
        cursor, _ = _read_optional_argument(declaration, cursor)
    cursor = _skip_space_and_comments(declaration, cursor)
    _, names = _read_braced(declaration, cursor)
    return [name.strip() for name in strip_comments(names).split(",")]


def _find_environment_end(text: str, environment: str, offset: int) -> re.Match[str] | None:
    pattern = re.compile(
        rf"^[ \t]*\\end\{{{re.escape(environment)}\}}[ \t]*$",
        re.MULTILINE,
    )
    return pattern.search(text, offset)


def _mask_display_environments(text: str) -> str:
    masked = list(text)
    pattern = re.compile(
        r"^[ \t]*\\begin\{(" + "|".join(DISPLAY_ENVIRONMENTS) + r")\}",
        re.MULTILINE,
    )
    offset = 0
    while match := pattern.search(text, offset):
        end = _find_environment_end(text, match.group(1), match.end())
        if end is None:
            break
        for index in range(match.start(), end.end()):
            if masked[index] != "\n":
                masked[index] = " "
        offset = end.end()
    return "".join(masked)


def _blank_range(masked: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if masked[index] != "\n":
            masked[index] = " "


def _mask_false_branches(
    text: str, inherited_conditionals: tuple[str, ...] = ()
) -> str:
    masked = list(text)
    scan = _display_comment_scan(text)
    start_scan = _display_comment_scan(
        _mask_macro_definitions(text, strict=False)
    )
    newif_pattern = re.compile(
        r"\\newif\s*\\(if[A-Za-z@]+)(?![A-Za-z@])"
    )
    newif_matches = list(newif_pattern.finditer(start_scan))
    let_pattern = re.compile(
        r"\\let\s*\\(if[A-Za-z@]+)\s*=?\s*\\(if[A-Za-z@]*)"
        r"(?![A-Za-z@])"
    )
    let_matches = list(let_pattern.finditer(start_scan))
    declaration_operands = {
        match.start(group) - 1
        for match in (*newif_matches, *let_matches)
        for group in range(1, len(match.groups()) + 1)
    }
    false_tokens = list(re.finditer(r"\\iffalse(?![A-Za-z@])", start_scan))
    for token in false_tokens:
        if (
            masked[token.start()] != "\\"
            or token.start() in declaration_operands
            or start_scan[token.start() : token.end()] != token.group(0)
            or _is_escaped(scan, token.start())
        ):
            continue
        active_newifs = [
            match
            for match in newif_matches
            if match.start() < token.start() and masked[match.start()] == "\\"
        ]
        active_lets = [
            match
            for match in let_matches
            if match.start() < token.start() and masked[match.start()] == "\\"
        ]
        declared_conditionals = [match.group(1) for match in active_newifs]
        known_conditionals = set(
            (
                *TEX_PRIMITIVE_CONDITIONALS,
                *_latex_format_conditionals(),
                *inherited_conditionals,
                *declared_conditionals,
            )
        )
        while True:
            additions = {
                match.group(1)
                for match in active_lets
                if match.group(2) in known_conditionals
            } - known_conditionals
            if not additions:
                break
            known_conditionals.update(additions)
        tokens = list(
            re.finditer(
                r"\\(?:"
                + "|".join(sorted(known_conditionals, key=len, reverse=True))
                + r"|fi)(?![A-Za-z@])",
                scan[token.start() :],
            )
        )
        depth = 1
        cursor = 1
        while cursor < len(tokens) and depth:
            nested = tokens[cursor]
            nested_start = token.start() + nested.start()
            if (
                nested_start not in declaration_operands
                and not _is_escaped(scan, nested_start)
            ):
                depth += -1 if nested.group(0) == r"\fi" else 1
            cursor += 1
        end = (
            token.start() + tokens[cursor - 1].end()
            if depth == 0
            else len(text)
        )
        _blank_range(masked, token.start(), end)
    return "".join(masked)


def _tex_search_roots(source_dir: Path) -> list[tuple[Path, bool]]:
    roots = [
        (source_dir, True),
        (MANUAL_DIR, True),
        (ROOT / "tex" / "tenkz", True),
    ]
    for entry in os.environ.get("TEXINPUTS", "").split(":"):
        recursive = entry.endswith("//")
        normalized = entry.removesuffix("//")
        if normalized:
            roots.append((Path(normalized), recursive))
    unique: dict[Path, bool] = {}
    for root, recursive in roots:
        if root.is_dir():
            resolved = root.resolve()
            unique[resolved] = unique.get(resolved, False) or recursive
    return list(unique.items())


def _resolve_tex_file(relative: Path, source_dir: Path) -> Path | None:
    for root, recursive in _tex_search_roots(source_dir):
        if (root / relative).is_file():
            return (root / relative).resolve()
        if recursive:
            candidate = next(
                (
                    path
                    for path in root.rglob(relative.as_posix())
                    if path.is_file()
                ),
                None,
            )
            if candidate is not None:
                return candidate.resolve()
    if shutil.which("kpsewhich"):
        lookup = subprocess.run(
            ["kpsewhich", relative.as_posix()],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=15,
        )
        resolved = Path(lookup.stdout.strip())
        if lookup.returncode == 0 and resolved.is_file():
            return resolved.resolve()
    return None


def _tex_file_exists(relative: Path, source_dir: Path) -> bool:
    return _resolve_tex_file(relative, source_dir) is not None


def _mask_inactive_file_branches(
    text: str,
    source_dir: Path,
    inherited_conditionals: tuple[str, ...] = (),
) -> str:
    masked = list(text)
    pattern = re.compile(r"\\IfFileExists(?![A-Za-z@])")
    offset = 0
    while True:
        current = "".join(masked)
        structural = _mask_macro_definitions(
            _mask_false_branches(current, inherited_conditionals), strict=False
        )
        scan = _mask_nonexecuted_tokens(_display_comment_scan(structural))
        match = pattern.search(scan, offset)
        if match is None:
            break
        if _is_escaped(scan, match.start()):
            offset = match.end()
            continue
        cursor = _skip_space_and_comments(scan, match.end())
        file_start = cursor
        file_end, filename = _read_braced(scan, file_start)
        true_start = _skip_space_and_comments(scan, file_end)
        true_end, _ = _read_braced(scan, true_start)
        false_start = _skip_space_and_comments(scan, true_end)
        false_end, _ = _read_braced(scan, false_start)
        normalized_filename = re.sub(r"\s+", "", strip_comments(filename))
        relative = Path(normalized_filename)
        if _tex_file_exists(relative, source_dir):
            active_start, active_end = true_start, true_end
            _blank_range(masked, match.start(), true_start + 1)
            _blank_range(masked, true_end - 1, false_end)
        else:
            active_start, active_end = false_start, false_end
            _blank_range(masked, match.start(), false_start + 1)
            _blank_range(masked, false_end - 1, false_end)
        active = current[active_start + 1 : active_end - 1]
        masked[active_start + 1 : active_end - 1] = (
            _mask_inactive_file_branches(
                active, source_dir, inherited_conditionals
            )
        )
        offset = false_end
    return "".join(masked)


def _display_comment_scan(text: str) -> str:
    return strip_comments(
        _mask_inline_verbatim(_mask_display_environments(text))
    )


def _mask_macro_definitions(text: str, *, strict: bool = True) -> str:
    masked = list(text)
    scan = _display_comment_scan(text)
    pattern = re.compile(
        r"\\(?:(?:new|renew|provide)command|(?:g|e|x)?def)\*?(?![A-Za-z@])"
    )
    offset = 0
    while match := pattern.search(scan, offset):
        if _is_escaped(scan, match.start()):
            offset = match.end()
            continue
        cursor = _skip_space_and_comments(scan, match.end())
        is_command = "command" in match.group(0)
        if is_command:
            if cursor < len(scan) and scan[cursor] == "{":
                cursor, _ = _read_braced(scan, cursor)
            else:
                control = re.match(r"\\(?:[A-Za-z@]+|.)", scan[cursor:])
                if control is None:
                    offset = match.end()
                    continue
                cursor += control.end()
            for _ in range(2):
                cursor = _skip_space_and_comments(scan, cursor)
                if cursor < len(scan) and scan[cursor] == "[":
                    cursor, _ = _read_optional_argument(scan, cursor)
        else:
            control = re.match(r"\\(?:[A-Za-z@]+|.)", scan[cursor:])
            if control is None:
                offset = match.end()
                continue
            cursor += control.end()
            while cursor < len(scan) and scan[cursor] != "{":
                cursor += 1
        cursor = _skip_space_and_comments(scan, cursor)
        if cursor >= len(scan) or scan[cursor] != "{":
            offset = match.end()
            continue
        try:
            end, _ = _read_braced(scan, cursor)
        except ValueError:
            if strict:
                raise
            offset = match.end()
            continue
        _blank_range(masked, cursor, end)
        offset = end
    return "".join(masked)


def _mask_inert_tex(
    text: str,
    source_dir: Path,
    inherited_conditionals: tuple[str, ...] = (),
) -> str:
    selected_file_branches = _mask_inactive_file_branches(
        text, source_dir, inherited_conditionals
    )
    without_false_branches = _mask_false_branches(
        selected_file_branches, inherited_conditionals
    )
    without_macros = _mask_macro_definitions(without_false_branches)
    return without_macros


def _mask_nonexecuted_tokens(text: str) -> str:
    masked = list(_mask_inline_verbatim(text))
    scan = "".join(masked)
    string_pattern = re.compile(r"\\string\s*\\(?:[A-Za-z@]+|.)")
    for match in string_pattern.finditer(scan):
        for index in range(match.start(), match.end()):
            if masked[index] != "\n":
                masked[index] = " "
    scan = "".join(masked)
    offset = 0
    while (start := _find_control_word(scan, "detokenize", offset)) >= 0:
        cursor = _skip_space_and_comments(scan, start + len(r"\detokenize"))
        if cursor >= len(scan) or scan[cursor] != "{":
            offset = cursor
            continue
        end, _ = _read_braced(scan, cursor)
        _blank_range(masked, start, end)
        offset = end
    return "".join(masked)


def _has_executable_command(text: str, command: str) -> bool:
    scan = _mask_nonexecuted_tokens(strip_comments(text))
    pattern = re.compile(rf"\\{re.escape(command)}(?![A-Za-z@:_])")
    return any(not _is_escaped(scan, match.start()) for match in pattern.finditer(scan))


def _instrument_command(
    document: str, command: str, source_dir: Path
) -> tuple[str, str]:
    selected = next(
        (
            (start, end)
            for start, end in _usepackage_ranges(document, source_dir)
            if "tenkz" in _package_names(document[start:end])
        ),
        None,
    )
    if selected is None:
        raise ValueError(f"reference for \\{command} does not load tenkz")
    scan = _mask_nonexecuted_tokens(
        strip_comments(_mask_inert_tex(document, source_dir))
    )
    pattern = re.compile(rf"\\{re.escape(command)}(?![A-Za-z@:_])")
    invocation = next(
        (
            match.start()
            for match in pattern.finditer(scan)
            if not _is_escaped(scan, match.start())
        ),
        None,
    )
    if invocation is None:
        raise ValueError(f"reference for \\{command} has no executable invocation")
    marker = f"TENKZ-DOCTEST-EXECUTED-{command}"
    original = f"tenkzdoctestoriginal{command}"
    instrumentation = "\n".join(
        [
            rf"\expandafter\let\csname {original}\endcsname\{command}",
            rf"\def\{command}{{\typeout{{{marker}}}\csname {original}\endcsname}}",
        ]
    )
    return (
        document[:invocation]
        + instrumentation
        + "\n"
        + document[invocation:],
        marker,
    )


def _source_label(path: Path) -> str:
    try:
        relative = path.relative_to(CHAPTERS)
    except ValueError:
        relative = Path(path.name)
    source_key = relative.with_suffix("").as_posix()
    return source_key.encode("utf-8").hex()


def _variant_definitions(variant_style: str) -> list[str]:
    return [
        rf"\pgfqkeys{{/tenkz/grid}}{{variant/.style={{{variant_style}}}}}",
        rf"\pgfqkeys{{/tenkz/cell}}{{variant/.style={{{variant_style}}}}}",
    ]


def _standalone_document(
    body: str, source_dir: Path, variant_style: str | None = None
) -> str:
    body = body.strip()
    scan_body = _mask_nonexecuted_tokens(body)
    has_document_class = _find_control_word(scan_body, "documentclass", 0) >= 0
    has_document = (
        _find_uncommented(scan_body, r"\begin{document}", 0) >= 0
        and _find_uncommented(scan_body, r"\end{document}", 0) >= 0
    )
    if has_document_class:
        if not has_document:
            raise ValueError("displayed document class has no complete document body")
        if variant_style is None:
            return body + "\n"
        begin = _find_uncommented(scan_body, r"\begin{document}", 0)
        definitions = "\n".join(_variant_definitions(variant_style)) + "\n"
        return body[:begin] + definitions + body[begin:] + "\n"

    preamble, content = _extract_usepackages(body, source_dir)
    if not any("tenkz" in _package_names(package) for package in preamble):
        preamble.append(r"\usepackage{tenkz}")
    if variant_style is not None:
        preamble.extend(_variant_definitions(variant_style))
    return "\n".join(
        [
            r"\documentclass{article}",
            *preamble,
            r"\pagestyle{empty}",
            r"\begin{document}",
            content,
            r"\end{document}",
            "",
        ]
    )


def extract_displayed_examples(
    path: Path, inherited_conditionals: tuple[str, ...] = ()
) -> list[Example]:
    text = path.read_text(encoding="utf-8")
    scan_text = _mask_inert_tex(
        text, path.parent, inherited_conditionals
    )
    begin_pattern = re.compile(
        r"^[ \t]*\\begin\{(" + "|".join(DISPLAY_ENVIRONMENTS) + r")\}",
        re.MULTILINE,
    )
    examples: list[Example] = []
    offset = 0
    ordinal = 0
    while match := begin_pattern.search(scan_text, offset):
        if _is_commented(scan_text, match.start()):
            offset = match.end()
            continue
        environment = match.group(1)
        body_start, options = _read_optional_argument(text, match.end())
        end_marker = rf"\end{{{environment}}}"
        end_match = _find_environment_end(text, environment, body_start)
        if end_match is None:
            line = text.count("\n", 0, match.start()) + 1
            raise ValueError(f"{path}:{line}: missing {end_marker}")
        body_end = end_match.start()
        body = text[body_start:body_end].strip()
        offset = end_match.end()
        if environment == "Verbatim" and not _is_tenkz_verbatim(
            body, path.parent
        ):
            continue
        line = text.count("\n", 0, match.start()) + 1
        variants = (
            _multiple_variants(options)
            if environment == "tnmultiples"
            else [(None, None)]
        )
        for variant_index, (_, variant_style) in enumerate(variants, start=1):
            ordinal += 1
            suffix = f"-variant-{variant_index}" if environment == "tnmultiples" else ""
            examples.append(
                Example(
                    label=f"manual-{_source_label(path)}-{ordinal}{suffix}",
                    source=path,
                    line=line,
                    document=_standalone_document(
                        body, path.parent, variant_style
                    ),
                )
            )
    return examples


def displayed_examples() -> list[Example]:
    examples: list[Example] = []
    for path, inherited_conditionals in _manual_source_contexts():
        examples.extend(extract_displayed_examples(path, inherited_conditionals))
    return examples


def _conditionals_before(
    text: str,
    offset: int,
    inherited_conditionals: tuple[str, ...],
    source_dir: Path,
) -> tuple[str, ...]:
    selected_file_branches = _mask_inactive_file_branches(
        text, source_dir, inherited_conditionals
    )
    executable = _display_comment_scan(
        _mask_macro_definitions(
            _mask_false_branches(
                selected_file_branches, inherited_conditionals
            ),
            strict=False,
        )
    )
    newif_pattern = re.compile(r"\\newif\s*\\(if[A-Za-z@]+)(?![A-Za-z@])")
    let_pattern = re.compile(
        r"\\let\s*\\(if[A-Za-z@]+)\s*=?\s*\\(if[A-Za-z@]*)"
        r"(?![A-Za-z@])"
    )
    newifs = [
        match
        for match in newif_pattern.finditer(executable)
        if match.start() < offset
    ]
    lets = [
        match for match in let_pattern.finditer(executable) if match.start() < offset
    ]
    known = set(
        (
            *TEX_PRIMITIVE_CONDITIONALS,
            *_latex_format_conditionals(),
            *inherited_conditionals,
        )
    )
    known.update(match.group(1) for match in newifs)
    while True:
        additions = {
            match.group(1) for match in lets if match.group(2) in known
        } - known
        if not additions:
            break
        known.update(additions)
    return tuple(sorted(known - set(TEX_PRIMITIVE_CONDITIONALS)))


def _manual_source_contexts() -> list[tuple[Path, tuple[str, ...]]]:
    pending = [(MANUAL, ())]
    visited: dict[Path, tuple[str, ...]] = {}
    input_pattern = re.compile(r"\\input(?![A-Za-z@])")
    while pending:
        source, inherited_conditionals = pending.pop()
        if source in visited:
            continue
        visited[source] = inherited_conditionals
        raw = source.read_text(encoding="utf-8")
        text = strip_comments(
            _mask_inline_verbatim(
                _mask_display_environments(
                    _mask_inert_tex(
                        raw, source.parent, inherited_conditionals
                    )
                )
            )
        )
        for match in input_pattern.finditer(text):
            if _is_escaped(text, match.start()):
                continue
            cursor = match.end()
            while cursor < len(text) and text[cursor].isspace():
                cursor += 1
            if cursor < len(text) and text[cursor] == "{":
                cursor, target = _read_braced(text, cursor)
            else:
                target_match = re.match(r"[^\s%{}]+", text[cursor:])
                if target_match is None:
                    raise ValueError(f"{source}: input command has no filename")
                target = target_match.group(0)
            relative = Path(target)
            if not relative.suffix:
                relative = relative.with_suffix(".tex")
            included = _resolve_tex_file(relative, source.parent)
            if included is None:
                raise ValueError(f"{source}: missing manual input {relative}")
            pending.append(
                (
                    included,
                    _conditionals_before(
                        raw,
                        match.start(),
                        inherited_conditionals,
                        source.parent,
                    ),
                )
            )
    return sorted(visited.items())


def _manual_sources() -> list[Path]:
    return [source for source, _ in _manual_source_contexts()]


def reference_examples() -> list[Example]:
    registry = strip_comments(REGISTRY.read_text(encoding="utf-8"))
    commands, _ = _registry_vocabulary()
    mappings = re.findall(
        r"\\__tenkz_language_registry_example:nnn\s*"
        r"\{([^{}]+)\}\s*\{([^{}]+)\}",
        registry,
    )
    mapping_by_command = dict(mappings)
    if len(mapping_by_command) != len(mappings):
        raise ValueError(f"{REGISTRY}: duplicate command example mapping")
    missing = sorted(set(commands) - mapping_by_command.keys())
    extra = sorted(mapping_by_command.keys() - set(commands))
    if missing or extra:
        raise ValueError(
            f"{REGISTRY}: command/example mismatch; missing={missing}, extra={extra}"
        )

    generated_paths = re.findall(
        r"Example:\s*\\texttt\{\\detokenize\{([^{}]+)\}\}",
        REFERENCE.read_text(encoding="utf-8"),
    )
    registry_paths = [mapping_by_command[command] for command in commands]
    if len(set(registry_paths)) != len(registry_paths):
        raise ValueError(f"{REGISTRY}: command example paths must be distinct")
    if generated_paths != registry_paths:
        raise ValueError(
            f"{REFERENCE}: generated example list differs from the registry"
        )

    examples: list[Example] = []
    for command in commands:
        relative = Path(mapping_by_command[command])
        source = ROOT / relative
        if not source.is_file():
            raise ValueError(f"{REGISTRY}: example for \\{command} is missing: {relative}")
        document = source.read_text(encoding="utf-8")
        if not _has_executable_command(document, command):
            raise ValueError(
                f"{source}: example mapped to \\{command} does not invoke that command"
            )
        instrumented, marker = _instrument_command(
            document, command, source.parent
        )
        examples.append(
            Example(
                label=f"reference-{command}",
                source=source,
                line=1,
                document=instrumented,
                coverage_marker=marker,
            )
        )
    return examples


def compile_example(example: Example, engine: str, work: Path) -> None:
    case_dir = work / example.label
    case_dir.mkdir()
    driver = case_dir / "example.tex"
    driver.write_text(example.document, encoding="utf-8")
    env = os.environ.copy()
    env["TEXINPUTS"] = (
        f"{example.source.parent}//:{MANUAL_DIR}//:{ROOT / 'tex' / 'tenkz'}//:"
        f"{env.get('TEXINPUTS', '')}"
    )
    run = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", driver.name],
        cwd=case_dir,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
    )
    if run.returncode:
        tail = "\n".join(run.stdout.splitlines()[-60:])
        raise RuntimeError(
            f"{example.source}:{example.line}: standalone compilation failed "
            f"for {example.label}\n{tail}"
        )
    if example.coverage_marker and example.coverage_marker not in run.stdout:
        raise RuntimeError(
            f"{example.source}:{example.line}: \\{example.label.removeprefix('reference-')} "
            "was not executed during standalone compilation"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default="xelatex", help="TeX engine (default: xelatex)")
    parser.add_argument(
        "--list",
        action="store_true",
        help="list extracted examples and validate coverage without compiling",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manual = displayed_examples()
    reference = reference_examples()
    if not manual:
        raise ValueError(f"{CHAPTERS}: no displayed TeX examples found")

    if args.list:
        for example in [*manual, *reference]:
            print(f"{example.label}\t{example.source.relative_to(ROOT)}:{example.line}")
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz-manual-doctest-") as tmp:
            work = Path(tmp)
            for example in [*manual, *reference]:
                print(f"compile {example.label}")
                compile_example(example, args.engine, work)

    print(
        f"PASS: {len(manual)} displayed manual examples and "
        f"{len(reference)} reference examples"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
