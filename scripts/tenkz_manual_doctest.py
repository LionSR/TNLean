#!/usr/bin/env python3
"""Compile every displayed tenkz manual example as a standalone document."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from tenkzlib.texcase import strip_comments


ROOT = Path(__file__).resolve().parents[1]
MANUAL_DIR = ROOT / "docs" / "tenkz"
MANUAL = MANUAL_DIR / "manual2.tex"
CHAPTERS = ROOT / "docs" / "tenkz" / "chapters2"
REGISTRY = ROOT / "tex" / "tenkz" / "tenkz-language-registry.tex"
REFERENCE = CHAPTERS / "generated-language-reference.tex"
DISPLAY_ENVIRONMENTS = ("tnexample", "tnmultiples", "Verbatim")


@dataclass(frozen=True)
class Example:
    label: str
    source: Path
    line: int
    document: str


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

    brace_depth = 0
    index = offset + 1
    while index < len(text):
        if text[index] == "%" and not _is_escaped(text, index):
            newline = text.find("\n", index)
            if newline < 0:
                break
            index = newline + 1
            continue
        escaped = _is_escaped(text, index)
        if text[index] == "{" and not escaped:
            brace_depth += 1
        elif text[index] == "}" and not escaped:
            brace_depth -= 1
            if brace_depth < 0:
                raise ValueError("unbalanced brace in optional environment argument")
        elif text[index] == "]" and not escaped and brace_depth == 0:
            return index + 1, _strip_tex_comments(text[offset + 1:index])
        index += 1
    raise ValueError("unterminated optional environment argument")


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
    depth = 0
    for index in range(offset, len(text)):
        escaped = _is_escaped(text, index)
        if text[index] == "{" and not escaped:
            depth += 1
        elif text[index] == "}" and not escaped:
            depth -= 1
            if depth == 0:
                return index + 1, text[offset + 1:index]
    raise ValueError("unterminated braced group")


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
    registry = REGISTRY.read_text(encoding="utf-8")
    commands = re.findall(
        r"\\__tenkz_language_registry_command:nnnnn\s*\{([^{}]+)\}", registry
    )
    environments = re.findall(
        r"\\__tenkz_language_registry_environment:nnnn\s*\{([^{}]+)\}", registry
    )
    return commands, environments


def _is_tenkz_verbatim(body: str) -> bool:
    commands, environments = _registry_vocabulary()
    command_pattern = "|".join(re.escape(command) for command in commands)
    environment_pattern = "|".join(re.escape(environment) for environment in environments)
    packages, _ = _extract_usepackages(body)
    uncommented = _strip_tex_comments(body)
    return bool(
        any("tenkz" in _package_names(package) for package in packages)
        or re.search(rf"\\(?:{command_pattern})(?![A-Za-z@:_])", uncommented)
        or re.search(rf"\\begin\{{(?:{environment_pattern})\}}", uncommented)
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


def _mask_inline_verbatim(text: str) -> str:
    masked = list(text)
    offset = 0
    while (start := text.find(r"\verb", offset)) >= 0:
        delimiter_offset = start + len(r"\verb")
        if delimiter_offset < len(text) and text[delimiter_offset] == "*":
            delimiter_offset += 1
        if delimiter_offset >= len(text):
            break
        delimiter = text[delimiter_offset]
        if delimiter.isspace() or delimiter.isalnum():
            offset = delimiter_offset
            continue
        end = text.find(delimiter, delimiter_offset + 1)
        if end < 0:
            break
        for index in range(start, end + 1):
            if masked[index] != "\n":
                masked[index] = " "
        offset = end + 1
    return "".join(masked)


def _extract_usepackages(body: str) -> tuple[list[str], str]:
    ranges: list[tuple[int, int]] = []
    offset = 0
    marker = r"\usepackage"
    scan_body = _mask_inline_verbatim(body)
    while (start := _find_uncommented(scan_body, marker, offset)) >= 0:
        cursor = _skip_space_and_comments(body, start + len(marker))
        if cursor < len(body) and body[cursor] == "[":
            cursor, _ = _read_optional_argument(body, cursor)
        cursor = _skip_space_and_comments(body, cursor)
        end, _ = _read_braced(body, cursor)
        ranges.append((start, end))
        offset = end

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
    return [name.strip() for name in names.split(",")]


def _find_environment_end(text: str, environment: str, offset: int) -> re.Match[str] | None:
    pattern = re.compile(
        rf"^[ \t]*\\end\{{{re.escape(environment)}\}}[ \t]*$",
        re.MULTILINE,
    )
    return pattern.search(text, offset)


def _variant_definitions(variant_style: str) -> list[str]:
    return [
        rf"\pgfqkeys{{/tenkz/grid}}{{variant/.style={{{variant_style}}}}}",
        rf"\pgfqkeys{{/tenkz/cell}}{{variant/.style={{{variant_style}}}}}",
    ]


def _standalone_document(body: str, variant_style: str | None = None) -> str:
    body = body.strip()
    scan_body = _mask_inline_verbatim(body)
    has_document_class = _find_uncommented(scan_body, r"\documentclass", 0) >= 0
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

    preamble, content = _extract_usepackages(body)
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


def extract_displayed_examples(path: Path) -> list[Example]:
    text = path.read_text(encoding="utf-8")
    begin_pattern = re.compile(
        r"^[ \t]*\\begin\{(" + "|".join(DISPLAY_ENVIRONMENTS) + r")\}",
        re.MULTILINE,
    )
    examples: list[Example] = []
    offset = 0
    ordinal = 0
    while match := begin_pattern.search(text, offset):
        if _is_commented(text, match.start()):
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
        if environment == "Verbatim" and not _is_tenkz_verbatim(body):
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
                    label=f"manual-{path.stem}-{ordinal}{suffix}",
                    source=path,
                    line=line,
                    document=_standalone_document(body, variant_style),
                )
            )
    return examples


def displayed_examples() -> list[Example]:
    examples: list[Example] = []
    for path in _manual_chapter_sources():
        examples.extend(extract_displayed_examples(path))
    return examples


def _manual_chapter_sources() -> list[Path]:
    pending = [MANUAL]
    visited: set[Path] = set()
    chapters: set[Path] = set()
    input_pattern = re.compile(r"\\input\s*\{([^{}]+)\}")
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        text = _strip_tex_comments(_mask_inline_verbatim(source.read_text(encoding="utf-8")))
        for match in input_pattern.finditer(text):
            relative = Path(match.group(1))
            if not relative.suffix:
                relative = relative.with_suffix(".tex")
            included = (MANUAL_DIR / relative).resolve()
            if not included.is_file():
                raise ValueError(f"{source}: missing manual input {relative}")
            pending.append(included)
            if included.is_relative_to(CHAPTERS):
                chapters.add(included)
    return sorted(chapters)


def reference_examples() -> list[Example]:
    registry = REGISTRY.read_text(encoding="utf-8")
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
        uncommented = _strip_tex_comments(document)
        if not re.search(rf"\\{re.escape(command)}(?![A-Za-z@:_])", uncommented):
            raise ValueError(
                f"{source}: example mapped to \\{command} does not invoke that command"
            )
        examples.append(
            Example(
                label=f"reference-{command}",
                source=source,
                line=1,
                document=document,
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
        f"{example.source.parent}//:{ROOT / 'tex' / 'tenkz'}//:"
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
