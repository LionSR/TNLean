#!/usr/bin/env python3
"""Compile every displayed tenkz manual example as a standalone document."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
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


def _read_optional_argument(text: str, offset: int) -> tuple[int, str | None]:
    while offset < len(text) and text[offset].isspace():
        offset += 1
    if offset == len(text) or text[offset] != "[":
        return offset, None

    depth = 0
    for index in range(offset, len(text)):
        if text[index] == "[" and (index == 0 or text[index - 1] != "\\"):
            depth += 1
        elif text[index] == "]" and (index == 0 or text[index - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return index + 1, text[offset + 1:index]
    raise ValueError("unterminated optional environment argument")


def _split_top_level(text: str) -> list[str]:
    pieces: list[str] = []
    start = 0
    brace_depth = 0
    bracket_depth = 0
    for index, character in enumerate(text):
        escaped = index > 0 and text[index - 1] == "\\"
        if character == "{" and not escaped:
            brace_depth += 1
        elif character == "}" and not escaped:
            brace_depth -= 1
        elif character == "[" and not escaped:
            bracket_depth += 1
        elif character == "]" and not escaped:
            bracket_depth -= 1
        elif character == "," and brace_depth == 0 and bracket_depth == 0:
            pieces.append(text[start:index].strip())
            start = index + 1
        if brace_depth < 0 or bracket_depth < 0:
            raise ValueError("unbalanced option group")
    if brace_depth or bracket_depth:
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
        escaped = index > 0 and text[index - 1] == "\\"
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
    return bool(
        re.search(r"\\usepackage\s*\{tenkz\}", body)
        or re.search(rf"\\(?:{command_pattern})(?![A-Za-z@:_])", body)
        or re.search(rf"\\begin\{{(?:{environment_pattern})\}}", body)
    )


def _standalone_document(body: str, variant_style: str | None = None) -> str:
    preamble: list[str] = []
    content: list[str] = []
    for line in body.strip().splitlines():
        if line.lstrip().startswith(r"\usepackage"):
            preamble.append(line.strip())
        else:
            content.append(line)
    if not any(r"\usepackage{tenkz}" in line for line in preamble):
        preamble.append(r"\usepackage{tenkz}")
    if variant_style is not None:
        preamble.extend(
            [
                rf"\pgfqkeys{{/tenkz/grid}}{{variant/.style={{{variant_style}}}}}",
                rf"\pgfqkeys{{/tenkz/cell}}{{variant/.style={{{variant_style}}}}}",
            ]
        )
    return "\n".join(
        [
            r"\documentclass{article}",
            *preamble,
            r"\pagestyle{empty}",
            r"\begin{document}",
            *content,
            r"\end{document}",
            "",
        ]
    )


def extract_displayed_examples(path: Path) -> list[Example]:
    text = path.read_text(encoding="utf-8")
    begin_pattern = re.compile(
        r"\\begin\{(" + "|".join(DISPLAY_ENVIRONMENTS) + r")\}"
    )
    examples: list[Example] = []
    offset = 0
    ordinal = 0
    while match := begin_pattern.search(text, offset):
        environment = match.group(1)
        body_start, options = _read_optional_argument(text, match.end())
        end_marker = rf"\end{{{environment}}}"
        body_end = text.find(end_marker, body_start)
        if body_end < 0:
            line = text.count("\n", 0, match.start()) + 1
            raise ValueError(f"{path}:{line}: missing {end_marker}")
        body = text[body_start:body_end].strip()
        offset = body_end + len(end_marker)
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
    for path in sorted(CHAPTERS.glob("*.tex")):
        if path.name == "generated-language-reference.tex":
            continue
        examples.extend(extract_displayed_examples(path))
    return examples


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
        uncommented = re.sub(r"(?<!\\)%.*", "", document)
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
    env["TEXINPUTS"] = f"{ROOT / 'tex' / 'tenkz'}//:{env.get('TEXINPUTS', '')}"
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
