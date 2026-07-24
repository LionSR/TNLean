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
TEX_VERBATIM_MARKERS = (
    r"\begin{tenkz",
    r"\tnpic",
    r"\tndeclareatom",
    r"\usepackage{tenkz}",
)


@dataclass(frozen=True)
class Example:
    label: str
    source: Path
    line: int
    document: str


def _skip_optional_argument(text: str, offset: int) -> int:
    while offset < len(text) and text[offset].isspace():
        offset += 1
    if offset == len(text) or text[offset] != "[":
        return offset

    depth = 0
    for index in range(offset, len(text)):
        if text[index] == "[" and (index == 0 or text[index - 1] != "\\"):
            depth += 1
        elif text[index] == "]" and (index == 0 or text[index - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return index + 1
    raise ValueError("unterminated optional environment argument")


def _standalone_document(body: str) -> str:
    preamble: list[str] = []
    content: list[str] = []
    for line in body.strip().splitlines():
        if line.lstrip().startswith(r"\usepackage"):
            preamble.append(line.strip())
        else:
            content.append(line)
    if not any(r"\usepackage{tenkz}" in line for line in preamble):
        preamble.append(r"\usepackage{tenkz}")
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
        body_start = _skip_optional_argument(text, match.end())
        end_marker = rf"\end{{{environment}}}"
        body_end = text.find(end_marker, body_start)
        if body_end < 0:
            line = text.count("\n", 0, match.start()) + 1
            raise ValueError(f"{path}:{line}: missing {end_marker}")
        body = text[body_start:body_end].strip()
        offset = body_end + len(end_marker)
        if environment == "Verbatim" and not any(
            marker in body for marker in TEX_VERBATIM_MARKERS
        ):
            continue
        ordinal += 1
        line = text.count("\n", 0, match.start()) + 1
        examples.append(
            Example(
                label=f"manual-{path.stem}-{ordinal}",
                source=path,
                line=line,
                document=_standalone_document(body),
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
    commands = re.findall(
        r"\\__tenkz_language_registry_command:nnnnn\s*\{([^{}]+)\}", registry
    )
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
        examples.append(
            Example(
                label=f"reference-{command}",
                source=source,
                line=1,
                document=source.read_text(encoding="utf-8"),
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
