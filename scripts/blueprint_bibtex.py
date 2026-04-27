#!/usr/bin/env python3
"""Generate the `.bbl` file needed by plasTeX blueprint builds."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

try:
    from pybtex.backends.latex import Backend
    from pybtex.database import BibliographyData, parse_file
    from pybtex.plugin import PluginNotFound, find_plugin
except ImportError as err:  # pragma: no cover - exercised in CI setup failures.
    raise SystemExit(
        "pybtex is required; install it with `python3 -m pip install pybtex`."
    ) from err


TEX_CITE_RE = re.compile(
    r"""\\(?:[cC]ite[talp]*|[cC]iteauthor|[cC]iteyear(?:par)?|citeN|nocite)\*?"""
    r"""(?:\s*\[[^\[\]]*\]){0,2}\s*\{([^{}]+)\}"""
)
BIB_STYLE_RE = re.compile(r"""\\bibliographystyle\{([^{}]+)\}""")
BIB_DATA_RE = re.compile(r"""\\bibliography\{([^{}]+)\}""")
INPUT_RE = re.compile(r"""\\(?:input|include)\{([^{}]+)\}""")


def first_match(pattern: re.Pattern[str], text: str, default: str = "") -> str:
    match = pattern.search(text)
    return match.group(1).strip() if match else default


def strip_latex_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        i = 0
        while True:
            i = line.find("%", i)
            if i == -1:
                lines.append(line)
                break
            backslashes = 0
            j = i - 1
            while j >= 0 and line[j] == "\\":
                backslashes += 1
                j -= 1
            if backslashes % 2 == 0:
                lines.append(line[:i])
                break
            i += 1
    return "\n".join(lines)


def resolve_tex_path(src_dir: Path, current_dir: Path, raw_path: str) -> Path:
    path = Path(raw_path.strip())
    if not path.suffix:
        path = path.with_suffix(".tex")
    if path.is_absolute():
        return path
    candidate = current_dir / path
    return candidate if candidate.exists() else src_dir / path


def reachable_tex_files(src_dir: Path, entry_path: Path) -> list[Path]:
    seen: set[Path] = set()
    ordered: list[Path] = []

    def visit(path: Path) -> None:
        path = path.resolve()
        if path in seen or not path.exists():
            return
        seen.add(path)
        ordered.append(path)
        text = strip_latex_comments(path.read_text(encoding="utf-8", errors="replace"))
        for match in INPUT_RE.finditer(text):
            visit(resolve_tex_path(src_dir, path.parent, match.group(1)))

    visit(entry_path)
    return ordered


def resolve_bib_path(src_dir: Path, current_dir: Path, raw_path: str) -> Path:
    path = Path(raw_path.strip())
    if not path.suffix:
        path = path.with_suffix(".bib")
    if path.is_absolute():
        return path
    candidate = current_dir / path
    return candidate if candidate.exists() else src_dir / path


def bibliography_files(src_dir: Path, tex_path: Path) -> list[Path]:
    paths: list[Path] = []
    seen: set[Path] = set()
    for source_path in reachable_tex_files(src_dir, tex_path):
        text = strip_latex_comments(source_path.read_text(encoding="utf-8", errors="replace"))
        for match in BIB_DATA_RE.finditer(text):
            for raw_name in match.group(1).split(","):
                name = raw_name.strip()
                if not name:
                    continue
                path = resolve_bib_path(src_dir, source_path.parent, name)
                resolved = path.resolve()
                if resolved not in seen:
                    seen.add(resolved)
                    paths.append(path)
    return paths


def citation_keys(src_dir: Path, tex_path: Path) -> list[str] | None:
    keys: list[str] = []
    seen: set[str] = set()
    for source_path in reachable_tex_files(src_dir, tex_path):
        text = strip_latex_comments(source_path.read_text(encoding="utf-8", errors="replace"))
        for match in TEX_CITE_RE.finditer(text):
            for raw_key in match.group(1).split(","):
                key = raw_key.strip()
                if key == "*":
                    return None
                if key and key not in seen:
                    seen.add(key)
                    keys.append(key)
    return keys


def load_bibliography(paths: list[Path]) -> BibliographyData:
    bibliography = BibliographyData()
    for path in paths:
        parsed = parse_file(str(path), bib_format="bibtex")
        duplicate_keys = sorted(key for key in parsed.entries if key in bibliography.entries)
        if duplicate_keys:
            print(f"warning: duplicate bibliography keys in {path}: "
                  f"{', '.join(duplicate_keys)}", file=sys.stderr)
        bibliography.add_entries(parsed.entries.items())
        for preamble in parsed.preamble_list:
            bibliography.add_to_preamble(preamble)
    return bibliography


def run(args: argparse.Namespace) -> int:
    src_dir = args.src_dir.resolve()
    tex_path = src_dir / args.tex
    if not tex_path.exists():
        print(f"error: blueprint TeX entry not found: {tex_path}", file=sys.stderr)
        return 2

    tex = strip_latex_comments(tex_path.read_text(encoding="utf-8", errors="replace"))
    style_name = first_match(BIB_STYLE_RE, tex, args.default_style)

    bib_paths = bibliography_files(src_dir, tex_path)
    if not bib_paths:
        print(f"No \\bibliography{{...}} found in {tex_path}; skipping bibliography.")
        return 0
    missing_paths = [str(path) for path in bib_paths if not path.exists()]
    if missing_paths:
        print(f"error: bibliography files not found: {', '.join(missing_paths)}", file=sys.stderr)
        return 1

    bibliography = load_bibliography(bib_paths)
    citations = None if args.keys == "*" else (
        [key.strip() for key in args.keys.split(",") if key.strip()]
        if args.keys else citation_keys(src_dir, tex_path)
    )
    if citations is not None and not citations:
        print("No citations found; skipping bibliography.")
        return 0

    missing_keys = [] if citations is None else [
        key for key in citations if key not in bibliography.entries
    ]
    if missing_keys:
        print(f"error: cited keys missing from bibliography: {', '.join(missing_keys)}",
              file=sys.stderr)
        return 1

    try:
        style_cls = find_plugin("pybtex.style.formatting", style_name)
    except PluginNotFound as err:
        print(f"error: pybtex does not provide bibliography style {style_name!r}",
              file=sys.stderr)
        return 1

    output_path = tex_path.with_suffix(".bbl")
    formatted = style_cls().format_bibliography(bibliography, citations=citations)
    with output_path.open("w", encoding="utf-8") as stream:
        Backend().write_to_stream(formatted, stream)
    print(f"Generated {output_path}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src-dir", type=Path, default=Path("blueprint/src"))
    parser.add_argument("--tex", default="web.tex")
    parser.add_argument("--default-style", default="alpha")
    parser.add_argument("--keys", help="Comma-separated citation keys, or '*' for all entries.")
    return run(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
