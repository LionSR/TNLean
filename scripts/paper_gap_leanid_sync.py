#!/usr/bin/env python3
r"""Check ``docs/paper-gaps`` ``\leanid{...}`` references and ``docs/glossary.md`` names.

The paper-gap notes use ``\leanid`` for prose-level Lean declaration citations.
This script extracts the declaration head from each payload, writes the unique
heads to a checkdecls-compatible file, and can invoke ``lake exe checkdecls`` so
existence is checked by Lean's compiled environment rather than by source regexes.

The glossary names declarations in backticks.  Every backticked span whose head is a
qualified name (``Namespace.decl``, first component capitalized) is added to the same
list, except module names and file names, so the one ``checkdecls`` run covers both.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from blueprint_lean_sync import is_escaped_tex_char, split_tex_lean_decls


_MACRO_NAME = "leanid"
_HEAD_STRIP_CHARS = "`$.,;:()[]{}"
# Intentional placeholders used to document the macro in policy/template prose.
_EXAMPLE_PLACEHOLDER_HEADS = {
    "policy.tex": {"someDeclaration"},
    "template.tex": {"modelCorrected"},
}


@dataclass(frozen=True)
class LeanIdRef:
    file: str
    line: int
    column: int
    payload: str
    head: str


def _line_col(text: str, index: int) -> tuple[int, int]:
    line = text.count("\n", 0, index) + 1
    line_start = text.rfind("\n", 0, index) + 1
    return line, index - line_start + 1


def _skip_tex_comment(text: str, index: int) -> int:
    newline = text.find("\n", index)
    return len(text) if newline < 0 else newline + 1


def iter_tex_macro_payloads(text: str, macro_name: str = _MACRO_NAME) -> list[tuple[int, int, str]]:
    r"""Return ``(offset, line, payload)`` triples for ``\macro_name{...}``.

    The scanner ignores TeX comments outside macros and tracks braces in the
    payload.  Braces in comments inside the payload are ignored, which matches
    the percent-continuation style used in long ``\leanid`` names.
    """
    marker = "\\" + macro_name
    payloads: list[tuple[int, int, str]] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char == "%" and not is_escaped_tex_char(text, index):
            index = _skip_tex_comment(text, index)
            continue
        if not text.startswith(marker, index):
            index += 1
            continue

        after = index + len(marker)
        if after < len(text) and text[after].isalpha():
            index += 1
            continue
        cursor = after
        while cursor < len(text) and text[cursor].isspace():
            cursor += 1
        if cursor >= len(text) or text[cursor] != "{":
            index += 1
            continue

        start = cursor + 1
        cursor = start
        depth = 1
        payload_parts: list[str] = []
        while cursor < len(text) and depth > 0:
            if text[cursor] == "%" and not is_escaped_tex_char(text, cursor):
                comment_end = _skip_tex_comment(text, cursor)
                payload_parts.append(text[cursor:comment_end])
                cursor = comment_end
                continue
            if text[cursor] == "{" and not is_escaped_tex_char(text, cursor):
                depth += 1
            elif text[cursor] == "}" and not is_escaped_tex_char(text, cursor):
                depth -= 1
                if depth == 0:
                    break
            payload_parts.append(text[cursor])
            cursor += 1

        if depth == 0:
            line, _ = _line_col(text, index)
            payloads.append((index, line, "".join(payload_parts)))
            index = cursor + 1
        else:
            index = start
    return payloads


def _normalise_tex_identifier_text(text: str) -> str:
    text = text.replace(r"\_", "_")
    text = text.replace(r"\.", ".")
    text = text.replace(r"\-", "-")
    text = text.replace("~", " ")
    return re.sub(r"\s+", " ", text).strip()


def _is_lean_name_char(char: str) -> bool:
    return char == "." or char == "_" or char == "'" or char.isalnum() or ord(char) >= 0x80


def lean_decl_head(payload_item: str) -> str | None:
    """Return the Lean declaration head cited by one normalized payload item."""
    item = _normalise_tex_identifier_text(payload_item).strip(_HEAD_STRIP_CHARS)
    if not item:
        return None
    cursor = 0
    while cursor < len(item) and _is_lean_name_char(item[cursor]):
        cursor += 1
    head = item[:cursor].strip(".")
    return head or None


def collect_paper_gap_leanid_refs(paper_gaps_dir: Path, root: Path) -> list[LeanIdRef]:
    refs: list[LeanIdRef] = []
    for tex_file in sorted(paper_gaps_dir.glob("*.tex")):
        text = tex_file.read_text(errors="replace")
        rel = str(tex_file.relative_to(root))
        for offset, line, payload in iter_tex_macro_payloads(text):
            _, column = _line_col(text, offset)
            for payload_item in split_tex_lean_decls(payload):
                head = lean_decl_head(payload_item)
                if head is None:
                    continue
                if head in _EXAMPLE_PLACEHOLDER_HEADS.get(tex_file.name, set()):
                    continue
                refs.append(
                    LeanIdRef(
                        file=rel,
                        line=line,
                        column=column,
                        payload=payload_item,
                        head=head,
                    )
                )
    return refs


_GLOSSARY_PATH = Path("docs") / "glossary.md"
_BACKTICK_SPAN = re.compile(r"(?<!`)`([^`\n]+)`(?!`)")
_QUALIFIED_HEAD = re.compile(r"^[A-Z][^.\s]*(\.[^.\s]+)+$")
_NAMESPACE_PREFIX = re.compile(r"\bnamespaces? $")
_FILE_SUFFIXES = (".lean", ".md", ".tex", ".py", ".sh", ".yml", ".yaml", ".toml", ".json",
                  ".txt", ".pdf", ".bib", ".cfg")


def _module_roots(root: Path) -> list[Path]:
    """Return the directories under which a dotted module name resolves to a source file."""
    packages = root / ".lake" / "packages"
    return [root, *sorted(path for path in packages.glob("*") if path.is_dir())]


def _is_module_name(head: str, roots: list[Path]) -> bool:
    relative = Path(*head.split(".")).with_suffix(".lean")
    return any((base / relative).is_file() or (base / Path(*head.split("."))).is_dir()
               for base in roots)


def glossary_decl_head(span: str) -> str | None:
    """Return the qualified declaration head named by one backticked glossary span."""
    head = lean_decl_head(span)
    if head is None or head != span.split(" ")[0].strip(_HEAD_STRIP_CHARS):
        return None
    if "/" in span.split(" ")[0] or head.endswith(_FILE_SUFFIXES):
        return None
    if not _QUALIFIED_HEAD.match(head) or len(head.split(".")[0]) == 1:
        return None  # not qualified, or a projection of a variable such as `M.toMPSTensor`
    return head


def collect_glossary_refs(glossary: Path, root: Path) -> list[LeanIdRef]:
    """Return the qualified declaration names that ``docs/glossary.md`` cites in backticks.

    Fenced code blocks are skipped.  A span whose head is a module (a ``.lean`` file or a
    directory of the repository or of a Lake package), a span introduced by the word
    "namespace", and a projection of a one-letter variable are not declarations.
    """
    refs: list[LeanIdRef] = []
    roots = _module_roots(root)
    rel = str(glossary.relative_to(root))
    in_fence = False
    for line_number, line in enumerate(glossary.read_text(errors="replace").splitlines(), 1):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for match in _BACKTICK_SPAN.finditer(line):
            if _NAMESPACE_PREFIX.search(line[: match.start()]):
                continue
            head = glossary_decl_head(match.group(1).strip())
            if head is None or _is_module_name(head, roots):
                continue
            refs.append(LeanIdRef(file=rel, line=line_number, column=match.start() + 1,
                                  payload=match.group(1), head=head))
    return refs


def write_decl_list(refs: list[LeanIdRef], path: Path) -> None:
    heads = sorted({ref.head for ref in refs})
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(heads) + ("\n" if heads else ""))


def print_summary(refs: list[LeanIdRef]) -> None:
    heads = sorted({ref.head for ref in refs})
    print(
        f"Found {len(refs)} \\leanid citation(s) with "
        f"{len(heads)} unique declaration head(s)."
    )


def run_checkdecls(root: Path, decls_file: Path) -> int:
    print(f"Checking paper-gap Lean declarations from {decls_file}")
    return subprocess.run(
        ["lake", "exe", "checkdecls", str(decls_file)],
        cwd=root,
        check=False,
    ).returncode


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract and check docs/paper-gaps \\leanid declaration heads and the "
        "declaration names of docs/glossary.md."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: auto-detected)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Write a checkdecls-compatible declaration list to this path.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Run `lake exe checkdecls` on the generated declaration list.",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    paper_gaps_dir = root / "docs" / "paper-gaps"
    if not paper_gaps_dir.is_dir():
        raise FileNotFoundError(f"Paper-gap directory not found: {paper_gaps_dir}")

    refs = collect_paper_gap_leanid_refs(paper_gaps_dir, root)
    print_summary(refs)
    glossary = root / _GLOSSARY_PATH
    if glossary.is_file():
        glossary_refs = collect_glossary_refs(glossary, root)
        print(f"Found {len({ref.head for ref in glossary_refs})} declaration name(s) "
              f"in {_GLOSSARY_PATH}.")
        refs += glossary_refs

    output = args.output
    if output is None:
        output = root / "build" / "paper_gap_leanid_decls"
    if not output.is_absolute():
        output = root / output
    write_decl_list(refs, output)
    print(f"Wrote {len({ref.head for ref in refs})} declaration head(s) to {output}")

    if args.check:
        sys.exit(run_checkdecls(root, output))


if __name__ == "__main__":
    main()
