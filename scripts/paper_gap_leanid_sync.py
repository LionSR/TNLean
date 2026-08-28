#!/usr/bin/env python3
r"""Check ``docs/paper-gaps`` ``\leanid{...}`` references.

The paper-gap notes use ``\leanid`` for prose-level Lean declaration citations.
This script extracts the declaration head from each payload, writes the unique
heads to a checkdecls-compatible file, and can invoke ``lake exe checkdecls`` so
existence is checked by Lean's compiled environment rather than by source regexes.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from blueprint_lean_sync import split_tex_lean_decls


_MACRO_NAME = "leanid"
_HEAD_STRIP_CHARS = "`$.,;:()[]{}"


@dataclass(frozen=True)
class LeanIdRef:
    file: str
    line: int
    column: int
    payload: str
    head: str


def _is_escaped(text: str, index: int) -> bool:
    backslashes = 0
    cursor = index - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


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
        if char == "%" and not _is_escaped(text, index):
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
            if text[cursor] == "%" and not _is_escaped(text, cursor):
                comment_end = _skip_tex_comment(text, cursor)
                payload_parts.append(text[cursor:comment_end])
                cursor = comment_end
                continue
            if text[cursor] == "{" and not _is_escaped(text, cursor):
                depth += 1
            elif text[cursor] == "}" and not _is_escaped(text, cursor):
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
        description="Extract and check docs/paper-gaps \\leanid declaration heads."
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
