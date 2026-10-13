#!/usr/bin/env python3
"""Find Lean declarations that nothing in the repository refers to.

Purpose
-------
Supports the zero-reference deletion waves of the proof-debt loop
(``docs/proof_debt.md``, ledger entry S2 in ``docs/proof_debt_ledger.md``,
tracker #4564).  Every wave so far rewrote this scan from scratch; this
module makes the residue re-derivable from an exact checkout.

Method
------
* Walk ``TNLean/**/*.lean`` (``Archive/`` only with ``--include-archive``)
  and collect every ``theorem``, ``lemma``, ``def``, ``abbrev``,
  ``structure``, ``class``, ``inductive`` and ``opaque`` header.  Comments
  are stripped before matching, so a docstring sentence starting with
  "theorem." is not a header; an indented header still counts.  Instances
  are skipped (they are found by synthesis, not by name).  Declarations
  whose header carries an attribute (``@[simp]``, ``@[grind]``, ``@[ext]``,
  ...) are skipped unless ``--include-attributed`` is given, because
  ``simp``, ``grind`` and ``ext`` use them without naming them.
* Count word-boundary occurrences of each declaration's final name component
  across the reference corpus: every ``.lean`` file under ``TNLean/``,
  ``TNLeanTest/``, ``Archive/`` and ``scripts/``, the blueprint sources,
  ``docs/``, ``Notes/``, ``Papers/`` and the Python/JSON files under
  ``scripts/``.  Extra corpus directories (for example a checked-out
  downstream package) are added with ``--corpus``.  Dot notation
  (``h.foo``) and namespace-qualified calls (``Foo.bar.foo``) both contain
  the final component.  Occurrences inside the declaration's own extent
  (its docstring, header and body, so also recursive calls) do not count,
  and a declaration is a candidate when nothing is left.
* Iterate to a fixed point: the source extent of each candidate (its
  docstring, header and indented body) is removed from the counting corpus
  and the count is taken again, so a declaration used only by other dead
  declarations is reported as well.  ``--no-transitive`` disables this
  pass.

The output is a candidate list, not a deletion list.  Each candidate still
needs the wave protocol before it goes: a check of the cited paper passage,
a check for paper-gap and blueprint prose that names it in words rather than
by identifier, and a build.

Usage
-----
    python3 scripts/zero_reference_scan.py                  # default scan
    python3 scripts/zero_reference_scan.py --include-attributed
    python3 scripts/zero_reference_scan.py --json > residue.json
    python3 scripts/zero_reference_scan.py --corpus ../QICLean

Exit code is always 0; this is a reporting tool, not a lint gate.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

DECLARATION_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "opaque",
    "instance",
)

MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "nonrec",
    "partial",
    "unsafe",
    "scoped",
)

NAME_PATTERN = r"[^\W\d][\w!?']*(?:\.[^\W\d][\w!?']*)*"

HEADER_RE = re.compile(
    r"^[ \t]*(?P<attr>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:(?:" + "|".join(MODIFIERS) + r")\s+)*)"
    r"(?P<kind>" + "|".join(DECLARATION_KEYWORDS) + r")\s+"
    r"(?P<name>" + NAME_PATTERN + r")",
    re.MULTILINE,
)

TOKEN_RE = re.compile(r"[^\W\d][\w!?']*")

# Directories under ``TNLean/`` that are not part of the library proper.
EXCLUDED_DIRS = {"Archive", "Scratch"}

CORPUS_GLOBS = (
    "TNLean/**/*.lean",
    "TNLeanTest/**/*.lean",
    "Archive/**/*.lean",
    "blueprint/src/**/*.tex",
    "docs/**/*.md",
    "docs/**/*.tex",
    "Notes/**/*.tex",
    "Notes/**/*.md",
    "Papers/**/*.tex",
    "Papers/**/*.md",
    "scripts/**/*.py",
    "scripts/**/*.json",
    "scripts/**/*.lean",
)


@dataclass(frozen=True)
class Declaration:
    """One declaration header: where it is and what it declares."""

    path: str
    line: int
    kind: str
    name: str
    attributed: bool
    start: int  # character offset of the docstring or header
    end: int  # character offset one past the last body line

    @property
    def short_name(self) -> str:
        return self.name.rsplit(".", 1)[-1]


def strip_comments(text: str) -> str:
    """Blank out block and line comments, keeping line structure and offsets.

    Every comment character except a newline becomes a space, so offsets and
    line numbers of the remaining code are unchanged.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
        i += 1
    return "".join(out)


def _extent(text: str, header_start: int, next_header_start: int | None) -> tuple[int, int]:
    """Return the character range of a declaration's docstring, header and body.

    The body is every following line that is blank or indented; the extent
    ends at the next line that starts in column zero, or at the line of the
    next declaration header when that comes first.  A docstring block ending
    just before the header is included.
    """
    line_starts = [0] + [m.end() for m in re.finditer(r"\n", text)]
    header_line = max(i for i, s in enumerate(line_starts) if s <= header_start)
    start = line_starts[header_line]
    # Include a docstring that ends on the preceding line.
    j = header_line - 1
    if j >= 0:
        prev = text[line_starts[j] : line_starts[header_line]]
        if prev.rstrip().endswith("-/"):
            while j >= 0 and not text[line_starts[j] :].lstrip().startswith("/-"):
                j -= 1
            if j >= 0:
                start = line_starts[j]
    end = len(text)
    for k in range(header_line + 1, len(line_starts)):
        line = text[line_starts[k] : line_starts[k + 1] if k + 1 < len(line_starts) else len(text)]
        if line.strip() and not line[0].isspace():
            end = line_starts[k]
            break
    if next_header_start is not None:
        next_line = max(i for i, s in enumerate(line_starts) if s <= next_header_start)
        end = min(end, line_starts[next_line])
    return start, end


def collect_declarations(path: Path, rel: str, include_attributed: bool) -> list[Declaration]:
    """Collect the declaration headers of one Lean file."""
    text = path.read_text(encoding="utf-8")
    code = strip_comments(text)
    decls: list[Declaration] = []
    matches = list(HEADER_RE.finditer(code))
    for m, following in zip(matches, matches[1:] + [None]):
        if m.group("kind") == "instance":
            continue
        attributed = bool(m.group("attr").strip())
        if attributed and not include_attributed:
            continue
        start, end = _extent(
            text, m.start("kind"), None if following is None else following.start("kind")
        )
        decls.append(
            Declaration(
                path=rel,
                line=code.count("\n", 0, m.start("kind")) + 1,
                kind=m.group("kind"),
                name=m.group("name"),
                attributed=attributed,
                start=start,
                end=end,
            )
        )
    return decls


def declaration_files(root: Path, include_archive: bool) -> list[Path]:
    files = []
    for path in sorted((root / "TNLean").rglob("*.lean")):
        parts = path.relative_to(root / "TNLean").parts
        if not include_archive and parts and parts[0] in EXCLUDED_DIRS:
            continue
        files.append(path)
    return files


def corpus_files(root: Path, extra: list[Path]) -> list[Path]:
    seen: set[Path] = set()
    files: list[Path] = []
    for pattern in CORPUS_GLOBS:
        for path in sorted(root.glob(pattern)):
            if path.is_file() and path not in seen:
                seen.add(path)
                files.append(path)
    for base in extra:
        for suffix in ("*.lean", "*.tex", "*.md", "*.py", "*.json"):
            for path in sorted(base.rglob(suffix)):
                if path.is_file() and path not in seen:
                    seen.add(path)
                    files.append(path)
    return files


def count_tokens(texts: dict[str, str], names: set[str]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for text in texts.values():
        for token in TOKEN_RE.findall(text):
            if token in names:
                counts[token] += 1
    return counts


def _own_occurrences(text: str, decl: Declaration) -> int:
    """Count the declaration's own name inside its docstring, header and body."""
    own = text[decl.start : decl.end]
    return sum(1 for token in TOKEN_RE.findall(own) if token == decl.short_name)


def _blank_extents(text: str, extents: list[tuple[int, int]]) -> str:
    chars = list(text)
    for start, end in extents:
        for i in range(start, end):
            if chars[i] != "\n":
                chars[i] = " "
    return "".join(chars)


def find_zero_reference(
    root: Path,
    *,
    include_archive: bool = False,
    include_attributed: bool = False,
    transitive: bool = True,
    extra_corpus: list[Path] | None = None,
) -> list[Declaration]:
    """Return the declarations whose final name component occurs only in their own extent."""
    decls: list[Declaration] = []
    for path in declaration_files(root, include_archive):
        decls.extend(
            collect_declarations(path, path.relative_to(root).as_posix(), include_attributed)
        )
    names = {d.short_name for d in decls}
    texts = {
        p.relative_to(root).as_posix() if p.is_relative_to(root) else str(p): p.read_text(
            encoding="utf-8", errors="replace"
        )
        for p in corpus_files(root, extra_corpus or [])
    }
    dead: dict[tuple[str, int], Declaration] = {}
    while True:
        counts = count_tokens(texts, names)
        fresh = [
            d
            for d in decls
            if (d.path, d.line) not in dead
            and counts[d.short_name] <= _own_occurrences(texts[d.path], d)
        ]
        if not fresh:
            break
        for d in fresh:
            dead[(d.path, d.line)] = d
        if not transitive:
            break
        by_file: dict[str, list[tuple[int, int]]] = {}
        for d in fresh:
            by_file.setdefault(d.path, []).append((d.start, d.end))
        for rel, extents in by_file.items():
            texts[rel] = _blank_extents(texts[rel], extents)
    return sorted(dead.values(), key=lambda d: (d.path, d.line))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument(
        "--include-archive", action="store_true", help="also scan TNLean/Archive declarations"
    )
    parser.add_argument(
        "--include-attributed",
        action="store_true",
        help="also report declarations carrying an attribute such as @[simp]",
    )
    parser.add_argument(
        "--no-transitive",
        action="store_true",
        help="report only first-round candidates, without the fixed-point pass",
    )
    parser.add_argument(
        "--corpus",
        type=Path,
        action="append",
        default=[],
        help="extra directory whose .lean/.tex/.md/.py/.json files count as references",
    )
    parser.add_argument("--json", action="store_true", help="emit a JSON list instead of text")
    args = parser.parse_args(argv)

    root = args.root.resolve()
    dead = find_zero_reference(
        root,
        include_archive=args.include_archive,
        include_attributed=args.include_attributed,
        transitive=not args.no_transitive,
        extra_corpus=[p.resolve() for p in args.corpus],
    )
    if args.json:
        print(
            json.dumps(
                [
                    {"path": d.path, "line": d.line, "kind": d.kind, "name": d.name}
                    for d in dead
                ],
                indent=2,
            )
        )
        return 0
    print(f"{len(dead)} declarations with no reference outside their own definition")
    for d in dead:
        print(f"{d.path}:{d.line}: {d.kind} {d.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
