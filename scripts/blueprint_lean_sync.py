#!/usr/bin/env python3
r"""
Blueprint ↔ Lean code synchronisation checker.

Parses the blueprint .tex files for \lean{DeclName} and \leanok annotations,
then greps the Lean source tree for matching declarations.  Reports:

  1. Blueprint references whose Lean declaration cannot be found.
  2. \leanok tags on items whose declaration is missing from the Lean source.
  3. lean_decls entries that don't appear in any .tex file (stale entries).
  4. \lean{} refs that are not listed in lean_decls (missing entries).
  5. Declarations carrying a \lean{} tag in more than one blueprint entry.
  6. Summary statistics (formalization progress per chapter).

Exit code 0  → everything in sync (or --ci not passed).
Exit code 1  → mismatches found AND --ci flag is active.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private|scoped)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|class|structure|inductive|axiom|opaque|alias)\s+"
    r"((?![\d.])[\w']+(?:\.(?![\d.])[\w']+)*)",
    re.MULTILINE,
)
# Matches a line consisting solely of a declaration keyword (with optional
# attribute/modifier prefixes), used to detect multi-line declarations whose
# name appears on the following line.
_LEAN_DECL_KEYWORD_ONLY_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private|scoped)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|class|structure|inductive|axiom|opaque|alias)\s*$"
)
# Structure fields are declarations too: Lean generates a projection named
# `StructureName.fieldName` for each field.  Blueprint entries may legitimately
# cite that projection rather than the bundling structure.
_LEAN_STRUCTURE_FIELD_RE = re.compile(
    r"^\s+((?!where\b|extends\b|deriving\b)[\w']+)"
    r"(?:\s*\([^)]*\))*\s*:\s*"
)

_TRACKED_REVERSE_DECL_KINDS = {"def", "theorem", "lemma"}
_DIFF_HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")

# Match a `private` modifier appearing before the declaration keyword on a
# single line.  Used to skip private helpers in the "missing blueprint entry"
# check: by project convention, private helpers are internal proof-engineering
# scaffolding and do not require a blueprint anchor.
_LEAN_PRIVATE_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected)\s+)*"
    r"private\s+",
)

_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)", re.MULTILINE)
_SECTION_OPEN_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|local)\s+)*section\s+([\w.]+)",
    re.MULTILINE,
)
_NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\s+([\w.]+)", re.MULTILINE)

_TEX_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.DOTALL)
_TEX_LEANOK_RE = re.compile(r"\\leanok")
_TEX_ENV_BEGIN_RE = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
    r"(?:\[.*?\])?"
    r"(?:\\label\{([^}]+)\})?"
)
_TEX_ENV_END_RE = re.compile(
    r"\\end\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
)
_TEX_PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
_TEX_PROOF_END_RE = re.compile(r"\\end\{proof\}")


def is_escaped_tex_char(text: str, index: int) -> bool:
    """Return whether the character at ``index`` is escaped in TeX source."""
    backslashes = 0
    cursor = index - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


def _strip_tex_comments(payload: str) -> str:
    parts: list[str] = []
    index = 0
    while index < len(payload):
        if payload[index] == "%" and not is_escaped_tex_char(payload, index):
            newline = payload.find("\n", index)
            if newline < 0:
                break
            index = newline + 1
            while index < len(payload) and payload[index].isspace():
                index += 1
            continue
        parts.append(payload[index])
        index += 1
    return "".join(parts)


def split_tex_lean_decls(payload: str) -> list[str]:
    """Split the contents of a TeX Lean-declaration tag into declaration names.

    Blueprint tags are often wrapped across several TeX source lines for
    readability.  Normalising whitespace here keeps the sync checker aligned
    with ``leanblueprint web``, whose generated ``lean_decls`` file includes
    declarations from both one-line and multi-line tags.
    """
    payload = _strip_tex_comments(payload)
    parts: list[str] = []
    start = 0
    depth = 0
    for index, char in enumerate(payload):
        if is_escaped_tex_char(payload, index):
            continue
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(payload[start:index])
            start = index + 1
    parts.append(payload[start:])
    return [
        normalised
        for part in parts
        if (normalised := re.sub(r"\s+", " ", part).strip())
    ]


def _split_lean_decls(payload: str) -> list[str]:
    """Backward-compatible wrapper for blueprint ``\\lean{...}`` payloads."""
    return split_tex_lean_decls(payload)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class BlueprintEntry:
    """A single blueprint environment that references a Lean declaration."""
    file: str
    line: int
    env_type: str          # definition, theorem, lemma, …
    label: str | None
    lean_decl: str         # the \lean{X} name
    has_leanok: bool       # whether \leanok appears on the statement
    proof_has_leanok: bool  # whether the proof block has \leanok


@dataclass
class LeanDecl:
    """A Lean declaration found in the source tree."""
    file: str
    line: int
    fqn: str  # fully-qualified name including namespace
    kind: str
    short_name: str
    end_line: int
    is_private: bool = False  # declaration carries the `private` modifier


@dataclass
class SyncReport:
    """Aggregated sync report."""
    blueprint_entries: list[BlueprintEntry] = field(default_factory=list)
    lean_decls: dict[str, LeanDecl] = field(default_factory=dict)
    # Problems
    missing_in_lean: list[BlueprintEntry] = field(default_factory=list)
    leanok_but_missing: list[BlueprintEntry] = field(default_factory=list)
    stale_lean_decls: list[str] = field(default_factory=list)
    missing_from_lean_decls_file: list[str] = field(default_factory=list)
    duplicate_lean_tags: list[tuple[str, list[BlueprintEntry]]] = field(
        default_factory=list
    )
    # Whether duplicate ownership tags count as a failure.  The ownership
    # convention is recorded in
    # docs/audits/2026-08-20_blueprint_declaration_ownership.md.
    duplicate_tags_are_errors: bool = False

    @property
    def ok(self) -> bool:
        return not (
            self.missing_in_lean
            or self.leanok_but_missing
            or self.stale_lean_decls
            or self.missing_from_lean_decls_file
            or (self.duplicate_tags_are_errors and self.duplicate_lean_tags)
        )


# ---------------------------------------------------------------------------
# Parse Lean source tree
# ---------------------------------------------------------------------------

def _mask_lean_noncode(text: str) -> str:
    """Mask nested comments/string contents, preserving line/column positions.

    String delimiters remain as invalid attribute syntax, so a string cannot
    accidentally turn an unsupported attribute into a bare to_additive.
    """
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                if i + 1 < len(text) and text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            i += 1
        else:
            i += 1
    return "".join(out)


_ADDITIVE_ATTACHED_RE = re.compile(
    r"(?P<attrs>(?:@\[[^\[\]]*\]\s*)+)"
    r"(?P<mods>(?:(?:private|protected|noncomputable)\s+)*)"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[\w']+(?:\.[\w']+)*)", re.MULTILINE,
)


@dataclass
class AdditiveRules:
    words: dict[str, list[str]]
    abbreviations: set[str]
    blocked_prefixes: set[str] = field(default_factory=set)
    hinted_words: set[str] = field(default_factory=set)


def _native_additive_rules(mathlib_root: Path) -> AdditiveRules | None:
    """Read the literal native dictionaries from the verified Mathlib source.

    Translate/GuessName.lean splits snake_case at underscores and applies
    nameDict word-by-word. We decline mixed-case names, name hints and every
    candidate potentially affected by abbreviationDict, rather than emulate
    Lean's environment or its complete naming algorithm.
    """
    try:
        text = (mathlib_root / "Tactic/Translate/ToAdditive.lean").read_text()
        words_block = text.split("def nameDict :", 1)[1].split("def abbreviationDict :", 1)[0]
        abbrev_block = text.split("def abbreviationDict :", 1)[1].split("initialize guessNameExt", 1)[0]
        words = {key: re.findall(r'"([^"\n]+)"', values)
                 for key, values in re.findall(r'\("([^"\n]+)", \[([^\]]+)\]\)', words_block)}
        abbreviations = {key.replace("_", "").lower()
                         for key in re.findall(r'\("([^"\n]+)", "[^"\n]+"\)', abbrev_block)}
        if not words or not abbreviations:
            return None
        return AdditiveRules(words, abbreviations)
    except (OSError, IndexError):
        return None


def _additive_target(source: str, attrs: str, rules: AdditiveRules) -> str | None:
    attrs = re.findall(r"@\[([^\[\]]*)\]", attrs)
    additive = [a.strip() for a in attrs if re.match(r"\s*to_additive\b", a)]
    if len(additive) != 1:
        return None
    match = re.fullmatch(r"to_additive(?:\s+([\w']+(?:\.[\w']+)*))?", additive[0])
    if not match:
        return None  # options, chained attributes, self/none/existing: unsupported
    explicit = match.group(1)
    if explicit in {"self", "none", "existing"}:
        return None
    if explicit and explicit.startswith("_root_."):
        return explicit.removeprefix("_root_.")
    namespace, _, name = source.rpartition(".")
    prefixes = [".".join(namespace.split(".")[:i])
                for i in range(1, len(namespace.split(".")) + 1)]
    if any(".".join(p.split(".")[i:]) in rules.blocked_prefixes
           for p in prefixes for i in range(len(p.split(".")))):
        return None  # namespace translation requires the elaborated environment
    if explicit:
        # Core.targetName replaces as many trailing namespace components as
        # the explicit target supplies; _root_ disables that heuristic above.
        parts = namespace.split(".") if namespace else []
        count = len(explicit.split(".")) - 1
        return ".".join(parts[:max(0, len(parts) - count)] + [explicit])
    if not re.fullmatch(r"[a-z]+(?:_[a-z]+)+", name):
        return None
    tokens = name.split("_")
    if any(h in name.replace("_", "") for h in rules.hinted_words):
        return None
    translated = []
    for token in tokens:
        values = rules.words.get(token, [token])
        if len(values) != 1:
            return None
        value = values[0][:1].lower() + values[0][1:]
        if not value.islower() or not value.isalpha():
            return None
        translated.append(value)
    target = "_".join(translated)
    if target == name or any(a in target.replace("_", "") for a in rules.abbreviations):
        return None
    return ".".join(filter(None, (namespace, target)))


def collect_file_lean_decls(
    lean_file: Path, lean_root: Path, *, additive_rules: AdditiveRules | None = None,
) -> list[LeanDecl]:
    """Parse one Lean file and return its declarations with approximate spans."""
    text = lean_file.read_text(errors="replace")
    source_code = _mask_lean_noncode(text)
    lines = source_code.splitlines()
    raw_lines = text.splitlines()
    rel = str(lean_file.relative_to(lean_root.parent))

    # Track namespace and section stacks separately.
    ns_stack: list[str] = []
    section_stack: list[str] = []
    decls: list[LeanDecl] = []

    for i, line in enumerate(lines, 1):
        m = _NAMESPACE_OPEN_RE.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue

        m = _SECTION_OPEN_RE.match(line)
        if m:
            section_stack.append(m.group(1))
            continue

        m = _NAMESPACE_CLOSE_RE.match(line)
        if m:
            closed = m.group(1)
            if section_stack and section_stack[-1] == closed:
                section_stack.pop()
                continue
            if ns_stack and ns_stack[-1] == closed:
                ns_stack.pop()
            elif ns_stack:
                for j in range(len(ns_stack) - 1, -1, -1):
                    if ns_stack[j] == closed:
                        ns_stack = ns_stack[:j]
                        break
            continue

        m = _LEAN_DECL_RE.match(line)
        if not m and _LEAN_DECL_KEYWORD_ONLY_RE.match(line) and i < len(lines):
            # Handle multi-line declarations where the keyword is on its own
            # line and the name is on the following line.
            m = _LEAN_DECL_RE.match(line + " " + lines[i])
        if m:
            kind = m.group(1)
            short_name = m.group(2)
            if short_name.startswith("_root_."):
                # `_root_.` escapes the enclosing namespace: the declaration's
                # fully-qualified name is exactly the remainder, independent of
                # the namespace stack (e.g. `theorem _root_.Foo.bar` inside
                # `namespace Baz` declares `Foo.bar`, not `Baz.Foo.bar`).
                short_name = short_name[len("_root_.") :]
                fqn = short_name
            else:
                prefix = ".".join(ns_stack) + "." if ns_stack else ""
                fqn = prefix + short_name
            decl_source = m.string[m.start():m.end(1) + 1]
            is_private = bool(_LEAN_PRIVATE_RE.match(decl_source))
            decls.append(
                LeanDecl(
                    file=rel,
                    line=i,
                    fqn=fqn,
                    kind=kind,
                    short_name=short_name,
                    end_line=len(lines),
                    is_private=is_private,
                )
            )

    for idx, decl in enumerate(decls):
        if idx + 1 < len(decls):
            decl.end_line = decls[idx + 1].line - 1

    # The declaration regex above finds the structure itself, but not the
    # projection declarations generated for its fields.  Scan only the source
    # span of each structure and ignore block/line comments so documentation
    # prose cannot be mistaken for a field.
    field_decls: list[LeanDecl] = []
    for decl in decls:
        if decl.kind != "structure":
            continue
        block_comment_depth = 0
        field_indent: int | None = None
        for line_no in range(decl.line + 1, decl.end_line + 1):
            raw = lines[line_no - 1]
            code_parts: list[str] = []
            cursor = 0
            while cursor < len(raw):
                if block_comment_depth:
                    nested = raw.find("/-", cursor)
                    end = raw.find("-/", cursor)
                    if nested >= 0 and (end < 0 or nested < end):
                        block_comment_depth += 1
                        cursor = nested + 2
                    elif end >= 0:
                        block_comment_depth -= 1
                        cursor = end + 2
                    else:
                        cursor = len(raw)
                    continue
                block = raw.find("/-", cursor)
                line_comment = raw.find("--", cursor)
                stops = [x for x in (block, line_comment) if x >= 0]
                stop = min(stops) if stops else len(raw)
                code_parts.append(raw[cursor:stop])
                if stop == line_comment:
                    cursor = len(raw)
                elif stop == block:
                    block_comment_depth = 1
                    cursor = stop + 2
                else:
                    cursor = len(raw)
            code = "".join(code_parts)
            match = _LEAN_STRUCTURE_FIELD_RE.match(code)
            if not match:
                continue
            # Comment stripping concatenates the surviving fragments and does
            # not preserve source columns. Lean layout uses the original line's
            # leading indentation, including for an inline field doc comment.
            indent = len(raw_lines[line_no - 1]) - len(raw_lines[line_no - 1].lstrip())
            if field_indent is None:
                field_indent = indent
            elif indent != field_indent:
                # Continuations of a field type may contain local binders such
                # as `letI : NeZero N`; only declarations aligned with the
                # structure's first field generate projections.
                continue
            field_name = match.group(1)
            field_decls.append(
                LeanDecl(
                    file=rel,
                    line=line_no,
                    fqn=f"{decl.fqn}.{field_name}",
                    kind="field",
                    short_name=field_name,
                    end_line=line_no,
                    is_private=decl.is_private,
                )
            )

    generated: list[LeanDecl] = []
    if additive_rules is not None:
        for attached in _ADDITIVE_ATTACHED_RE.finditer(source_code):
            name_line = source_code.count("\n", 0, attached.start("name")) + 1
            decl = next((d for d in decls if d.line <= name_line <= d.end_line
                         and d.short_name == attached.group("name").removeprefix("_root_.")), None)
            if decl is None or decl.is_private or "private" in attached.group("mods").split():
                continue
            target = _additive_target(decl.fqn, attached.group("attrs"), additive_rules)
            if target and target != decl.fqn:
                generated.append(LeanDecl(rel, decl.line, target, "generated", target,
                                          decl.end_line))
    return decls + field_decls + generated


def collect_lean_decls(
    lean_root: Path, *, tracked_only: bool = False,
    additive_rules: AdditiveRules | None = None,
) -> dict[str, LeanDecl]:
    """Walk all .lean files and return {fqn: LeanDecl}."""
    decls: dict[str, LeanDecl] = {}

    if tracked_only:
        tracked = _git_output(lean_root.parent, "ls-files", "-z", "--", lean_root.name)
        files = [lean_root.parent / name for name in tracked.split("\0")
                 if name.endswith(".lean")]
    else:
        files = list(lean_root.rglob("*.lean"))
    if additive_rules is not None:
        # Conservatively block every source namespace with an attached
        # translation, plus explicit namespace registrations/name hints.
        for path in files:
            if path.is_symlink() or not path.is_file():
                continue
            code = _mask_lean_noncode(path.read_text())
            declarations = collect_file_lean_decls(path, lean_root)
            attached_names = {m.group("name").removeprefix("_root_.")
                              for m in _ADDITIVE_ATTACHED_RE.finditer(code)
                              if "to_additive" in m.group("attrs")}
            additive_rules.blocked_prefixes.update(
                d.fqn for d in declarations if d.short_name in attached_names)
            additive_rules.blocked_prefixes.update(re.findall(
                r"(?m)^\s*insert_to_additive_translation\s+([\w.]+)", code))
            for targets in re.findall(
                r"(?m)^\s*attribute\s*\[[^\]\n]*\bto_additive\b[^\]\n]*\]([^\n]*)", code):
                additive_rules.blocked_prefixes.update(re.findall(r"[\w.]+", targets))
            additive_rules.hinted_words.update(w.lower() for w in re.findall(
                r"(?m)^\s*to_additive_name_hint\s+(\w+)", code))
    for lean_file in sorted(files):
        if lean_file.is_symlink() or not lean_file.is_file():
            continue
        for decl in collect_file_lean_decls(lean_file, lean_root, additive_rules=additive_rules):
            if not decl.is_private:
                decls[decl.fqn] = decl

    return decls


# ---------------------------------------------------------------------------
# Parse blueprint .tex files
# ---------------------------------------------------------------------------

def _blueprint_content_files(blueprint_src: Path) -> list[Path]:
    """Return theorem-bearing chapter and appendix sources in stable order."""
    files = list((blueprint_src / "chapter").glob("*.tex"))
    files.extend((blueprint_src / "appendix").rglob("*.tex"))
    return sorted(files)


def collect_blueprint_lean_refs(blueprint_src: Path) -> list[BlueprintEntry]:
    """Return all raw declaration references appearing in ``\\lean{...}`` tags."""
    refs: list[BlueprintEntry] = []
    for tex_file in _blueprint_content_files(blueprint_src):
        text = tex_file.read_text(errors="replace")
        rel = str(tex_file.relative_to(blueprint_src.parent))
        for lm in _TEX_LEAN_RE.finditer(text):
            line = text.count("\n", 0, lm.start()) + 1
            for decl in _split_lean_decls(lm.group(1)):
                refs.append(BlueprintEntry(
                    file=rel,
                    line=line,
                    env_type="lean-tag",
                    label=None,
                    lean_decl=decl,
                    has_leanok=False,
                    proof_has_leanok=False,
                ))
    return refs


def find_duplicate_lean_tags(
    refs: list[BlueprintEntry],
) -> list[tuple[str, list[BlueprintEntry]]]:
    """Return declarations whose ``\\lean{...}`` tag occurs in several entries.

    The blueprint convention gives every Lean declaration exactly one owning
    entry; any further entry mentioning the same declaration cites the owner
    through ``\\uses`` instead of repeating the ownership tag.  Two tags for one
    declaration make the owning entry ambiguous, so they are reported here.

    Every ``\\lean{...}`` tag counts, including one written inside a proof body:
    the convention has a proof cite the owning entry through ``\\uses``, so a
    proof-body tag repeating an owned declaration is itself a second anchor on
    that declaration rather than a citation of the owner.
    """
    occurrences: dict[str, list[BlueprintEntry]] = {}
    for ref in refs:
        occurrences.setdefault(ref.lean_decl, []).append(ref)
    return [
        (decl, entries)
        for decl, entries in sorted(occurrences.items())
        if len(entries) > 1
    ]


def collect_blueprint_entries(blueprint_src: Path) -> list[BlueprintEntry]:
    """Parse theorem-like blueprint environments for ``\\lean{}`` and ``\\leanok``."""
    entries: list[BlueprintEntry] = []
    for tex_file in _blueprint_content_files(blueprint_src):
        text = tex_file.read_text(errors="replace")
        lines = text.splitlines()
        lean_decls_by_line: dict[int, list[str]] = {}
        for lm in _TEX_LEAN_RE.finditer(text):
            start_line = text.count("\n", 0, lm.start()) + 1
            lean_decls_by_line.setdefault(start_line, []).extend(
                _split_lean_decls(lm.group(1))
            )

        # State machine: track current environment
        env_stack: list[dict] = []
        in_proof = False
        current_proof: dict | None = None
        last_env: dict | None = None  # last closed environment

        def finish_proof() -> None:
            """Attach proof ``\\leanok`` to the preceding theorem-like environment."""
            nonlocal in_proof, current_proof
            if current_proof and current_proof["has_leanok"] and last_env:
                for idx in range(last_env["_entry_start"], last_env["_entry_end"]):
                    e = entries[idx]
                    entries[idx] = BlueprintEntry(
                        file=e.file,
                        line=e.line,
                        env_type=e.env_type,
                        label=e.label,
                        lean_decl=e.lean_decl,
                        has_leanok=e.has_leanok,
                        proof_has_leanok=True,
                    )
            in_proof = False
            current_proof = None

        for i, line in enumerate(lines, 1):
            # Check for environment begin
            m = _TEX_ENV_BEGIN_RE.search(line)
            if m:
                env = {
                    "type": m.group(1),
                    "label": m.group(2),
                    "file": str(tex_file.relative_to(blueprint_src.parent)),
                    "line": i,
                    "lean_decls": [],
                    "has_leanok": bool(_TEX_LEANOK_RE.search(line)),
                }
                env_stack.append(env)
                # Check rest of line for \\lean{} and \\leanok.  Multi-line tags
                # are attributed to the line where the tag starts.
                env["lean_decls"].extend(lean_decls_by_line.get(i, []))
                continue

            # Check for environment end
            m = _TEX_ENV_END_RE.search(line)
            if m and env_stack:
                env = env_stack.pop()
                env_entry_start = len(entries)
                for decl in env["lean_decls"]:
                    entries.append(BlueprintEntry(
                        file=env["file"],
                        line=env["line"],
                        env_type=env["type"],
                        label=env["label"],
                        lean_decl=decl,
                        has_leanok=env["has_leanok"],
                        proof_has_leanok=False,
                    ))
                env["_entry_start"] = env_entry_start
                env["_entry_end"] = len(entries)
                # Only track as last_env if it produced lean entries, so an
                # intervening remark without \\lean{} doesn't steal the proof.
                if env_entry_start < len(entries):
                    last_env = env
                continue

            # Proof begin.  Handle one-line proofs such as
            # ``\\begin{proof}\\leanok ... \\end{proof}`` without leaving the parser
            # stuck inside proof mode.
            if _TEX_PROOF_BEGIN_RE.search(line):
                in_proof = True
                current_proof = {
                    "has_leanok": bool(_TEX_LEANOK_RE.search(line)),
                }
                if _TEX_PROOF_END_RE.search(line):
                    finish_proof()
                continue

            # Inside a proof block, update the proof-status flag before checking
            # for the proof end, so ``\\leanok`` and ``\\end{proof}`` may share a line.
            # Inline ``\\lean{}`` citations inside proof prose are deliberately not
            # turned into BlueprintEntry values; they are only used when checking
            # blueprint/lean_decls synchronisation via collect_blueprint_lean_refs.
            if in_proof:
                if current_proof and _TEX_LEANOK_RE.search(line):
                    current_proof["has_leanok"] = True
                if _TEX_PROOF_END_RE.search(line):
                    finish_proof()
                continue

            # Inside an environment: collect \\lean{} and \\leanok
            if env_stack:
                env_stack[-1]["lean_decls"].extend(lean_decls_by_line.get(i, []))
                if _TEX_LEANOK_RE.search(line):
                    env_stack[-1]["has_leanok"] = True

    return entries


# ---------------------------------------------------------------------------
# Read lean_decls file
# ---------------------------------------------------------------------------

def read_lean_decls_file(path: Path) -> set[str]:
    if not path.exists():
        return set()
    decls = {line.strip() for line in path.read_text().splitlines() if line.strip()}
    if not decls:
        # leanblueprint web can clobber lean_decls to empty when kpsewhich is
        # missing; fall back to the committed version so the sync check still
        # works after that step.
        try:
            out = subprocess.check_output(
                ["git", "show", "HEAD:blueprint/lean_decls"],
                cwd=path.parent.parent,
                text=True,
                stderr=subprocess.DEVNULL,
            )
            decls = {l.strip() for l in out.splitlines() if l.strip()}
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass
    return decls


def _git_diff_changed_lines(root: Path, rel_path: str, diff_base: str, diff_head: str) -> set[int]:
    """Return changed line numbers in the post-change file using `git diff -U0`."""
    try:
        diff = subprocess.check_output(
            ["git", "diff", "--unified=0", diff_base, diff_head, "--", rel_path],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as exc:
        raise RuntimeError(
            f"Could not diff {rel_path!r} between {diff_base} and {diff_head}"
        ) from exc

    changed_lines: set[int] = set()
    for line in diff.splitlines():
        m = _DIFF_HUNK_RE.match(line)
        if not m:
            continue
        start = int(m.group(1))
        count = int(m.group(2) or "1")
        if count == 0:
            continue
        changed_lines.update(range(start, start + count))
    return changed_lines


def _decl_blueprint_spellings(decl: LeanDecl) -> set[str]:
    names = {decl.fqn}
    if "." in decl.short_name:
        names.add(decl.short_name)
    return names


def find_changed_decls_missing_from_blueprint(
    root: Path,
    *,
    changed_files: list[str],
    diff_base: str,
    diff_head: str,
) -> list[LeanDecl]:
    """Return changed `def`/`theorem`/`lemma` declarations missing from blueprint."""
    lean_root = root / "TNLean"
    blueprint_src = root / "blueprint" / "src"

    blueprint_decl_names = {
        entry.lean_decl for entry in collect_blueprint_entries(blueprint_src)
    }
    missing: list[LeanDecl] = []
    seen: set[str] = set()

    for rel_path in changed_files:
        if not rel_path.endswith(".lean"):
            continue
        abs_path = root / rel_path
        if not abs_path.is_file():
            continue
        try:
            abs_path.relative_to(lean_root)
        except ValueError:
            continue

        changed_lines = _git_diff_changed_lines(root, rel_path, diff_base, diff_head)
        if not changed_lines:
            continue

        for decl in collect_file_lean_decls(abs_path, lean_root):
            if decl.kind not in _TRACKED_REVERSE_DECL_KINDS:
                continue
            if decl.is_private:
                # By project convention, `private` helpers are internal
                # proof scaffolding and do not require a blueprint anchor.
                continue
            if not any(decl.line <= line <= decl.end_line for line in changed_lines):
                continue
            if _decl_blueprint_spellings(decl) & blueprint_decl_names:
                continue
            if decl.fqn in seen:
                continue
            seen.add(decl.fqn)
            missing.append(decl)

    return missing


def print_missing_blueprint_warnings(missing: list[LeanDecl]) -> None:
    """Print a warning-only report for changed declarations missing blueprint refs."""
    print()
    print("=" * 70)
    print("  CHANGED LEAN DECLARATIONS ↔ BLUEPRINT COVERAGE")
    print("=" * 70)
    print()

    if not missing:
        print("✓ No changed def/theorem/lemma declarations are missing blueprint entries.")
        print()
        return

    print(f"WARNING: Changed declarations not yet in blueprint ({len(missing)}):")
    for decl in missing:
        print(f"  - {decl.fqn}  ({decl.file}:{decl.line})")
        if os.getenv("GITHUB_ACTIONS") == "true":
            print(
                "::warning "
                f"file={decl.file},line={decl.line},title=Blueprint update suggested::"
                f"{decl.fqn} is changed in this PR but has no corresponding "
                "\\lean{} tag in blueprint/src/chapter or blueprint/src/appendix."
            )
    print()


def _dependency_fetch_enabled() -> bool:
    """Network access requires an explicit opt-in, including on CI."""
    return os.getenv("BLUEPRINT_SYNC_FETCH_DEPS") == "1"


def _git_output(package_dir: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(package_dir), *args], stderr=subprocess.DEVNULL,
        text=True, timeout=30,
    ).strip()


def _verified_dependency(package_dir: Path, rev: str) -> bool:
    """Require an independent Git checkout at the exact clean manifest commit."""
    try:
        return (
            Path(_git_output(package_dir, "rev-parse", "--show-toplevel")).resolve()
            == package_dir.resolve()
            and _git_output(package_dir, "rev-parse", "HEAD") == rev
            and not _git_output(package_dir, "status", "--porcelain", "--untracked-files=all")
        )
    except (OSError, subprocess.SubprocessError):
        return False


def _fetch_dependency_sources(package_dir: Path, url: str, rev: str) -> bool:
    """Stage an exact commit; never use a branch fallback or alter an existing checkout."""
    if package_dir.exists() or package_dir.is_symlink() or not re.fullmatch(r"[0-9a-f]{40}", rev):
        return False
    package_dir.parent.mkdir(parents=True, exist_ok=True)
    try:
        with tempfile.TemporaryDirectory(dir=package_dir.parent) as tmp:
            staged = Path(tmp) / "source"
            subprocess.run(["git", "init", "-q", str(staged)], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            for args in (("fetch", "--depth", "1", "--", url, rev),
                         ("checkout", "--detach", rev)):
                subprocess.run(["git", "-C", str(staged), *args], check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               timeout=120)
            if not _verified_dependency(staged, rev):
                return False
            if package_dir.exists() or package_dir.is_symlink():
                return False
            staged.rename(package_dir)
            return True
    except (OSError, subprocess.SubprocessError):
        return False


def _resolve_dependency_lean_root(root: Path, package_name: str) -> Path | None:
    """Resolve only the two named libraries, at clean exact manifest Git SHAs."""
    library = {"qiclean": "QICLean", "mathlib": "Mathlib"}.get(package_name)
    if library is None:
        return None
    try:
        manifest = json.loads((root / "lake-manifest.json").read_text())
        entries = [p for p in manifest["packages"] if p.get("name") == package_name]
        if len(entries) != 1:
            raise ValueError("expected one manifest entry")
        entry = entries[0]
        rev = entry.get("rev", "")
        if entry.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", rev):
            raise ValueError("dependency must have an exact Git commit")
        packages_dir = manifest.get("packagesDir", ".lake/packages")
        if (not isinstance(packages_dir, str) or not packages_dir
                or Path(packages_dir).is_absolute() or ".." in Path(packages_dir).parts):
            raise ValueError("packagesDir must be a relative path without '..'")
        if entry.get("subDir") not in (None, ""):
            raise ValueError("dependency subDir is unsupported")
        package_dir = root / packages_dir / package_name
        if not package_dir.exists() and _dependency_fetch_enabled():
            url = entry.get("url")
            if not isinstance(url, str) or not _fetch_dependency_sources(package_dir, url, rev):
                raise ValueError("exact source fetch failed")
        if not _verified_dependency(package_dir, rev):
            raise ValueError("checkout unavailable, dirty, not independent, or at the wrong commit")
        library_root = package_dir / library
        if not library_root.is_dir() or library_root.is_symlink():
            raise ValueError("expected library directory unavailable")
        return library_root
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print(f"  (dependency '{package_name}' skipped: {error})")
        return None


# ---------------------------------------------------------------------------
# Run sync check
# ---------------------------------------------------------------------------

def run_sync(
    root: Path,
    *,
    report_file: Path | None = None,
    update_lean_decls: bool = False,
    report_duplicate_tags: bool = False,
) -> SyncReport:
    lean_root = root / "TNLean"
    blueprint_src = root / "blueprint" / "src"
    lean_decls_path = root / "blueprint" / "lean_decls"

    if not lean_root.is_dir():
        raise FileNotFoundError(f"Lean source directory not found: {lean_root}")
    if not blueprint_src.is_dir():
        raise FileNotFoundError(f"Blueprint source directory not found: {blueprint_src}")

    report = SyncReport(duplicate_tags_are_errors=report_duplicate_tags)

    # 1. Resolve citations directly into the QICLean and Mathlib dependencies.
    # A migrated declaration needs no local compatibility wrapper merely to
    # satisfy this source check. Scan only these mathematical libraries, not
    # every Lake package; TNLean takes precedence, then QICLean, then Mathlib.
    print("Scanning Lean source tree …")
    report.lean_decls = collect_lean_decls(lean_root)
    print(f"  Found {len(report.lean_decls)} declarations in Lean source")
    for package_name in ("qiclean", "mathlib"):
        dependency_root = _resolve_dependency_lean_root(root, package_name)
        if dependency_root is None:
            continue
        rules = _native_additive_rules(dependency_root) if package_name == "mathlib" else None
        dependency_decls = collect_lean_decls(
            dependency_root, tracked_only=True, additive_rules=rules)
        added = 0
        for fqn, decl in dependency_decls.items():
            if fqn not in report.lean_decls:
                report.lean_decls[fqn] = decl
                added += 1
        print(
            f"  Found {len(dependency_decls)} declarations in the {package_name} "
            f"dependency ({added} new)"
        )

    # 2. Collect blueprint entries and raw tag names
    print("Scanning blueprint .tex files …")
    all_blueprint_refs = collect_blueprint_lean_refs(blueprint_src)
    all_blueprint_decl_names = {ref.lean_decl for ref in all_blueprint_refs}
    report.blueprint_entries = collect_blueprint_entries(blueprint_src)
    report.duplicate_lean_tags = find_duplicate_lean_tags(all_blueprint_refs)
    print(f"  Found {len(all_blueprint_decl_names)} unique \\lean{{}} references in blueprint")
    print(f"  Found {len(report.blueprint_entries)} theorem-like blueprint entries")

    # 3. Cross-reference all raw \\lean{} tags against Lean.  Only theorem-like
    # entries contribute to formalization statistics and \\leanok accounting, but
    # proof-prose citations should still fail CI if their declaration name is stale
    # or misspelled.
    missing_seen: set[str] = set()
    for entry in report.blueprint_entries:
        if entry.lean_decl not in report.lean_decls:
            report.missing_in_lean.append(entry)
            missing_seen.add(entry.lean_decl)
            if entry.has_leanok:
                report.leanok_but_missing.append(entry)
    for ref in all_blueprint_refs:
        if ref.lean_decl not in report.lean_decls and ref.lean_decl not in missing_seen:
            report.missing_in_lean.append(ref)
            missing_seen.add(ref.lean_decl)

    # 4. Optionally update lean_decls before checking its generated contents.
    # The report should describe the post-update state, not stale metadata read
    # before this command rewrote the file.
    if update_lean_decls:
        sorted_decls = sorted(all_blueprint_decl_names)
        lean_decls_path.write_text("\n".join(sorted_decls) + "\n")
        print(f"  Updated {lean_decls_path} with {len(sorted_decls)} entries")

    # 5. Check lean_decls file against every raw \\lean{} tag, including inline
    # proof-prose citations that leanblueprint records in blueprint/lean_decls.
    #
    # The file is generated by CI and ignored locally.  In a clean checkout it
    # may therefore be absent; in that case, the Lean-vs-blueprint check above
    # is still meaningful, but lean_decls drift is not.
    if lean_decls_path.exists():
        existing_lean_decls = read_lean_decls_file(lean_decls_path)
        for name in sorted(existing_lean_decls - all_blueprint_decl_names):
            report.stale_lean_decls.append(name)
        for name in sorted(all_blueprint_decl_names - existing_lean_decls):
            report.missing_from_lean_decls_file.append(name)

    # 6. Print report
    _print_report(report, root)

    # 7. Write JSON report
    if report_file:
        _write_json_report(report, report_file, root)

    return report


def _chapter_stats(report: SyncReport) -> dict[str, dict]:
    """Per-chapter formalization progress."""
    stats: dict[str, dict] = {}
    for entry in report.blueprint_entries:
        chapter = entry.file
        if chapter not in stats:
            stats[chapter] = {
                "total": 0,
                "formalized": 0,
                "proof_formalized": 0,
                "missing_lean": 0,
            }
        s = stats[chapter]
        s["total"] += 1
        found = entry.lean_decl in report.lean_decls
        if entry.has_leanok and found:
            s["formalized"] += 1
        if entry.proof_has_leanok and found:
            s["proof_formalized"] += 1
        if not found:
            s["missing_lean"] += 1
    return stats


def _print_report(report: SyncReport, root: Path) -> None:
    print()
    print("=" * 70)
    print("  BLUEPRINT ↔ LEAN SYNC REPORT")
    print("=" * 70)

    # Per-chapter stats
    stats = _chapter_stats(report)
    print()
    print("Per-chapter formalization progress:")
    print(f"  {'Chapter':<50} {'Done':>5} / {'Total':>5}  {'%':>6}")
    print("  " + "-" * 68)
    total_done = 0
    total_all = 0
    for chapter in sorted(stats):
        s = stats[chapter]
        pct = 100 * s["formalized"] / s["total"] if s["total"] else 0
        short = chapter.replace("src/chapter/", "")
        print(f"  {short:<50} {s['formalized']:>5} / {s['total']:>5}  {pct:>5.1f}%")
        total_done += s["formalized"]
        total_all += s["total"]
    pct = 100 * total_done / total_all if total_all else 0
    print("  " + "-" * 68)
    print(f"  {'TOTAL':<50} {total_done:>5} / {total_all:>5}  {pct:>5.1f}%")

    # Missing in Lean
    if report.missing_in_lean:
        print()
        print(f"Blueprint refs with NO matching Lean declaration ({len(report.missing_in_lean)}):")
        seen: set[str] = set()
        for entry in report.missing_in_lean:
            if entry.lean_decl not in seen:
                seen.add(entry.lean_decl)
                ok_tag = " [has \\leanok!]" if entry.has_leanok else ""
                print(f"  ✗ {entry.lean_decl}{ok_tag}")
                print(f"    {entry.file}:{entry.line} ({entry.env_type})")

    # leanok but missing
    if report.leanok_but_missing:
        print()
        print(
            "WARNING: \\leanok on items whose Lean decl is MISSING "
            f"({len(report.leanok_but_missing)}):"
        )
        seen2: set[str] = set()
        for entry in report.leanok_but_missing:
            if entry.lean_decl not in seen2:
                seen2.add(entry.lean_decl)
                print(f"  ⚠ {entry.lean_decl}  ({entry.file}:{entry.line})")

    # Stale lean_decls
    if report.stale_lean_decls:
        print()
        print(f"Stale entries in lean_decls (not in any .tex) ({len(report.stale_lean_decls)}):")
        for name in report.stale_lean_decls:
            print(f"  − {name}")

    # Missing from lean_decls
    if report.missing_from_lean_decls_file:
        print()
        print(
            "Blueprint refs missing from lean_decls file "
            f"({len(report.missing_from_lean_decls_file)}):"
        )
        for name in report.missing_from_lean_decls_file:
            print(f"  + {name}")

    # Duplicate ownership tags
    if report.duplicate_lean_tags:
        print()
        marker = "✗" if report.duplicate_tags_are_errors else "⚠"
        print(
            "Declarations tagged in more than one blueprint entry "
            f"({len(report.duplicate_lean_tags)}):"
        )
        for decl, entries in report.duplicate_lean_tags:
            print(f"  {marker} {decl}")
            for entry in entries:
                print(f"    {entry.file}:{entry.line}")

    # Summary
    print()
    if report.ok:
        print("✓ Blueprint and Lean code are in sync.")
    else:
        problems = (
            len(report.missing_in_lean)
            + len(report.stale_lean_decls)
            + len(report.missing_from_lean_decls_file)
        )
        if report.duplicate_tags_are_errors:
            problems += len(report.duplicate_lean_tags)
        print(f"✗ Found {problems} sync issue(s). See details above.")
    print()


def _write_json_report(report: SyncReport, path: Path, root: Path) -> None:
    data = {
        "sync_ok": report.ok,
        "total_blueprint_refs": len(report.blueprint_entries),
        "total_lean_decls": len(report.lean_decls),
        "missing_in_lean": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line, "has_leanok": e.has_leanok}
            for e in report.missing_in_lean
        ],
        "leanok_but_missing": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line}
            for e in report.leanok_but_missing
        ],
        "duplicate_lean_tags": [
            {
                "decl": decl,
                "entries": [{"file": e.file, "line": e.line} for e in entries],
            }
            for decl, entries in report.duplicate_lean_tags
        ],
        "stale_lean_decls": report.stale_lean_decls,
        "missing_from_lean_decls_file": report.missing_from_lean_decls_file,
        "chapter_stats": _chapter_stats(report),
    }
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"JSON report written to {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check synchronisation between blueprint .tex and Lean source."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: auto-detected)",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="Write JSON report to this file",
    )
    parser.add_argument(
        "--update-lean-decls",
        action="store_true",
        help="Rewrite blueprint/lean_decls from current .tex refs",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit with code 1 on mismatches (for CI)",
    )
    parser.add_argument(
        "--report-duplicate-tags",
        action="store_true",
        help=(
            "Treat a declaration tagged in more than one blueprint entry as a "
            "mismatch; without this flag such declarations are only listed"
        ),
    )
    parser.add_argument(
        "--warn-missing-blueprint",
        action="store_true",
        help=(
            "Warn about changed def/theorem/lemma declarations in changed Lean files "
            "that have no corresponding \\lean{} tag in blueprint chapters"
        ),
    )
    parser.add_argument(
        "--changed-files",
        nargs="*",
        default=None,
        help="Changed Lean files to inspect for reverse blueprint coverage",
    )
    parser.add_argument(
        "--diff-base",
        default=None,
        help="Git base revision for reverse blueprint coverage checks",
    )
    parser.add_argument(
        "--diff-head",
        default="HEAD",
        help="Git head revision for reverse blueprint coverage checks (default: HEAD)",
    )
    args = parser.parse_args()

    should_run_sync = (
        args.update_lean_decls
        or args.ci
        or args.report is not None
        or not args.warn_missing_blueprint
    )

    if should_run_sync:
        report = run_sync(
            args.root,
            report_file=args.report,
            update_lean_decls=args.update_lean_decls,
            report_duplicate_tags=args.report_duplicate_tags,
        )
        if args.ci and not report.ok:
            sys.exit(1)

    if args.warn_missing_blueprint:
        if not args.changed_files:
            parser.error("--warn-missing-blueprint requires --changed-files")
        if not args.diff_base:
            parser.error("--warn-missing-blueprint requires --diff-base")
        missing = find_changed_decls_missing_from_blueprint(
            args.root,
            changed_files=args.changed_files,
            diff_base=args.diff_base,
            diff_head=args.diff_head,
        )
        print_missing_blueprint_warnings(missing)


if __name__ == "__main__":
    main()
