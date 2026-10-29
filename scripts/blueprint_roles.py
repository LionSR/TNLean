#!/usr/bin/env python3
"""Set blueprint theorem-like environments by mathematical role.

Rule 8 of ``docs/blueprint_style_guide.md``: ``\\begin{theorem}`` is reserved
for the results a chapter exists to prove, ``\\begin{corollary}`` for direct
consequences of such a theorem, and ``\\begin{lemma}`` for every supporting
result; ``\\begin{proposition}`` is never used.

The roles live in a data file (default ``blueprint/roles.json``)::

    {
      "chapters": {
        "<chapter label>": {
          "theorems": ["thm:...", ...],
          "corollaries": ["cor:...", ...],
          "notes": {"thm:...": "why this is a main result"}
        }
      }
    }

Roles are keyed by the *entry label*, never by file path: the chapter key is
only a grouping used in reports, so the data stays valid when files move
between chapters or chapters are renamed.  A label listed under some
chapter's ``theorems`` gets ``theorem``; under ``corollaries`` gets
``corollary``; every other theorem-like environment (``theorem``,
``proposition``, ``lemma``, ``corollary``) gets ``lemma``.  Definitions,
remarks and examples are never touched, and labels are never renamed.

After the environments are fixed, prose references across every
``blueprint/src/**/*.tex`` file are rewritten from the final environment of
the referenced label: ``Theorem~\\ref{x}`` becomes ``Lemma~\\ref{x}`` when
``x`` is a lemma, plural lists such as ``Theorems~\\ref{a} and~\\ref{b}``
become ``Lemmas~...`` when every member agrees, and mixed lists are reported
rather than guessed.

Modes:

``--check``    exit 1 and list every environment or prose reference that
               disagrees with the data file (no files written);
``--dry-run``  print per-chapter counts before and after (no files written);
``--apply``    rewrite the files, after verifying in memory that every
               ``\\label``, ``\\lean`` name, ``\\uses`` entry, ``\\leanok`` and
               proof environment is conserved;
``--verify``   compare those tags between the working tree and ``--base``.
"""

from __future__ import annotations

import argparse
import bisect
from collections import Counter, defaultdict
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SRC = REPO_ROOT / "blueprint" / "src"
DEFAULT_ROLES = REPO_ROOT / "blueprint" / "roles.json"
DEFAULT_ENTRY = "content.tex"

THEOREM_LIKE = ("theorem", "proposition", "lemma", "corollary")

WORD_FORMS = {
    "theorem": ("Theorem", "Theorems"),
    "proposition": ("Proposition", "Propositions"),
    "lemma": ("Lemma", "Lemmas"),
    "corollary": ("Corollary", "Corollaries"),
}
WORD_TO_ENV: dict[str, tuple[str, bool]] = {}
for _env, (_sing, _plur) in WORD_FORMS.items():
    WORD_TO_ENV[_sing] = (_env, False)
    WORD_TO_ENV[_plur] = (_env, True)

TOKEN_RE = re.compile(
    r"\\(?P<kind>begin|end)\{(?P<env>[^}]*)\}"
    r"|\\label\{(?P<label>[^}]*)\}"
    r"|\\(?:input|include)\{(?P<input>[^}]*)\}"
    r"|\\chapter\*?(?:\[[^\]]*\])?\{"
)

# A reference word, the gap before ``\ref`` (a tie, spaces, or one line
# break), and a list of ``\ref``s joined by commas, ``and`` or ``--``.
REF_LIST_RE = re.compile(
    r"\b(?P<word>Theorems?|Propositions?|Lemmas?|Corollary|Corollaries)"
    r"(?P<gap>~|[ \t]+|[ \t]*\n[ \t]*)"
    r"(?P<refs>\\ref\{[^}]*\}"
    r"(?:(?:\s*,\s*(?:and\b\s*)?|\s+and\b\s*|\s*--\s*)~?\s*\\ref\{[^}]*\})*)"
)
REF_RE = re.compile(r"\\ref\{([^}]*)\}")

TAG_PATTERNS = {
    "label": re.compile(r"\\label\{([^}]*)\}"),
    "lean": re.compile(r"\\lean\{([^}]*)\}"),
    "uses": re.compile(r"\\uses\{([^}]*)\}"),
}
LEANOK_RE = re.compile(r"\\leanok\b")
PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
PROOF_END_RE = re.compile(r"\\end\{proof\}")


# ---------------------------------------------------------------------------
# Low-level TeX scanning


def comment_mask(text: str) -> list[tuple[int, int]]:
    """Return the ``(start, end)`` spans of TeX comments in ``text``."""
    spans: list[tuple[int, int]] = []
    pos = 0
    for line in text.splitlines(keepends=True):
        if "%" not in line:
            pos += len(line)
            continue
        i = 0
        while i < len(line):
            ch = line[i]
            if ch == "\\":
                i += 2
                continue
            if ch == "%":
                end = pos + len(line.rstrip("\n"))
                spans.append((pos + i, end))
                break
            i += 1
        pos += len(line)
    return spans


class CommentIndex:
    """Fast membership test for positions inside comments."""

    def __init__(self, text: str) -> None:
        self.spans = comment_mask(text)
        self.starts = [s for s, _ in self.spans]

    def __contains__(self, pos: int) -> bool:
        i = bisect.bisect_right(self.starts, pos) - 1
        return i >= 0 and self.spans[i][0] <= pos < self.spans[i][1]


def read_braced(text: str, open_pos: int) -> tuple[str, int]:
    """Return the contents of the brace group whose ``{`` is at ``open_pos``."""
    depth = 0
    i = open_pos
    while i < len(text):
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[open_pos + 1 : i], i + 1
        i += 1
    return text[open_pos + 1 :], len(text)


@dataclass
class Env:
    """One theorem-like environment in one file."""

    path: Path
    name: str
    begin_name_span: tuple[int, int]
    end_name_span: tuple[int, int]
    begin_pos: int
    line: int
    labels: list[str] = field(default_factory=list)
    caption: str = ""
    chapter: str | None = None

    @property
    def label(self) -> str | None:
        """The entry's own label: the first one in its body."""
        return self.labels[0] if self.labels else None


@dataclass
class FileScan:
    path: Path
    text: str
    envs: list[Env] = field(default_factory=list)
    # Ordered events for chapter assignment: (pos, kind, payload).
    events: list[tuple[int, str, object]] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def scan_file(path: Path, text: str) -> FileScan:
    """Pair every ``\\begin``/``\\end`` and record theorem-like environments.

    The labels of an environment are those that sit directly in its body,
    outside any nested environment; the first is its own label.
    """
    scan = FileScan(path, text)
    comments = CommentIndex(text)
    stack: list[tuple[str, int, Env | None]] = []
    for m in TOKEN_RE.finditer(text):
        if m.start() in comments:
            continue
        if m.group("kind"):
            env = m.group("env")
            name_span = m.span("env")
            if m.group("kind") == "begin":
                record: Env | None = None
                if env in THEOREM_LIKE:
                    record = Env(
                        path=path,
                        name=env,
                        begin_name_span=name_span,
                        end_name_span=(-1, -1),
                        begin_pos=m.start(),
                        line=line_of(text, m.start()),
                    )
                    rest = text[m.end() : m.end() + 2000]
                    cap = re.match(r"\s*\[", rest)
                    if cap:
                        depth, j = 0, cap.end() - 1
                        while j < len(rest):
                            if rest[j] == "[":
                                depth += 1
                            elif rest[j] == "]":
                                depth -= 1
                                if depth == 0:
                                    break
                            j += 1
                        record.caption = " ".join(rest[cap.end() : j].split())
                    scan.events.append((m.start(), "env", record))
                stack.append((env, m.start(), record))
            else:
                if not stack:
                    scan.errors.append(
                        f"{path}:{line_of(text, m.start())}: unmatched \\end{{{env}}}"
                    )
                    continue
                top_env, top_pos, record = stack.pop()
                if top_env != env:
                    scan.errors.append(
                        f"{path}:{line_of(text, m.start())}: \\end{{{env}}} closes "
                        f"\\begin{{{top_env}}} from line {line_of(text, top_pos)}"
                    )
                if record is not None:
                    record.end_name_span = name_span
                    scan.envs.append(record)
        elif m.group("label") is not None:
            if stack and stack[-1][2] is not None:
                stack[-1][2].labels.append(m.group("label").strip())
            scan.events.append((m.start(), "label", m.group("label").strip()))
        elif m.group("input") is not None:
            scan.events.append((m.start(), "input", m.group("input").strip()))
        else:  # \chapter{
            title, _ = read_braced(text, m.end() - 1)
            scan.events.append((m.start(), "chapter", " ".join(title.split())))
    for env, pos, _ in stack:
        scan.errors.append(f"{path}:{line_of(text, pos)}: unclosed \\begin{{{env}}}")
    scan.envs.sort(key=lambda e: e.begin_pos)
    return scan


# ---------------------------------------------------------------------------
# Blueprint model


@dataclass
class Chapter:
    key: str
    title: str
    label: str | None
    files: list[Path] = field(default_factory=list)


class Blueprint:
    """All ``.tex`` files under ``src`` with chapter assignment from ``entry``."""

    def __init__(self, src: Path, entry: str = DEFAULT_ENTRY,
                 texts: dict[Path, str] | None = None) -> None:
        self.src = src
        if texts is None:
            texts = {p: p.read_text(encoding="utf-8") for p in tex_files(src)}
        self.texts = texts
        self.scans = {p: scan_file(p, t) for p, t in texts.items()}
        self.chapters: list[Chapter] = []
        self.warnings: list[str] = []
        self._assign_chapters(src / entry)

    def _resolve(self, name: str) -> Path | None:
        cand = self.src / name
        if cand.suffix != ".tex":
            cand = cand.with_name(cand.name + ".tex")
        return cand if cand in self.scans else None

    def _assign_chapters(self, entry: Path) -> None:
        current: list[Chapter | None] = [None]
        visited: set[Path] = set()
        pending_label = [False]

        def walk(path: Path) -> None:
            if path in visited:
                self.warnings.append(f"{path} is input more than once")
                return
            visited.add(path)
            scan = self.scans[path]
            for _, kind, payload in sorted(scan.events, key=lambda e: e[0]):
                if kind == "chapter":
                    ch = Chapter(key=str(payload), title=str(payload), label=None)
                    self.chapters.append(ch)
                    current[0] = ch
                    pending_label[0] = True
                    if path not in ch.files:
                        ch.files.append(path)
                elif kind == "label":
                    if pending_label[0] and current[0] is not None:
                        current[0].label = str(payload)
                        current[0].key = str(payload)
                    pending_label[0] = False
                elif kind == "env":
                    pending_label[0] = False
                    assert isinstance(payload, Env)
                    if current[0] is not None:
                        payload.chapter = current[0].key
                        if path not in current[0].files:
                            current[0].files.append(path)
                elif kind == "input":
                    pending_label[0] = False
                    target = self._resolve(str(payload))
                    if target is None:
                        self.warnings.append(f"{path}: cannot resolve \\input{{{payload}}}")
                        continue
                    if current[0] is not None and target not in current[0].files:
                        current[0].files.append(target)
                    walk(target)

        if entry in self.scans:
            walk(entry)
        else:
            self.warnings.append(f"entry file {entry} not found")
        self.unreached = sorted(p for p in self.scans if p not in visited)

    @property
    def envs(self) -> list[Env]:
        return [e for p in sorted(self.scans) for e in self.scans[p].envs]

    def errors(self) -> list[str]:
        return [err for p in sorted(self.scans) for err in self.scans[p].errors]

    def label_envs(self) -> dict[str, str]:
        """Map each label of a theorem-like entry to its current environment."""
        return {label: e.name for e in self.envs for label in e.labels}


def tex_files(src: Path) -> list[Path]:
    """Blueprint sources, skipping hidden build caches such as ``.tenkz_svg_cache``."""
    return sorted(
        p for p in src.rglob("*.tex")
        if p.is_file() and not any(part.startswith(".") for part in p.relative_to(src).parts)
    )


# ---------------------------------------------------------------------------
# Roles


@dataclass
class Roles:
    theorems: dict[str, str]  # label -> chapter key in the data file
    corollaries: dict[str, str]
    notes: dict[str, str]
    problems: list[str]

    def target(self, env: Env) -> str:
        """The environment an entry should use, from any of its labels."""
        if any(label in self.theorems for label in env.labels):
            return "theorem"
        if any(label in self.corollaries for label in env.labels):
            return "corollary"
        return "lemma"


def load_roles(path: Path) -> Roles:
    data = json.loads(path.read_text(encoding="utf-8"))
    theorems: dict[str, str] = {}
    corollaries: dict[str, str] = {}
    notes: dict[str, str] = {}
    problems: list[str] = []
    for chapter, entry in data.get("chapters", {}).items():
        for kind, store in (("theorems", theorems), ("corollaries", corollaries)):
            for label in entry.get(kind, []):
                if label in theorems or label in corollaries:
                    problems.append(f"roles: {label} is listed more than once")
                store[label] = chapter
        for label, note in entry.get("notes", {}).items():
            notes[label] = note
    return Roles(theorems, corollaries, notes, problems)


def validate_roles(bp: Blueprint, roles: Roles) -> list[str]:
    problems = list(roles.problems)
    label_envs = bp.label_envs()
    for label in list(roles.theorems) + list(roles.corollaries):
        if label not in label_envs:
            problems.append(f"roles: {label} is not the label of a theorem-like entry")
    return problems


# ---------------------------------------------------------------------------
# Transformation


@dataclass
class RefChange:
    path: Path
    line: int
    old: str
    new: str


@dataclass
class Result:
    texts: dict[Path, str]
    env_changes: list[tuple[Env, str]]
    ref_changes: list[RefChange]
    mixed_refs: list[str]


def set_environments(bp: Blueprint, roles: Roles) -> tuple[dict[Path, str], list[tuple[Env, str]]]:
    new_texts: dict[Path, str] = {}
    changes: list[tuple[Env, str]] = []
    for path, scan in bp.scans.items():
        edits: list[tuple[int, int, str]] = []
        for env in scan.envs:
            target = roles.target(env)
            if target != env.name:
                changes.append((env, target))
                edits.append((*env.begin_name_span, target))
                edits.append((*env.end_name_span, target))
        new_texts[path] = apply_edits(scan.text, edits)
    return new_texts, changes


def apply_edits(text: str, edits: Iterable[tuple[int, int, str]]) -> str:
    out = text
    for start, end, repl in sorted(edits, key=lambda e: e[0], reverse=True):
        out = out[:start] + repl + out[end:]
    return out


def rewrite_refs(
    texts: dict[Path, str], final_envs: dict[str, str], root: Path | None = None
) -> tuple[dict[Path, str], list[RefChange], list[str]]:
    """Rewrite reference words from the final environment of each label."""
    out: dict[Path, str] = {}
    changes: list[RefChange] = []
    mixed: list[str] = []
    for path, text in texts.items():
        edits: list[tuple[int, int, str]] = []
        for m in REF_LIST_RE.finditer(text):
            word = m.group("word")
            _, plural = WORD_TO_ENV[word]
            labels = REF_RE.findall(m.group("refs"))
            envs = {final_envs.get(lbl.strip()) for lbl in labels}
            if envs == {None}:
                continue  # references only non-theorem-like labels
            if None in envs or len(envs) > 1:
                wanted = sorted(e or "other" for e in envs)
                current = WORD_TO_ENV[word][0]
                if {e for e in envs if e} != {current}:
                    shown = path.relative_to(root) if root else path
                    mixed.append(
                        f"{shown}:{line_of(text, m.start())}: "
                        f"{' '.join(m.group(0).split())!r} refers to {', '.join(wanted)}"
                    )
                continue
            (env,) = envs
            new_word = WORD_FORMS[env][1 if plural else 0]
            if new_word != word:
                edits.append((m.start("word"), m.end("word"), new_word))
                changes.append(
                    RefChange(path, line_of(text, m.start()), m.group(0),
                              new_word + m.group(0)[len(word):])
                )
        out[path] = apply_edits(text, edits)
    return out, changes, mixed


def transform(bp: Blueprint, roles: Roles) -> Result:
    texts, env_changes = set_environments(bp, roles)
    final_envs = {label: roles.target(e) for e in bp.envs for label in e.labels}
    texts, ref_changes, mixed = rewrite_refs(texts, final_envs, bp.src)
    return Result(texts, env_changes, ref_changes, mixed)


# ---------------------------------------------------------------------------
# Tag conservation


def tag_summary(texts: dict[Path, str]) -> dict[str, Counter]:
    """Count every structural tag; reference words and env names excluded."""
    summary: dict[str, Counter] = {k: Counter() for k in TAG_PATTERNS}
    summary["leanok"] = Counter()
    summary["proof"] = Counter()
    summary["theorem_like"] = Counter()
    for path, text in texts.items():
        for key, pat in TAG_PATTERNS.items():
            for m in pat.finditer(text):
                for item in m.group(1).split(","):
                    item = item.strip()
                    if item:
                        summary[key][item] += 1
        summary["leanok"][str(path)] += len(LEANOK_RE.findall(text))
        summary["proof"][str(path)] += len(PROOF_BEGIN_RE.findall(text))
        summary["proof"][str(path) + ":end"] += len(PROOF_END_RE.findall(text))
        for name in THEOREM_LIKE:
            summary["theorem_like"][str(path)] += text.count("\\begin{" + name + "}")
            summary["theorem_like"][str(path) + ":end"] += text.count("\\end{" + name + "}")
    return summary


def compare_summaries(before: dict[str, Counter], after: dict[str, Counter]) -> list[str]:
    problems = []
    for key in before:
        if before[key] != after[key]:
            diff_minus = before[key] - after[key]
            diff_plus = after[key] - before[key]
            problems.append(
                f"tag conservation failed for {key}: lost {dict(diff_minus)} "
                f"gained {dict(diff_plus)}"
            )
    return problems


def strip_reference_words(text: str) -> str:
    """Normalize the text so that only environment names and reference words differ."""
    text = re.sub(r"\\(begin|end)\{(?:" + "|".join(THEOREM_LIKE) + r")\}", r"\\\1{THM}", text)
    return REF_LIST_RE.sub(lambda m: "WORD" + m.group(0)[len(m.group("word")):], text)


def verify_texts(before: dict[Path, str], after: dict[Path, str]) -> list[str]:
    problems = compare_summaries(tag_summary(before), tag_summary(after))
    if set(before) != set(after):
        problems.append("file sets differ")
    for path in sorted(set(before) & set(after)):
        if before[path] != after[path] and (
            strip_reference_words(before[path]) != strip_reference_words(after[path])
        ):
            problems.append(f"{path}: changes beyond environment names and reference words")
        scan = scan_file(path, after[path])
        problems.extend(scan.errors)
    return problems


def git_texts(src: Path, base: str) -> dict[Path, str]:
    rel = src.resolve().relative_to(REPO_ROOT)
    names = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-tree", "-r", "--name-only", base, str(rel)],
        check=True, capture_output=True, text=True,
    ).stdout.split()
    out: dict[Path, str] = {}
    for name in names:
        if name.endswith(".tex"):
            out[REPO_ROOT / name] = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "show", f"{base}:{name}"],
                check=True, capture_output=True, text=True,
            ).stdout
    return out


# ---------------------------------------------------------------------------
# Reports


def chapter_counts(bp: Blueprint, roles: Roles | None) -> dict[str, Counter]:
    counts: dict[str, Counter] = defaultdict(Counter)
    for env in bp.envs:
        name = roles.target(env) if roles else env.name
        counts[env.chapter or "(no chapter)"][name] += 1
    return counts


def fmt_counts(c: Counter) -> str:
    return "/".join(str(c.get(k, 0)) for k in ("theorem", "corollary", "lemma", "proposition"))


def dry_run_report(bp: Blueprint, roles: Roles, result: Result) -> str:
    before = chapter_counts(bp, None)
    after = chapter_counts(bp, roles)
    by_chapter: dict[str, list[Env]] = defaultdict(list)
    for env in bp.envs:
        by_chapter[env.chapter or "(no chapter)"].append(env)
    lines = ["counts are theorem/corollary/lemma/proposition", ""]
    keys = [ch.key for ch in bp.chapters] + (["(no chapter)"] if "(no chapter)" in by_chapter else [])
    titles = {ch.key: ch.title for ch in bp.chapters}
    seen: set[str] = set()
    for key in keys:
        if key in seen:
            continue
        seen.add(key)
        lines.append(f"== {key}: {titles.get(key, '')}")
        lines.append(f"   {fmt_counts(before[key])} -> {fmt_counts(after[key])}")
        for env in by_chapter.get(key, []):
            target = roles.target(env)
            if target in ("theorem", "corollary"):
                note = roles.notes.get(env.label or "", "")
                lines.append(f"   [{target}] {env.label}: {env.caption}")
                if note:
                    lines.append(f"       reason: {note}")
        lines.append("")
    total_before = sum(before.values(), Counter())
    total_after = sum(after.values(), Counter())
    lines.append(f"TOTAL {fmt_counts(total_before)} -> {fmt_counts(total_after)}")
    lines.append(f"environment changes: {len(result.env_changes)}")
    lines.append(f"prose reference rewrites: {len(result.ref_changes)}")
    lines.append(f"mixed reference lists left unchanged: {len(result.mixed_refs)}")
    for item in result.mixed_refs:
        lines.append(f"   {item}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--dry-run", action="store_true")
    mode.add_argument("--apply", action="store_true")
    mode.add_argument("--verify", action="store_true")
    parser.add_argument("--roles", type=Path, default=DEFAULT_ROLES)
    parser.add_argument("--src", type=Path, default=DEFAULT_SRC)
    parser.add_argument("--entry", default=DEFAULT_ENTRY)
    parser.add_argument("--base", default="origin/main", help="git ref for --verify")
    parser.add_argument("--report", type=Path, help="also write the dry-run report here")
    args = parser.parse_args(argv)
    src = args.src.resolve()

    if args.verify:
        before = git_texts(src, args.base)
        after = {p: p.read_text(encoding="utf-8") for p in tex_files(src)}
        problems = verify_texts(before, after)
        for p in problems:
            print(p)
        print("verify: OK" if not problems else f"verify: {len(problems)} problem(s)")
        return 1 if problems else 0

    bp = Blueprint(src, args.entry)
    roles = load_roles(args.roles)
    problems = bp.errors() + validate_roles(bp, roles)
    for w in bp.warnings:
        print(f"warning: {w}", file=sys.stderr)
    result = transform(bp, roles)

    if args.check:
        for env, target in result.env_changes:
            rel = env.path.relative_to(src)
            print(f"{rel}:{env.line}: {env.name} {env.label or '(no label)'} should be {target}")
        for ch in result.ref_changes:
            rel = ch.path.relative_to(src)
            print(f"{rel}:{ch.line}: {' '.join(ch.old.split())!r} should read "
                  f"{' '.join(ch.new.split())!r}")
        for item in result.mixed_refs:
            print(f"{item} (name both environments)")
        for p in problems:
            print(p)
        bad = (len(result.env_changes) + len(result.ref_changes)
               + len(result.mixed_refs) + len(problems))
        print(f"check: {bad} mismatch(es)" if bad else "check: OK")
        return 1 if bad else 0

    report = dry_run_report(bp, roles, result)
    if args.report:
        args.report.write_text(report + "\n", encoding="utf-8")
    if args.dry_run:
        print(report)
        for p in problems:
            print(p)
        return 1 if problems else 0

    # --apply
    if problems:
        for p in problems:
            print(p)
        print("apply: refusing to write while the data file or sources have problems")
        return 1
    conservation = verify_texts(bp.texts, result.texts)
    if conservation:
        for p in conservation:
            print(p)
        print("apply: refusing to write; tag conservation failed")
        return 1
    written = 0
    for path, text in result.texts.items():
        if text != bp.texts[path]:
            path.write_text(text, encoding="utf-8")
            written += 1
    print(
        f"apply: {len(result.env_changes)} environment(s), "
        f"{len(result.ref_changes)} reference word(s), {written} file(s) written; "
        f"{len(result.mixed_refs)} mixed reference list(s) left unchanged"
    )
    for item in result.mixed_refs:
        print(f"   {item}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
