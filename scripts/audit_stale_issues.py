#!/usr/bin/env python3
r"""
Stale-issue audit for theorem / sorry tracking tickets.

Scans exported GitHub issue JSON (from ``gh issue list --json``) and flags
references whose state on current ``main`` looks outdated:

  * ``TNLean/**/*.lean`` paths that no longer exist;
  * cited ``file.lean:LINE`` or ``line NNN`` markers where the line is no
    longer a ``sorry`` / ``admit``;
  * backtick-quoted declaration names that no longer resolve to any
    ``def`` / ``theorem`` / ``lemma`` / ``structure`` / ``instance`` /
    ``class`` / ``abbrev`` / ``inductive`` declaration under ``TNLean/``.

The tool is **report-only**: it never edits or closes issues.  It is intended
as a triage aid for humans who will decide whether a flagged issue is truly
stale or simply needs its body updated.

Typical workflow::

    gh issue list --repo OWNER/REPO --state open --limit 500 \
      --json number,title,body,url,labels > issues.json
    python scripts/audit_stale_issues.py --issues issues.json

See ``docs/stale_issue_audit.md`` for the documented workflow.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


# ---------------------------------------------------------------------------
# Regexes
# ---------------------------------------------------------------------------

# Lean file path under the project. ``:LINE`` suffix captured when present.
# The outer ``(?:/…)*`` also matches the root ``TNLean.lean`` file.  A
# leading ``\b`` keeps the match from starting mid-identifier.
_FILE_RE = re.compile(r"\b(TNLean(?:/[A-Za-z0-9_.\-]+)*\.lean)(?::(\d+))?")

# GitHub blob URLs often appear in issue bodies; normalize them to plain
# ``TNLean/...`` citations before scanning so we don't greedily match the
# repo-name prefix (``.../TNLean/blob/main/...``) as part of the path.
_GITHUB_BLOB_RE = re.compile(
    r"https?://github\.com/[^/\s]+/[^/\s]+/blob/[^\s#]+?/"
    r"(TNLean(?:/[A-Za-z0-9_.\-]+)*\.lean)(?:#L(\d+)(?:-L\d+)?)?"
)

# "line 141" / "Line 131" — used when a path is mentioned nearby without the
# bare ``:LINE`` suffix (the common table-cell idiom in this repo's issues).
_LINE_WORD_RE = re.compile(r"\bline\s+(\d{1,6})\b", re.IGNORECASE)

# Backtick-quoted token that looks like a Lean identifier.  Deliberately
# conservative: must start with a letter, minimum two chars, only identifier
# punctuation allowed.  This filters out inline prose like `main` and `sorry`
# via the _DECL_STOPLIST below rather than by regex alone.
_BACKTICK_DECL_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_.']{1,})`")

# Declaration-definition pattern used to build the "known declarations" set.
# Matches the header line of a Lean declaration; mirrors the lighter-weight
# variant used by scripts/blueprint_lean_sync.py but only returns the short
# (unqualified) name.
_DECL_DEFN_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:noncomputable|protected|private|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|class|structure|inductive|opaque)\s+"
    r"([A-Za-z_][\w.']*)",
    re.MULTILINE,
)

_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.']*)\b")
_END_NAMESPACE_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.']*))?\s*(?:--.*)?$")

# Sorry markers we count as "still unproven".
_SORRY_LINE_RE = re.compile(r"\b(sorry|admit)\b")

# Tokens that are common English words, Lean keywords, or otherwise too
# ambiguous to treat as declaration citations.  Any backtick token in this
# set is skipped.
_DECL_STOPLIST = frozenset({
    "sorry", "admit", "main", "by", "true", "false", "Prop", "Type",
    "True", "False", "Nat", "Int", "Rat", "Real", "Complex",
    "rfl", "simp", "rw", "exact", "apply", "intro", "cases",
    "this", "self", "it", "foo", "bar", "baz", "qux",
    # Common command / tool names that show up in validation snippets.
    "lean", "lake", "gh", "git", "rg", "grep", "sed", "awk",
    "python", "python3", "bash", "sh", "ls", "cd",
})


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FileCitation:
    """A ``TNLean/...`` path (with optional line) cited in an issue body."""
    path: str
    line: int | None


@dataclass(frozen=True)
class DeclCitation:
    """A backtick-quoted identifier cited in an issue body."""
    name: str


@dataclass
class IssueReport:
    """Per-issue findings."""
    number: int
    title: str
    url: str
    missing_files: list[str] = field(default_factory=list)
    non_sorry_lines: list[tuple[str, int]] = field(default_factory=list)
    missing_decls: list[str] = field(default_factory=list)
    file_citations: int = 0
    decl_citations: int = 0

    @property
    def is_flagged(self) -> bool:
        return bool(self.missing_files or self.non_sorry_lines or self.missing_decls)


# ---------------------------------------------------------------------------
# Citation extraction
# ---------------------------------------------------------------------------

def _normalize_github_blob_urls(body: str) -> str:
    """Rewrite GitHub blob URLs to plain ``TNLean/...[:LINE]`` citations."""

    def repl(match: re.Match[str]) -> str:
        path = match.group(1)
        line = match.group(2)
        return f"{path}:{line}" if line is not None else path

    return _GITHUB_BLOB_RE.sub(repl, body)


def extract_file_citations(body: str) -> list[FileCitation]:
    """Pull ``TNLean/.../file.lean[:LINE]`` references out of ``body``.

    When the path appears in a table row that separately lists ``line NNN``
    (the common convention in sorry-site trackers), we attach the nearest
    ``line NNN`` on the same line as the path.
    """
    out: list[FileCitation] = []
    for raw_line in _normalize_github_blob_urls(body).splitlines():
        paths_on_line = list(_FILE_RE.finditer(raw_line))
        if not paths_on_line:
            continue
        line_hints = [int(m.group(1)) for m in _LINE_WORD_RE.finditer(raw_line)]
        for idx, m in enumerate(paths_on_line):
            path = m.group(1)
            if m.group(2) is not None:
                out.append(FileCitation(path=path, line=int(m.group(2))))
                continue
            # No ``:LINE`` suffix — fall back to a ``line NNN`` word on the
            # same line only when exactly one path appears (avoids cross
            # attribution in tables with multiple rows on one wrapped line).
            if len(paths_on_line) == 1 and len(line_hints) == 1:
                out.append(FileCitation(path=path, line=line_hints[0]))
            else:
                out.append(FileCitation(path=path, line=None))
    # Deduplicate while preserving order.
    seen: set[tuple[str, int | None]] = set()
    unique: list[FileCitation] = []
    for fc in out:
        key = (fc.path, fc.line)
        if key in seen:
            continue
        seen.add(key)
        unique.append(fc)
    return unique


def extract_decl_citations(body: str) -> list[DeclCitation]:
    """Pull backtick-quoted Lean-identifier-shaped tokens out of ``body``."""
    out: list[DeclCitation] = []
    seen: set[str] = set()
    for m in _BACKTICK_DECL_RE.finditer(body):
        name = m.group(1)
        if name in _DECL_STOPLIST or name in seen:
            continue
        # Require at least one lowercase or digit; purely uppercase backtick
        # items are dropped, which helps exclude obvious sentence starts like
        # `The`.  This is a soft filter.
        if not any(c.islower() or c.isdigit() for c in name):
            continue
        seen.add(name)
        out.append(DeclCitation(name=name))
    return out


# ---------------------------------------------------------------------------
# Main-branch indices
# ---------------------------------------------------------------------------

def build_decl_index(lean_root: Path) -> set[str]:
    """Collect declaration names under ``lean_root``.

    The index stores both short names (for unqualified issue citations) and the
    namespace-qualified names visible from simple ``namespace ...`` blocks.  A
    cited qualified name is later matched exactly, so ``Foo.bar`` cannot be
    silently satisfied by some unrelated short declaration named ``bar``.
    """
    names: set[str] = set()
    for path in sorted(lean_root.rglob("*.lean")):
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        namespace_stack: list[str] = []
        for line in text.splitlines():
            if m := _NAMESPACE_RE.match(line):
                namespace_stack.extend(m.group(1).split("."))
                continue
            if m := _END_NAMESPACE_RE.match(line):
                end_name = m.group(1)
                if end_name:
                    parts = end_name.split(".")
                    if namespace_stack[-len(parts):] == parts:
                        del namespace_stack[-len(parts):]
                    # Otherwise this is likely closing a named section, not a
                    # tracked namespace; leave the namespace stack unchanged.
                # An anonymous ``end`` is ambiguous: in this repo it commonly
                # closes an unnamed ``section`` inside a namespace.  Do not pop
                # the namespace stack unless Lean text explicitly names the
                # namespace being closed.
                continue
            if m := _DECL_DEFN_RE.match(line):
                declared = m.group(1)
                short = declared.rsplit(".", 1)[-1]
                names.add(short)
                names.add(declared)
                if namespace_stack:
                    names.add(".".join([*namespace_stack, declared]))
    return names


def line_is_sorry(path: Path, line_no: int) -> bool | None:
    """Return True/False if ``path:line_no`` still contains a ``sorry``/``admit``.

    Returns ``None`` if the file can't be read or the line number is out of
    range.  Single-line ``--`` comments are stripped before matching so that
    commented-out mentions (``-- sorry``) don't masquerade as active sorry
    sites.
    """
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return None
    lines = text.splitlines()
    if line_no < 1 or line_no > len(lines):
        return None
    line = lines[line_no - 1].split("--", 1)[0]
    return _SORRY_LINE_RE.search(line) is not None


# ---------------------------------------------------------------------------
# Audit driver
# ---------------------------------------------------------------------------

def _repo_file_path(repo_root: Path, citation_path: str) -> Path | None:
    """Resolve a cited file path, rejecting paths that escape ``repo_root``.

    Issue text is untrusted input.  The path regex intentionally recognizes
    broad ``TNLean/...``-shaped strings, so normalize away any ``..``
    segments before opening the file.  A citation that resolves outside the
    checkout is treated as an invalid/missing in-repository file instead of
    letting the audit inspect arbitrary host files.
    """
    root = repo_root.resolve()
    candidate = (root / citation_path).resolve(strict=False)
    try:
        candidate.relative_to(root)
    except ValueError:
        return None
    return candidate


def audit_issue(
    issue: dict,
    repo_root: Path,
    decl_index: set[str],
) -> IssueReport:
    """Run all checks against a single issue dict from ``gh issue list``."""
    number = int(issue.get("number", 0))
    title = str(issue.get("title", ""))
    url = str(issue.get("url", ""))
    body = str(issue.get("body") or "")

    report = IssueReport(number=number, title=title, url=url)

    file_cites = extract_file_citations(body)
    decl_cites = extract_decl_citations(body)
    report.file_citations = len(file_cites)
    report.decl_citations = len(decl_cites)

    for fc in file_cites:
        full = _repo_file_path(repo_root, fc.path)
        if full is None or not full.is_file():
            report.missing_files.append(
                fc.path if fc.line is None else f"{fc.path}:{fc.line}"
            )
            continue
        if fc.line is not None:
            sorry = line_is_sorry(full, fc.line)
            # Treat both an explicit "no sorry on this line" (False) and an
            # out-of-range line number (None) as stale: trackers drift as
            # files are edited, and a citation past EOF is exactly the kind
            # of stale reference this audit is meant to surface.
            if sorry is not True:
                report.non_sorry_lines.append((fc.path, fc.line))

    for dc in decl_cites:
        if "." in dc.name:
            # Qualified citations are meant to disambiguate.  Require an exact
            # qualified-name match instead of accepting any declaration with the
            # same final component.
            if dc.name not in decl_index:
                report.missing_decls.append(dc.name)
        else:
            short = dc.name.rsplit(".", 1)[-1]
            if dc.name not in decl_index and short not in decl_index:
                report.missing_decls.append(dc.name)

    return report


def load_issues(path: Path) -> list[dict]:
    """Load issues from a JSON file produced by ``gh issue list --json``."""
    data = json.loads(path.read_text())
    if not isinstance(data, list):
        raise ValueError(
            f"{path}: expected a JSON array (from `gh issue list --json ...`)"
        )
    return data


def run_audit(
    issues: Iterable[dict],
    repo_root: Path,
) -> list[IssueReport]:
    decl_index = build_decl_index(repo_root / "TNLean")
    reports: list[IssueReport] = []
    for issue in issues:
        reports.append(audit_issue(issue, repo_root, decl_index))
    return reports


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def render_text_report(reports: list[IssueReport], only_flagged: bool) -> str:
    total = len(reports)
    flagged = [r for r in reports if r.is_flagged]
    scanned = [r for r in reports if r.file_citations or r.decl_citations]
    lines = [
        "Stale-issue audit report",
        "========================",
        f"issues scanned        : {total}",
        f"issues with citations : {len(scanned)}",
        f"issues flagged stale  : {len(flagged)}",
        "triage note           : keep mathematical source citations precise",
        "                       (paper/blueprint path, line, label, and",
        "                       short quotation or precise paraphrase)",
        "",
    ]
    show = flagged if only_flagged else reports
    for r in show:
        header = f"#{r.number} — {r.title}"
        lines.append(header)
        lines.append("-" * len(header))
        if r.url:
            lines.append(f"  {r.url}")
        if not r.is_flagged:
            lines.append("  (no stale citations detected)")
            lines.append("")
            continue
        if r.missing_files:
            lines.append("  missing files:")
            for p in r.missing_files:
                lines.append(f"    - {p}")
        if r.non_sorry_lines:
            lines.append("  lines no longer containing `sorry`/`admit`:")
            for path, ln in r.non_sorry_lines:
                lines.append(f"    - {path}:{ln}")
        if r.missing_decls:
            lines.append("  declarations not found under TNLean/:")
            for name in r.missing_decls:
                lines.append(f"    - {name}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_json_report(reports: list[IssueReport]) -> str:
    payload = [
        {
            "number": r.number,
            "title": r.title,
            "url": r.url,
            "flagged": r.is_flagged,
            "missing_files": r.missing_files,
            "non_sorry_lines": [
                {"path": p, "line": ln} for p, ln in r.non_sorry_lines
            ],
            "missing_decls": r.missing_decls,
            "file_citations": r.file_citations,
            "decl_citations": r.decl_citations,
        }
        for r in reports
    ]
    return json.dumps(payload, indent=2) + "\n"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="audit_stale_issues",
        description=(
            "Flag open GitHub issues whose cited files, line numbers, or "
            "backtick-quoted declarations look stale on current main. "
            "Report-only: never edits or closes issues."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Example:\n"
            "  gh issue list --repo OWNER/REPO --state open --limit 500 \\\n"
            "    --json number,title,body,url > issues.json\n"
            "  python scripts/audit_stale_issues.py --issues issues.json\n"
        ),
    )
    parser.add_argument(
        "--issues",
        type=Path,
        help=(
            "Path to a JSON file produced by `gh issue list --json "
            "number,title,body,url`.  Required unless --self-test is used."
        ),
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: parent of this script's directory).",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Output format (default: text).",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Include non-flagged issues in text reports (default: flagged only).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write report to this file instead of stdout.",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help=(
            "Run a credentials-free smoke test against a synthetic issue "
            "and the current repository state.  Exits 0 on success."
        ),
    )
    return parser


def _self_test(repo_root: Path) -> int:
    """Minimal credentials-free smoke test.

    Builds one synthetic issue whose body references this very script and a
    deliberately bogus declaration, then confirms the audit emits the
    expected flags.  Used by CI and by human reviewers to verify the tool
    works on a fresh checkout without talking to GitHub.
    """
    synthetic = {
        "number": 0,
        "title": "[self-test] synthetic audit fixture",
        "url": "https://example.invalid/issue/0",
        "body": (
            "Refers to `TNLean/Does/Not/Exist.lean:10` and to "
            "`definitely_not_a_real_declaration`.\n"
            "Also mentions `scripts/audit_stale_issues.py` (should be ignored)."
        ),
    }
    reports = run_audit([synthetic], repo_root)
    r = reports[0]
    problems: list[str] = []
    if "TNLean/Does/Not/Exist.lean:10" not in r.missing_files:
        problems.append(
            f"expected missing-file flag, got: {r.missing_files!r}"
        )
    if "definitely_not_a_real_declaration" not in r.missing_decls:
        problems.append(
            f"expected missing-decl flag, got: {r.missing_decls!r}"
        )
    if problems:
        print("self-test FAILED:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    print("self-test OK: synthetic issue flagged as expected.")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    if not (repo_root / "TNLean").is_dir():
        parser.error(f"--repo-root {repo_root} has no TNLean/ subdirectory")

    if args.self_test:
        return _self_test(repo_root)

    if args.issues is None:
        parser.error("--issues is required (or pass --self-test)")

    issues = load_issues(args.issues)
    reports = run_audit(issues, repo_root)

    if args.format == "json":
        output = render_json_report(reports)
    else:
        output = render_text_report(reports, only_flagged=not args.all)

    if args.output is not None:
        args.output.write_text(output)
    else:
        sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
