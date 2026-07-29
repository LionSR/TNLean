#!/usr/bin/env python3
"""Build and audit the source-first tenkz RMP benchmark corpus.

The committed case files are preamble-free fragments.  This driver is the
only assembly layer: it makes disposable standalone wrappers for checking,
generates a disposable book index, and never copies a case body into another
committed source file.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from collections import Counter
from pathlib import Path
from typing import Any, Iterable, Sequence

from tenkzlib.texcase import strip_comments
from tenkzlib.tnlog import ParsedLog, parse_log


REPO = Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = REPO / "tests" / "tenkz" / "rmp" / "manifest.toml"
DEFAULT_VERDICT = REPO / "tests" / "tenkz" / "rmp" / "verdicts.toml"
PAPER_SOURCE = REPO / "Papers" / "2011.12127" / "TN-Review-main.tex"
FROZEN_TARGET_COUNT = 130
BOOK_SOURCE = REPO / "docs" / "tenkz" / "rmp-benchmark.tex"
BOOK_OUTPUT = REPO / "output" / "pdf" / "tenkz-rmp-benchmark.pdf"
COMPARE_OUTPUT = REPO / "output" / "pdf" / "tenkz-rmp-comparison.pdf"
RENDER_OUTPUT = REPO / "tmp" / "pdfs" / "tenkz-rmp"
SECTIONS = (
    "section-ii",
    "section-iii-a",
    "section-iii-b",
    "section-iv-v-app",
)
CORPORA = ("published", "author-workbench")
REQUIRED_HEADERS = (
    "Target",
    "Formula",
    "Ink",
    "Boundary",
    "Source",
    "Capabilities",
)
CORPUS_FIELDS = (
    "published_targets",
    "paper_placements",
    "author_workbench_targets",
    "total_targets",
    "author_source_mapped",
    "paper_context_only",
)
TARGET_REQUIRED = {
    "id",
    "corpus",
    "section",
    "order",
    "case",
    "formula",
    "ink",
    "boundary",
    "source",
    "capabilities",
    "paper_context_only",
    "placements",
}
TARGET_OPTIONAL = {
    "fixture",
    "author_source",
    "author_lines",
    "equivalent_to",
    "extraction_override",
}
FORBIDDEN_CASE_PATTERNS = (
    (re.compile(r"\\documentclass\b|\\usepackage\b|\\begin\{document\}"),
     "case must be a preamble-free fragment"),
    (re.compile(
        r"\\begin\{tikzpicture\}|\\(?:draw|fill|filldraw|shade|path|node|tikzset)\b"
    ),
     "case uses raw TikZ ink"),
    (re.compile(r"\\(?:__tenkz|tenkz@|tenkz_[A-Za-z])"),
     "case uses a private tenkz name"),
    (re.compile(r"\\tndefine\b"),
     "case uses a whole-figure definition"),
    (re.compile(r"\\coordinate\b|\\pgf(?:point|path|extra)\b"),
     "case uses an undocumented coordinate escape"),
)
INCLUDEGRAPHICS_RE = re.compile(
    r"\\includegraphics(?:\s*\[[^\]]*\])?\s*\{([^}]*)\}"
)


VERDICT_STATUSES = (
    "unreviewed",
    "faithful",
    "cosmetic-gap",
    "structural-gap",
    "unfaithful",
    "blocked",
)
PAIRING_STATES = (
    "unverified",
    "verified",
    "wrong-source",
    "source-misrender",
    "context-only",
)
DEFECT_KINDS = (
    "label-collision",
    "open-closure",
    "text-substitution",
    "unfaithful-substitution",
    "weight-mismatch",
    "boundary-mismatch",
    "wrong-contraction",
    "missing-element",
    "extra-element",
    "placement-illegible",
)
# Structural capability tags map one-to-one onto public constructs; a tag
# without its construct in the case body is manifest drift, not judgment.
STRUCTURAL_CAPABILITY_PATTERNS = {
    "kernel": re.compile(r"\\tenkzkernel\b"),
    "grid": re.compile(r"\\begin\{tenkz\}|\\tnpic\b"),
    "lattice": re.compile(r"\\begin\{tenkzlattice\}|\\begin\{tenkzplanes\}"),
    "lattice-preset": re.compile(r"\\begin\{tenkzplanes\}"),
    "free-graph": re.compile(r"\\begin\{tenkzfree\}"),
    "fusion-tree": re.compile(r"\\tntree\b|\\begin\{tenkzcd\}"),
}
INK_ENVIRONMENT_PATTERNS = {
    "tenkzfree": re.compile(r"\\begin\{tenkzfree\}"),
    "tenkzlattice": re.compile(r"\\begin\{tenkzlattice\}"),
    "tenkzplanes": re.compile(r"\\begin\{tenkzplanes\}"),
    "tenkz": re.compile(r"\\begin\{tenkz(?:eq|cd)?\}|\\tnpic\b|\\tntree\b"),
}
INK_SCOPE_TOKEN = re.compile(
    r"(?P<skip>\\\\(?:\s*\[[^\]]*\])?|\\[{}])"
    r"|\\tenkzkernel\b"
    r"|\\begin\s*\{(?P<begin>[^{}]+)\}"
    r"|\\end\s*\{(?P<end>[^{}]+)\}"
    r"|\\begingroup\b|\\endgroup\b"
    r"|\\\[|\\\]|\\\(|\\\)"
    r"|\\tnpic\b|\\tntree\b"
    r"|[{}]"
)


def used_ink_environment_families(body: str) -> set[str]:
    """Return public picture families, respecting the scoped kernel switch."""
    families: set[str] = set()
    kernel_scope = [False]
    for token in INK_SCOPE_TOKEN.finditer(body):
        text = token.group()
        begin = token.group("begin")
        if token.group("skip") is not None:
            continue
        if text == r"\tenkzkernel":
            kernel_scope[-1] = True
        elif begin is not None:
            if begin in {"tenkz", "tenkzeq"}:
                families.add("kernel" if kernel_scope[-1] else "tenkz")
            elif begin == "tenkzcd":
                families.add("tenkz")
            elif begin in {"tenkzfree", "tenkzlattice", "tenkzplanes"}:
                families.add(begin)
            kernel_scope.append(kernel_scope[-1])
        elif token.group("end") is not None:
            if len(kernel_scope) > 1:
                kernel_scope.pop()
        elif text in {r"\begingroup", r"\[", r"\(", "{"}:
            kernel_scope.append(kernel_scope[-1])
        elif text in {r"\endgroup", r"\]", r"\)", "}"}:
            if len(kernel_scope) > 1:
                kernel_scope.pop()
        elif text in {r"\tnpic", r"\tntree"}:
            families.add("tenkz")
    return families


def ink_environment_problems(target_id: str, ink: str, body: str) -> list[str]:
    """Return contradictions between an Ink family claim and the case body."""
    problems: list[str] = []
    claimed = {
        family
        for family in (*INK_ENVIRONMENT_PATTERNS, "kernel")
        if re.search(rf"\b{family}\b", ink, flags=re.IGNORECASE)
    }
    used = used_ink_environment_families(body)
    for family in (*INK_ENVIRONMENT_PATTERNS, "kernel"):
        if family in claimed and family not in used:
            problems.append(
                f"{target_id}: Ink names {family} but the case body does not "
                "contain a picture owned by that family"
            )
        if family in used and family not in claimed:
            problems.append(
                f"{target_id}: case body uses {family} but Ink does not name "
                "that family"
            )
    return problems


def structural_capability_problems(
    target_id: str, capabilities: Sequence[str], body: str
) -> list[str]:
    """Return construct-witness and model-owner contradictions."""
    problems: list[str] = []
    kernel_body = bool(STRUCTURAL_CAPABILITY_PATTERNS["kernel"].search(body))
    if kernel_body and "kernel" not in capabilities:
        problems.append(
            f"{target_id}: \\tenkzkernel owns the picture model but capability "
            "'kernel' is missing"
        )
    if kernel_body and "grid" in capabilities:
        problems.append(
            f"{target_id}: capability tag 'grid' names the nested renderer of a "
            "\\tenkzkernel picture; use the exclusive owner tag 'kernel'"
        )
    for capability in capabilities:
        pattern = STRUCTURAL_CAPABILITY_PATTERNS.get(capability)
        if pattern is not None and not pattern.search(body):
            problems.append(
                f"{target_id}: capability tag {capability!r} has no matching "
                "construct in the case body (manifest drift)"
            )
    return problems


# Statuses that already concede the figure is not a faithful reproduction;
# automatic defect detection demands consistency from the rest.
CONCEDING_STATUSES = {"structural-gap", "unfaithful", "blocked"}


class RMPError(RuntimeError):
    """A benchmark contract or build step failed."""


@dataclasses.dataclass(frozen=True)
class Target:
    id: str
    corpus: str
    section: str
    order: int
    case: Path
    formula: str
    ink: str
    boundary: str
    source: str
    capabilities: tuple[str, ...]
    paper_context_only: bool
    placements: tuple[dict[str, Any], ...]
    fixture: Path | None
    author_source: Path | None
    author_lines: str | None
    equivalent_to: str | None
    extraction_override: str | None


@dataclasses.dataclass(frozen=True)
class BuildResult:
    target: Target
    wrapper: Path
    pdf: Path
    tnlog: Path
    width: str
    height: str
    pages: int
    audit_signatures: tuple[str, ...]


@dataclasses.dataclass(frozen=True)
class TargetVerdict:
    id: str
    status: str
    pairing: str
    defects: tuple[str, ...]
    missing: tuple[str, ...]
    case_sha256: str | None
    note: str
    reviewed: str
    renderer: str
    second_viewer: str
    pairing_by: str


def fail(message: str) -> None:
    raise RMPError(message)


def require_tool(name: str) -> str:
    executable = shutil.which(name)
    if executable is None:
        fail(f"tenkz RMP benchmark requires {name}")
    return executable


def run(
    command: Sequence[str],
    *,
    cwd: Path,
    timeout: int,
    env: dict[str, str] | None = None,
    label: str,
) -> subprocess.CompletedProcess[str]:
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        fail(f"{label} timed out after {timeout}s")
    if result.returncode:
        tail = "\n".join(result.stdout.splitlines()[-120:])
        fail(f"{label} failed (exit {result.returncode})\n{tail}")
    return result


def relative_repo_path(value: Any, *, field: str, suffix: str | None = None) -> Path:
    if not isinstance(value, str) or not value.strip():
        fail(f"{field} must be a nonempty repo-relative path")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        fail(f"{field} must stay within the repository: {value!r}")
    if suffix is not None and path.suffix != suffix:
        fail(f"{field} must name a {suffix} file: {value!r}")
    return path


def nonempty_string(value: Any, *, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        fail(f"{field} must be a nonempty string")
    return value.strip()


def parse_author_lines(value: Any, *, field: str) -> str:
    text = nonempty_string(value, field=field)
    if re.fullmatch(r"[1-9][0-9]*(?:-[1-9][0-9]*)?", text) is None:
        fail(f"{field} must be N or N-M, got {text!r}")
    start, _, end = text.partition("-")
    if end and int(end) < int(start):
        fail(f"{field} has a descending range: {text!r}")
    return text


def load_manifest(path: Path) -> list[Target]:
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"manifest does not exist: {path}")
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        fail(f"cannot read manifest {path}: {exc}")

    if data.get("schema_version") != 1:
        fail("manifest schema_version must be exactly 1")
    corpus = data.get("corpus")
    if not isinstance(corpus, dict):
        fail("manifest needs a [corpus] table")
    if set(corpus) != set(CORPUS_FIELDS):
        fail("[corpus] fields must be exactly: " + ", ".join(CORPUS_FIELDS))
    for field in CORPUS_FIELDS:
        if (
            not isinstance(corpus[field], int)
            or isinstance(corpus[field], bool)
            or corpus[field] < 0
        ):
            fail(f"corpus.{field} must be a nonnegative integer")

    raw_targets = data.get("target")
    if not isinstance(raw_targets, list):
        fail("manifest needs repeated [[target]] tables")
    targets: list[Target] = []
    for index, raw in enumerate(raw_targets, 1):
        where = f"target[{index}]"
        if not isinstance(raw, dict):
            fail(f"{where} must be a table")
        missing = TARGET_REQUIRED - set(raw)
        unknown = set(raw) - TARGET_REQUIRED - TARGET_OPTIONAL
        if missing:
            fail(f"{where} is missing fields: {', '.join(sorted(missing))}")
        if unknown:
            fail(f"{where} has unknown fields: {', '.join(sorted(unknown))}")
        target_id = nonempty_string(raw["id"], field=f"{where}.id")
        if re.fullmatch(r"rmp-[a-z0-9]+(?:-[a-z0-9]+)*", target_id) is None:
            fail(f"{where}.id is not a stable rmp-* slug: {target_id!r}")
        target_corpus = nonempty_string(raw["corpus"], field=f"{where}.corpus")
        if target_corpus not in CORPORA:
            fail(f"{where}.corpus must be published or author-workbench")
        section = nonempty_string(raw["section"], field=f"{where}.section")
        if section not in SECTIONS:
            fail(f"{where}.section is unknown: {section!r}")
        order = raw["order"]
        if not isinstance(order, int) or isinstance(order, bool) or order < 1:
            fail(f"{where}.order must be a positive integer")
        case = relative_repo_path(raw["case"], field=f"{where}.case", suffix=".tex")
        expected_parent = Path("tests") / "tenkz" / "rmp" / section / "cases"
        if case.parent != expected_parent:
            fail(f"{where}.case must live under {expected_parent.as_posix()}/")
        capabilities = raw["capabilities"]
        if (
            not isinstance(capabilities, list)
            or not capabilities
            or any(not isinstance(item, str) or not item.strip() for item in capabilities)
        ):
            fail(f"{where}.capabilities must be a nonempty string array")
        normalized_capabilities = tuple(item.strip() for item in capabilities)
        if len(set(normalized_capabilities)) != len(normalized_capabilities):
            fail(f"{where}.capabilities contains a duplicate")
        context_only = raw["paper_context_only"]
        if not isinstance(context_only, bool):
            fail(f"{where}.paper_context_only must be boolean")
        placements = raw["placements"]
        if not isinstance(placements, list):
            fail(f"{where}.placements must be an array")
        normalized_placements: list[dict[str, Any]] = []
        for placement_index, placement in enumerate(placements, 1):
            pwhere = f"{where}.placements[{placement_index}]"
            if not isinstance(placement, dict) or set(placement) != {"order", "line", "asset"}:
                fail(f"{pwhere} fields must be exactly order, line, asset")
            if any(
                not isinstance(placement[key], int)
                or isinstance(placement[key], bool)
                or placement[key] < 1
                for key in ("order", "line")
            ):
                fail(f"{pwhere}.order and .line must be positive integers")
            nonempty_string(placement["asset"], field=f"{pwhere}.asset")
            normalized_placements.append(dict(placement))
        if target_corpus == "published" and not normalized_placements:
            fail(f"{where} is published but has no paper placement")
        if target_corpus == "author-workbench" and normalized_placements:
            fail(f"{where} is author-workbench and must not have paper placements")

        author_source = None
        author_lines = None
        if "author_source" in raw or "author_lines" in raw:
            if "author_source" not in raw or "author_lines" not in raw:
                fail(f"{where} must provide author_source and author_lines together")
            author_source = relative_repo_path(
                raw["author_source"], field=f"{where}.author_source", suffix=".tex"
            )
            author_lines = parse_author_lines(raw["author_lines"], field=f"{where}.author_lines")
        if context_only and (author_source is not None or author_lines is not None):
            fail(f"{where} is paper-context-only and cannot claim author source")
        if target_corpus == "published" and not context_only and author_source is None:
            fail(f"{where} needs an author-source mapping or paper_context_only=true")
        if target_corpus == "author-workbench" and author_source is None:
            fail(f"{where} needs its author-workbench source mapping")

        fixture = None
        if "fixture" in raw:
            fixture = relative_repo_path(raw["fixture"], field=f"{where}.fixture", suffix=".tex")
            if fixture.parent != Path("tests") / "tenkz":
                fail(f"{where}.fixture must name an existing tests/tenkz/*.tex fixture")
        equivalent_to = None
        if "equivalent_to" in raw:
            equivalent_to = nonempty_string(
                raw["equivalent_to"], field=f"{where}.equivalent_to"
            )
            if equivalent_to == target_id:
                fail(f"{where}.equivalent_to cannot name the target itself")
        extraction_override = None
        if "extraction_override" in raw:
            extraction_override = nonempty_string(
                raw["extraction_override"], field=f"{where}.extraction_override"
            )
            if author_lines is None:
                fail(f"{where}.extraction_override requires author_lines")
        targets.append(
            Target(
                id=target_id,
                corpus=target_corpus,
                section=section,
                order=order,
                case=case,
                formula=nonempty_string(raw["formula"], field=f"{where}.formula"),
                ink=nonempty_string(raw["ink"], field=f"{where}.ink"),
                boundary=nonempty_string(raw["boundary"], field=f"{where}.boundary"),
                source=nonempty_string(raw["source"], field=f"{where}.source"),
                capabilities=normalized_capabilities,
                paper_context_only=context_only,
                placements=tuple(normalized_placements),
                fixture=fixture,
                author_source=author_source,
                author_lines=author_lines,
                equivalent_to=equivalent_to,
                extraction_override=extraction_override,
            )
        )
    validate_census(targets, corpus)
    validate_source_placements(targets)
    for target in targets:
        validate_case(target)
    validate_distinct_case_bodies(targets)
    validate_author_ranges(targets)
    return targets


def duplicates(values: Iterable[Any]) -> list[Any]:
    counts = Counter(values)
    return sorted(value for value, count in counts.items() if count > 1)


def validate_census(targets: list[Target], census: dict[str, Any]) -> None:
    # M4 is explicitly defined over a frozen benchmark denominator.  The
    # manifest derives the detailed census, but it cannot redefine that gate.
    if len(targets) != FROZEN_TARGET_COUNT:
        fail(
            f"manifest has {len(targets)} targets; "
            f"the benchmark denominator is frozen at {FROZEN_TARGET_COUNT}"
        )
    if len(targets) != census["total_targets"]:
        fail(
            f"manifest has {len(targets)} targets; "
            f"[corpus] declares {census['total_targets']}"
        )
    repeated_ids = duplicates(target.id for target in targets)
    repeated_cases = duplicates(target.case for target in targets)
    if repeated_ids:
        fail("manifest repeats target ids: " + ", ".join(repeated_ids))
    if repeated_cases:
        repeated = ", ".join(path.as_posix() for path in repeated_cases)
        fail("manifest repeats case files: " + repeated)
    for corpus_name, expected_count in (
        ("published", census["published_targets"]),
        ("author-workbench", census["author_workbench_targets"]),
    ):
        members = [target for target in targets if target.corpus == corpus_name]
        if len(members) != expected_count:
            fail(
                f"manifest has {len(members)} {corpus_name} targets; "
                f"[corpus] declares {expected_count}"
            )
        orders = sorted(target.order for target in members)
        if orders != list(range(1, expected_count + 1)):
            fail(f"{corpus_name} order must be exactly 1..{expected_count}")
    placement_count = sum(len(target.placements) for target in targets)
    if placement_count != census["paper_placements"]:
        fail(
            f"manifest has {placement_count} paper placements; "
            f"[corpus] declares {census['paper_placements']}"
        )
    placement_orders = sorted(
        placement["order"] for target in targets for placement in target.placements
    )
    if placement_orders != list(range(1, census["paper_placements"] + 1)):
        fail(
            "paper placement order must be exactly "
            f"1..{census['paper_placements']}"
        )
    published = [target for target in targets if target.corpus == "published"]
    mapped = sum(target.author_source is not None for target in published)
    context_only = sum(target.paper_context_only for target in published)
    if mapped != census["author_source_mapped"]:
        fail(
            f"manifest has {mapped} mapped published targets; "
            f"[corpus] declares {census['author_source_mapped']}"
        )
    if context_only != census["paper_context_only"]:
        fail(
            f"manifest has {context_only} paper-context-only targets; "
            f"[corpus] declares {census['paper_context_only']}"
        )


def validate_source_placements(targets: Sequence[Target]) -> None:
    """Keep the manifest's placement census anchored to the source paper."""
    try:
        source = strip_comments(PAPER_SOURCE.read_text(encoding="utf-8"))
    except (OSError, UnicodeError) as exc:
        fail(f"cannot read source paper {PAPER_SOURCE}: {exc}")
    expected = [
        (source.count("\n", 0, match.start()) + 1, match.group(1))
        for match in INCLUDEGRAPHICS_RE.finditer(source)
    ]
    ordered = sorted(
        (placement["order"], placement["line"], placement["asset"])
        for target in targets
        for placement in target.placements
    )
    actual = [(line, asset) for _, line, asset in ordered]
    if actual != expected:
        fail(
            "paper placements must match the source paper's "
            f"{len(expected)} includegraphics occurrences"
        )
    expected_published = len({asset for _, asset in expected})
    published = sum(target.corpus == "published" for target in targets)
    if published != expected_published:
        fail(
            f"manifest has {published} published targets; the source paper has "
            f"{expected_published} distinct graphics"
        )
    expected_workbench = FROZEN_TARGET_COUNT - expected_published
    workbench = sum(target.corpus == "author-workbench" for target in targets)
    if workbench != expected_workbench:
        fail(
            f"manifest has {workbench} author-workbench targets; "
            f"the frozen remainder is {expected_workbench}"
        )


def case_headers(lines: list[str], *, path: Path) -> dict[str, str]:
    headers: dict[str, str] = {}
    pattern = re.compile(r"^% (Target|Formula|Ink|Boundary|Source|Capabilities):\s*(.*\S)\s*$")
    continuation = re.compile(r"^%   (.*\S)\s*$")
    active: str | None = None
    for line in lines:
        match = pattern.match(line)
        if match:
            key, value = match.groups()
            if key in headers:
                fail(f"{path}: duplicate % {key}: header")
            headers[key] = value
            active = key
            continue
        continued = continuation.match(line)
        if continued is not None and active is not None:
            headers[active] += " " + continued.group(1)
            continue
        active = None
    missing = [header for header in REQUIRED_HEADERS if header not in headers]
    if missing:
        fail(f"{path}: missing headers: " + ", ".join(f"% {name}:" for name in missing))
    return headers


def normalized_case_body(target: Target) -> str:
    """Return semantic case source with provenance comments and layout removed."""
    text = (REPO / target.case).read_text(encoding="utf-8")
    return re.sub(r"\s+", "", strip_comments(text))


def validate_distinct_case_bodies(targets: list[Target]) -> None:
    """Different benchmark targets must not be placeholder copies.

    Repeated paper placements belong to one target.  Consequently, two target
    IDs with the same normalized public source are always a corpus modelling
    error, even when their provenance comments differ.
    """
    groups: dict[str, list[Target]] = {}
    for target in targets:
        groups.setdefault(normalized_case_body(target), []).append(target)
    repeated: list[list[str]] = []
    used_equivalences: set[str] = set()
    for body, members in groups.items():
        if not body or len(members) < 2:
            continue
        ids = {target.id for target in members}
        roots = [target for target in members if target.equivalent_to is None]
        valid = len(roots) == 1 and all(
            target.equivalent_to in ids
            for target in members
            if target.equivalent_to is not None
        )
        if not valid:
            repeated.append([target.id for target in members])
        used_equivalences.update(
            target.id for target in members if target.equivalent_to is not None
        )
    dangling = [
        target.id
        for target in targets
        if target.equivalent_to is not None and target.id not in used_equivalences
    ]
    if dangling:
        fail("equivalent_to declared for non-equivalent case bodies: " + ", ".join(dangling))
    if repeated:
        details = "; ".join(", ".join(ids) for ids in repeated)
        fail("distinct targets have duplicate normalized case bodies: " + details)


def validate_case(target: Target) -> None:
    path = REPO / target.case
    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"case does not exist: {target.case.as_posix()}")
    except (OSError, UnicodeError) as exc:
        fail(f"cannot read {target.case.as_posix()}: {exc}")
    lines = text.splitlines()
    if not lines:
        fail(f"{target.case.as_posix()}: empty case")
    headers = case_headers(lines, path=target.case)
    expected_headers = {
        "Target": target.id,
        "Formula": target.formula,
        "Ink": target.ink,
        "Boundary": target.boundary,
        "Source": target.source,
        "Capabilities": ", ".join(target.capabilities),
    }
    for key, expected in expected_headers.items():
        actual_normalized = " ".join(headers[key].split())
        expected_normalized = " ".join(expected.split())
        if actual_normalized != expected_normalized:
            fail(
                f"{target.case.as_posix()}: % {key}: disagrees with manifest "
                f"({headers[key]!r} != {expected!r})"
            )
    if len(lines) > 100:
        fail(f"{target.case.as_posix()}: {len(lines)} lines exceeds the 100-line review limit")
    wide = [(number, len(line)) for number, line in enumerate(lines, 1) if len(line) > 88]
    if wide:
        details = ", ".join(f"{number} ({width})" for number, width in wide[:8])
        fail(f"{target.case.as_posix()}: lines exceed 88 characters: {details}")
    syntax = strip_comments(text)
    ink_problems = ink_environment_problems(target.id, target.ink, syntax)
    if ink_problems:
        fail(
            f"{target.case.as_posix()}: Ink environment mismatch:\n"
            + "\n".join(ink_problems)
        )
    for pattern, reason in FORBIDDEN_CASE_PATTERNS:
        match = pattern.search(syntax)
        if match:
            line = syntax.count("\n", 0, match.start()) + 1
            fail(f"{target.case.as_posix()}:{line}: {reason}: {match.group(0)}")
    if re.search(
        r"\\begin\{tenkz(?:cd|lattice|free|planes)?\}|\\tnpic\b|\\tntree\b", syntax
    ) is None:
        fail(f"{target.case.as_posix()}: case must contain a public tenkz picture")
    bracket_display = "\\[" in syntax and "\\]" in syntax
    environment_display = re.search(
        r"\\begin\{(?:align|alignat|equation|gather|multline)\*?\}", syntax
    ) is not None
    if not bracket_display and not environment_display:
        fail(f"{target.case.as_posix()}: case must contain a directly readable display")
    if target.fixture is not None and not (REPO / target.fixture).is_file():
        fail(f"fixture does not exist: {target.fixture.as_posix()}")


def select_targets(targets: list[Target], args: argparse.Namespace) -> list[Target]:
    target_id = getattr(args, "target_id", None)
    section = getattr(args, "section", None)
    if target_id is not None:
        selected = [target for target in targets if target.id == target_id]
        if not selected:
            fail(f"unknown target id: {target_id}")
        return selected
    if section is not None:
        return [target for target in targets if target.section == section]
    return list(targets)


def tex_environment(work: Path) -> dict[str, str]:
    env = os.environ.copy()
    paths = (
        f"{work.resolve()}//",
        f"{REPO / 'tex' / 'tenkz'}//",
        f"{REPO / 'docs' / 'tenkz'}//",
        f"{REPO}//",
        env.get("TEXINPUTS", ""),
    )
    env["TEXINPUTS"] = ":".join(paths)
    return env


def standalone_wrapper(target: Target) -> str:
    return "\n".join(
        (
            r"\documentclass[border=8pt,varwidth=270mm]{standalone}",
            r"\usepackage{amsmath,amssymb,mathtools}",
            r"\usepackage{tenkz}",
            r"\begin{document}",
            rf"\input{{{target.case.as_posix()}}}",
            r"\end{document}",
            "",
        )
    )


def pdf_dimensions(pdf: Path) -> tuple[str, str, int]:
    pdfinfo = require_tool("pdfinfo")
    result = run([pdfinfo, str(pdf)], cwd=pdf.parent, timeout=30, label=f"pdfinfo {pdf.name}")
    size_match = re.search(r"^Page size:\s+([0-9.]+) x ([0-9.]+) pts", result.stdout, re.MULTILINE)
    pages_match = re.search(r"^Pages:\s+([1-9][0-9]*)\s*$", result.stdout, re.MULTILINE)
    if size_match is None or pages_match is None:
        fail(f"pdfinfo did not report dimensions and page count for {pdf}")
    return size_match.group(1), size_match.group(2), int(pages_match.group(1))


def event_signatures(parsed: ParsedLog) -> tuple[str, ...]:
    """Return concise signatures from a parsed render event stream."""
    boundaries = tuple(
        event.raw for event in parsed.events if event.kind == "boundary"
    )
    if boundaries:
        return boundaries

    languages: dict[str, str] = {}
    counts: dict[str, Counter[str]] = {}
    boundary_atoms: Counter[str] = Counter()
    for event in parsed.events:
        if event.kind == "picture":
            picture = event.attrs.get("id", "?")
            languages[picture] = event.attrs.get("lang", "unknown")
            counts.setdefault(picture, Counter())
            continue
        picture = event.attrs.get("picture")
        if picture is None:
            continue
        counts.setdefault(picture, Counter())[event.kind] += 1
        if event.kind == "atom" and event.attrs.get("kind") == "boundary":
            boundary_atoms[picture] += 1

    signatures: list[str] = []
    for picture, event_counts in counts.items():
        topology = "".join(
            f"|{event}={event_counts[event]}" for event in sorted(event_counts)
            if event not in {"bbox", "glyph-geometry", "ink-use", "label-use"}
        ) or "|topology=none"
        signatures.append(
            "model-events"
            f"|picture={picture}"
            f"|lang={languages.get(picture, 'unknown')}"
            f"|boundary-atoms={boundary_atoms[picture]}"
            f"{topology}"
        )
    return tuple(signatures) or ("model-events|none",)


def compile_one(target: Target, root: Path, env: dict[str, str]) -> BuildResult:
    target_work = root / "targets" / target.id
    target_work.mkdir(parents=True)
    # The wrapper basename must not equal the case basename: TEXINPUTS contains
    # the repository recursively, and kpathsea could otherwise select the
    # preamble-free case instead of the disposable document in this directory.
    wrapper = target_work / f"{target.id}-standalone.tex"
    wrapper.write_text(standalone_wrapper(target), encoding="utf-8")
    transcript = target_work / f"{target.id}.xelatex.txt"
    try:
        result = run(
            [
                require_tool("timeout"),
                "120",
                require_tool("xelatex"),
                "-interaction=nonstopmode",
                "-halt-on-error",
                wrapper.name,
            ],
            cwd=target_work,
            timeout=125,
            env=env,
            label=f"XeLaTeX {target.id}",
        )
        transcript.write_text(result.stdout, encoding="utf-8")
        pdf = wrapper.with_suffix(".pdf")
        tnlog = wrapper.with_suffix(".tnlog")
        if not pdf.is_file() or pdf.stat().st_size == 0:
            fail(f"{target.id} produced no PDF")
        if not tnlog.is_file() or not tnlog.read_text(encoding="utf-8").strip():
            fail(f"{target.id} produced no nonempty .tnlog")
        audit = run(
            [
                sys.executable,
                str(REPO / "scripts" / "tenkz_audit.py"),
                str(tnlog),
                str(REPO / target.case),
            ],
            cwd=target_work,
            timeout=120,
            label=f"event audit {target.id}",
        )
        (target_work / f"{target.id}.audit.txt").write_text(audit.stdout, encoding="utf-8")
        width, height, pages = pdf_dimensions(pdf)
        parsed = parse_log(tnlog.read_text(encoding="utf-8"), source_name=tnlog.name)
        signatures = event_signatures(parsed)
        return BuildResult(target, wrapper, pdf, tnlog, width, height, pages, signatures)
    except RMPError as exc:
        if not transcript.exists():
            transcript.write_text(str(exc) + "\n", encoding="utf-8")
        raise


def lint_selected(targets: list[Target], work: Path) -> None:
    paths = [str(REPO / target.case) for target in targets]
    result = run(
        [sys.executable, str(REPO / "scripts" / "tenkz_lint.py"), *paths],
        cwd=work,
        timeout=max(120, len(targets) * 3),
        label="tenkz source lint",
    )
    (work / "lint.txt").write_text(result.stdout, encoding="utf-8")


def compile_targets(targets: list[Target], work: Path, jobs: int) -> list[BuildResult]:
    require_tool("xelatex")
    lint_selected(targets, work)
    env = tex_environment(work)
    results: list[BuildResult] = []
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {executor.submit(compile_one, target, work, env): target for target in targets}
        for future in concurrent.futures.as_completed(futures):
            target = futures[future]
            try:
                results.append(future.result())
                print(f"[tenkz rmp] PASS {target.id}")
            except Exception as exc:  # retain every parallel failure
                errors.append(f"{target.id}: {exc}")
    if errors:
        fail("target checks failed:\n" + "\n".join(errors))
    by_id = {result.target.id: result for result in results}
    return [by_id[target.id] for target in targets]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def campaign_digest(targets: Sequence[Target]) -> str:
    """Hash every committed input whose change invalidates visual verdicts."""
    paths = {
        DEFAULT_MANIFEST,
        PAPER_SOURCE,
        BOOK_SOURCE,
        REPO / "docs" / "tenkz" / "tenkzrmpbenchmark.sty",
        REPO / "scripts" / "tenkz_rmp.py",
        REPO / "scripts" / "tenkz_lint.py",
        REPO / "scripts" / "tenkz_audit.py",
        REPO / "scripts" / "tenkzlib" / "texcase.py",
        REPO / "scripts" / "tenkzlib" / "tnlog.py",
    }
    paths.update((REPO / "tex" / "tenkz").glob("*.tex"))
    paths.update((REPO / "tex" / "tenkz").glob("*.sty"))
    for target in targets:
        paths.add(REPO / target.case)
        if target.fixture is not None:
            paths.add(REPO / target.fixture)
    digest = hashlib.sha256()
    for path in sorted(paths, key=lambda item: item.relative_to(REPO).as_posix()):
        relative = path.relative_to(REPO).as_posix()
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(sha256(path).encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


VERDICT_STANZA_KEYS = {
    "id",
    "status",
    "pairing",
    "pairing_by",
    "defects",
    "missing",
    "case_sha256",
    "note",
    "reviewed",
    "renderer",
    "second_viewer",
}


def string_tuple(value: Any, *, where: str, allowed: tuple[str, ...] | None) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        fail(f"{where} must be a list of strings")
    if allowed is not None:
        unknown = sorted(set(value) - set(allowed))
        if unknown:
            fail(f"{where} uses unknown entries {unknown}; allowed: {sorted(allowed)}")
    return tuple(value)


def load_verdicts(targets: Sequence[Target]) -> dict[str, TargetVerdict]:
    """Load and validate the per-target verdict ledger.

    Every target carries exactly one stanza.  Any status may be recorded --
    including failure; the gate rejects lies (stale hashes, uncountersigned
    faithful claims, blocked entries that name no missing capability), never
    the existence of gaps.
    """
    if not DEFAULT_VERDICT.is_file():
        fail(
            f"per-target verdict ledger missing: {DEFAULT_VERDICT}; "
            "every target needs a [[verdict]] stanza (status=unreviewed is legal)"
        )
    try:
        raw = tomllib.loads(DEFAULT_VERDICT.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        fail(f"cannot read verdict ledger {DEFAULT_VERDICT}: {exc}")
    allowed_top = {"schema_version", "campaign_sha256", "verdict"}
    if not set(raw) <= allowed_top:
        fail(f"verdict ledger top-level keys must be within {sorted(allowed_top)}")
    if raw.get("schema_version") != 1:
        fail("verdict ledger schema_version must be 1")
    stanzas = raw.get("verdict")
    if not isinstance(stanzas, list) or not stanzas:
        fail("verdict ledger must contain [[verdict]] stanzas")
    by_target = {target.id: target for target in targets}
    verdicts: dict[str, TargetVerdict] = {}
    for index, stanza in enumerate(stanzas):
        where = f"verdict[{index}]"
        if not isinstance(stanza, dict):
            fail(f"{where} must be a table")
        unknown = sorted(set(stanza) - VERDICT_STANZA_KEYS)
        if unknown:
            fail(f"{where} has unknown keys {unknown}")
        for key in ("id", "status", "pairing"):
            if not isinstance(stanza.get(key), str) or not stanza.get(key):
                fail(f"{where}.{key} must be a nonempty string")
        identifier = stanza["id"]
        if identifier not in by_target:
            fail(f"{where}.id {identifier!r} is not a manifest target")
        if identifier in verdicts:
            fail(f"duplicate verdict stanza for {identifier}")
        status = stanza["status"]
        pairing = stanza["pairing"]
        if status not in VERDICT_STATUSES:
            fail(f"{where}.status {status!r} not in {VERDICT_STATUSES}")
        if pairing not in PAIRING_STATES:
            fail(f"{where}.pairing {pairing!r} not in {PAIRING_STATES}")
        defects = string_tuple(stanza.get("defects", []), where=f"{where}.defects", allowed=DEFECT_KINDS)
        missing = string_tuple(stanza.get("missing", []), where=f"{where}.missing", allowed=None)
        for key in ("note", "reviewed", "renderer", "second_viewer", "pairing_by"):
            if key in stanza and not isinstance(stanza[key], str):
                fail(f"{where}.{key} must be a string")
        if pairing == "verified" and not stanza.get("pairing_by"):
            fail(f"{where}: pairing=verified requires pairing_by naming the viewers")
        case_sha = stanza.get("case_sha256")
        if case_sha is not None and not isinstance(case_sha, str):
            fail(f"{where}.case_sha256 must be a string")
        verdict = TargetVerdict(
            id=identifier,
            status=status,
            pairing=pairing,
            defects=defects,
            missing=missing,
            case_sha256=case_sha,
            note=stanza.get("note", ""),
            reviewed=stanza.get("reviewed", ""),
            renderer=stanza.get("renderer", ""),
            second_viewer=stanza.get("second_viewer", ""),
            pairing_by=stanza.get("pairing_by", ""),
        )
        target = by_target[identifier]
        if status == "blocked" and not missing:
            fail(f"{where}: blocked requires missing=[...] naming the absent capabilities")
        if status == "faithful":
            if not verdict.second_viewer:
                fail(f"{where}: faithful requires a second_viewer countersign")
            # context-only targets have no author panel to mispair; their
            # pairing is vacuously settled.
            if pairing not in ("verified", "context-only"):
                fail(f"{where}: faithful requires pairing=verified, got {pairing!r}")
        if status != "unreviewed":
            if not verdict.reviewed:
                fail(f"{where}: judged status {status!r} requires a reviewed date")
            if case_sha is None:
                fail(f"{where}: judged status {status!r} requires case_sha256")
        if case_sha is not None:
            current = sha256(REPO / target.case)
            if case_sha != current:
                fail(
                    f"{where}: stale verdict; case {target.case} changed since review "
                    f"(recorded {case_sha[:12]}, current {current[:12]}) -- re-review "
                    "or reset status=unreviewed"
                )
        if target.paper_context_only != (pairing == "context-only"):
            fail(
                f"{where}: pairing=context-only is required exactly for "
                "paper-context-only targets"
            )
        verdicts[identifier] = verdict
    missing_ids = sorted(set(by_target) - set(verdicts))
    if missing_ids:
        fail("targets without a verdict stanza: " + ", ".join(missing_ids))
    recorded_campaign = raw.get("campaign_sha256")
    if isinstance(recorded_campaign, str):
        current_campaign = campaign_digest(targets)
        if recorded_campaign != current_campaign:
            print(
                "[tenkz rmp] WARNING: campaign inputs changed since the last full "
                "review; judged verdicts stand on per-case hashes only"
            )
    return verdicts


def verdict_histogram(verdicts: dict[str, TargetVerdict]) -> dict[str, int]:
    counts = {status: 0 for status in VERDICT_STATUSES}
    for verdict in verdicts.values():
        counts[verdict.status] += 1
    return counts


def validate_verdict_consistency(targets: Sequence[Target], verdicts: dict[str, TargetVerdict]) -> None:
    """Mechanical checks that need no judgment.

    A detected defect never blocks by itself; a detected defect CONTRADICTING
    the recorded verdict blocks.  Honesty is cheap, lying is expensive.
    """
    problems: list[str] = []
    for target in targets:
        body = strip_comments((REPO / target.case).read_text(encoding="utf-8"))
        verdict = verdicts[target.id]
        # Literal prose standing in for a declared diagram.
        if "\\text{" in body:
            concedes = verdict.status in CONCEDING_STATUSES
            declared = "text-substitution" in verdict.defects
            if not (concedes or declared):
                problems.append(
                    f"{target.id}: case body typesets \\text{{...}} where the manifest "
                    "declares diagram ink; record defects=[\"text-substitution\"] or a "
                    "conceding status"
                )
        problems.extend(
            structural_capability_problems(target.id, target.capabilities, body)
        )
    if problems:
        fail("verdict consistency failed:\n" + "\n".join(problems))


def tex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "#": r"\#",
        "$": r"\$",
        "%": r"\%",
        "&": r"\&",
        "_": r"\_",
        "^": r"\textasciicircum{}",
        "~": r"\textasciitilde{}",
    }
    return "".join(replacements.get(character, character) for character in text)


def verdict_detail(verdict: TargetVerdict) -> str:
    parts: list[str] = []
    if verdict.defects:
        parts.append("defects: " + ", ".join(verdict.defects))
    if verdict.missing:
        parts.append("missing: " + ", ".join(verdict.missing))
    if not parts and verdict.note:
        parts.append(verdict.note)
    return "; ".join(parts) if parts else "none recorded"


def generate_book_index(results: list[BuildResult], destination: Path) -> None:
    targets = [result.target for result in results]
    verdicts = load_verdicts(targets)
    validate_verdict_consistency(targets, verdicts)
    counts = verdict_histogram(verdicts)
    lines = [
        "% Generated by scripts/tenkz_rmp.py; do not edit.",
        r"\RMPVerdictSummary"
        + "".join("{" + str(counts[status]) + "}" for status in VERDICT_STATUSES),
        r"\RMPMethodPages",
    ]
    lines.append(r"\RMPAtlasBegin")
    for corpus in CORPORA:
        for section in SECTIONS:
            count = sum(
                result.target.corpus == corpus and result.target.section == section
                for result in results
            )
            if count:
                lines.append(
                    r"\RMPAtlasRow"
                    + "{" + tex_escape(corpus) + "}"
                    + "{" + tex_escape(section) + "}"
                    + "{" + str(count) + "}"
                )
    lines.append(r"\RMPAtlasEnd")
    current_corpus = None
    current_section = None
    for result in results:
        target = result.target
        if target.corpus != current_corpus:
            title = (
                "Published corpus"
                if target.corpus == "published"
                else "Author-workbench archive"
            )
            lines.append(rf"\RMPPart{{{tex_escape(title)}}}")
            current_corpus = target.corpus
            current_section = None
        if target.section != current_section:
            lines.append(rf"\RMPSection{{{tex_escape(target.section)}}}")
            current_section = target.section
        case = REPO / target.case
        line_count = len(case.read_text(encoding="utf-8").splitlines())
        fixture_digest = "none"
        if target.fixture is not None:
            fixture_digest = sha256(REPO / target.fixture)
        signature = "; ".join(result.audit_signatures)
        placement = "; ".join(
            f"{item['order']}: {item['asset']} line {item['line']}" for item in target.placements
        ) or "author source order"
        source_mode = "paper-context-only" if target.paper_context_only else "author source mapped"
        fields = (
            target.id,
            target.corpus,
            target.section,
            str(target.order),
            target.formula,
            target.ink,
            target.boundary,
            target.source,
            ", ".join(target.capabilities),
            placement,
            source_mode,
            signature,
            f"{result.width} x {result.height} pt; {result.pages} page(s)",
            sha256(case),
            fixture_digest,
            target.case.as_posix(),
            str(line_count),
        )
        first = "".join("{" + tex_escape(field) + "}" for field in fields[:9])
        second = "".join("{" + tex_escape(field) + "}" for field in fields[9:])
        artifact = r"\detokenize{" + result.pdf.as_posix() + "}"
        verdict = verdicts[target.id]
        lines.append(
            r"\RMPCaseVerdict"
            + "{" + tex_escape(verdict.status) + "}"
            + "{" + tex_escape(verdict.pairing) + "}"
            + "{" + tex_escape(verdict_detail(verdict)) + "}"
        )
        lines.append(
            r"\RMPCaseSpread" + first
            + r"\RMPCaseEvidence" + second
            + "{" + artifact + "}"
        )
    lines.append(r"\RMPGrammarIndexBegin")
    capabilities: dict[str, list[str]] = {}
    for result in results:
        for capability in result.target.capabilities:
            capabilities.setdefault(capability, []).append(result.target.id)
    for capability in sorted(capabilities):
        consumers = capabilities[capability]
        lines.append(
            r"\RMPGrammarRow"
            + "{" + tex_escape(capability) + "}"
            + "{" + str(len(consumers)) + "}"
            + "{" + tex_escape(", ".join(consumers)) + "}"
        )
    lines.append(r"\RMPGrammarIndexEnd")
    lines.append(r"\RMPVerdictTablesBegin")
    for result in results:
        verdict = verdicts[result.target.id]
        lines.append(
            r"\RMPVerdictRow"
            + "{" + tex_escape(result.target.id) + "}"
            + "{" + tex_escape(verdict.status) + "}"
            + "{" + tex_escape(verdict.pairing) + "}"
            + "{" + tex_escape(", ".join(verdict.defects) or "none") + "}"
            + "{" + tex_escape(", ".join(verdict.missing) or verdict.note or "none") + "}"
        )
    lines.extend((r"\RMPVerdictTablesEnd", ""))
    destination.write_text("\n".join(lines), encoding="utf-8")


def compile_book(results: list[BuildResult], work: Path) -> Path:
    index = work / "rmp-benchmark-index.tex"
    generate_book_index(results, index)
    driver = work / "tenkz-rmp-benchmark-driver.tex"
    driver.write_text(
        "\\def\\TenkzRMPGeneratedIndex{" + index.as_posix() + "}\n"
        "\\input{" + BOOK_SOURCE.as_posix() + "}\n",
        encoding="utf-8",
    )
    env = tex_environment(work)
    # Pass 1 discovers entries, pass 2 materializes the multi-page contents,
    # and pass 3 stabilizes destinations after that contents block shifts the
    # body.  Two passes are insufficient for the full 130-target book.
    for pass_number in (1, 2, 3):
        result = run(
            [
                require_tool("timeout"),
                "180",
                require_tool("xelatex"),
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-jobname=tenkz-rmp-benchmark",
                driver.name,
            ],
            cwd=work,
            timeout=185,
            env=env,
            label=f"benchmark book XeLaTeX pass {pass_number}",
        )
        (work / f"book-pass-{pass_number}.txt").write_text(result.stdout, encoding="utf-8")
    log = work / "tenkz-rmp-benchmark.log"
    try:
        log_text = log.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        fail(f"cannot inspect benchmark book log: {exc}")
    overfull = [
        line for line in log_text.splitlines()
        if line.startswith("Overfull \\hbox") or line.startswith("Overfull \\vbox")
    ]
    if overfull:
        fail("benchmark book has overfull/clipped boxes:\n" + "\n".join(overfull[:20]))
    pdf = work / "tenkz-rmp-benchmark.pdf"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        fail("benchmark book produced no PDF")
    return pdf


def install_pdf(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = destination.with_name(f".{destination.name}.staging.{os.getpid()}")
    shutil.copy2(source, stage)
    os.replace(stage, destination)


def render_pdf_pages(pdf: Path, destination: Path, stem: str) -> list[Path]:
    pdftocairo = require_tool("pdftocairo")
    _, _, pages = pdf_dimensions(pdf)
    destination.mkdir(parents=True, exist_ok=True)
    outputs: list[Path] = []
    for page in range(1, pages + 1):
        output = destination / f"page-{page:03d}.png"
        run(
            [
                pdftocairo,
                "-png",
                "-r",
                "200",
                "-f",
                str(page),
                "-l",
                str(page),
                "-singlefile",
                str(pdf),
                str(output.with_suffix("")),
            ],
            cwd=destination,
            timeout=120,
            label=f"render {stem} page {page}",
        )
        if not output.is_file() or output.stat().st_size == 0:
            fail(f"rendering produced no PNG for {stem} page {page}")
        outputs.append(output)
    return outputs


def render_pdf_svgs(pdf: Path, destination: Path, stem: str) -> list[Path]:
    """Render target PDFs for the web pipeline without raster design input."""
    pdftocairo = require_tool("pdftocairo")
    _, _, pages = pdf_dimensions(pdf)
    destination.mkdir(parents=True, exist_ok=True)
    outputs: list[Path] = []
    for page in range(1, pages + 1):
        output = destination / f"page-{page:03d}.svg"
        run(
            [
                pdftocairo,
                "-svg",
                "-f",
                str(page),
                "-l",
                str(page),
                str(pdf),
                str(output),
            ],
            cwd=destination,
            timeout=120,
            label=f"SVG render {stem} page {page}",
        )
        if not output.is_file() or output.stat().st_size == 0:
            fail(f"rendering produced no SVG for {stem} page {page}")
        outputs.append(output)
    return outputs


def transactional_render(
    results: list[BuildResult], book: Path, manifest: Path
) -> tuple[int, Path]:
    # Reuse the corpus renderer's hardened destination locking and atomic swap.
    sys.path.insert(0, str(REPO / "scripts"))
    import tenkz_render_corpus as render_core  # pylint: disable=import-outside-toplevel

    output = RENDER_OUTPUT
    output.parent.mkdir(parents=True, exist_ok=True)
    input_root = book.parent
    with render_core.destination_lock(output):
        render_core.validate_paths(
            input_root, output, [REPO, REPO / "tests", REPO / "docs", REPO / "tex"]
        )
        expected = render_core.destination_snapshot(output)
    stage = Path(tempfile.mkdtemp(prefix=f".{output.name}.staging.", dir=output.parent))
    artifacts: list[Path] = []
    census: list[tuple[str, int, int]] = []
    try:
        for result in results:
            target_dir = stage / "targets" / result.target.id
            rendered = render_pdf_pages(result.pdf, target_dir, result.target.id)
            svgs = render_pdf_svgs(result.pdf, target_dir, result.target.id)
            artifacts.extend(rendered)
            artifacts.extend(svgs)
            census.append((f"target/{result.target.id}", len(rendered), len(svgs)))
        rendered_book = render_pdf_pages(book, stage / "book", "benchmark book")
        artifacts.extend(rendered_book)
        census.append(("book/tenkz-rmp-benchmark", len(rendered_book), 0))
        (stage / render_core.MARKER_NAME).write_text(render_core.MARKER_CONTENT, encoding="utf-8")
        (stage / "CENSUS.tsv").write_text(
            "artifact\tpng_pages\tsvg_pages\n"
            + "".join(f"{name}\t{pngs}\t{svgs}\n" for name, pngs, svgs in census),
            encoding="utf-8",
        )
        (stage / "SHA256SUMS").write_text(
            "".join(
                f"{sha256(path)}  {path.relative_to(stage).as_posix()}\n"
                for path in sorted(
                    artifacts, key=lambda item: item.relative_to(stage).as_posix()
                )
            ),
            encoding="utf-8",
        )
        inputs = {manifest.resolve()}
        for result in results:
            inputs.add((REPO / result.target.case).resolve())
            if result.target.fixture is not None:
                inputs.add((REPO / result.target.fixture).resolve())
        input_lines: list[str] = []
        for path in sorted(inputs, key=lambda item: item.as_posix()):
            try:
                label = path.relative_to(REPO).as_posix()
            except ValueError:
                label = path.as_posix()
            input_lines.append(f"{sha256(path)}  {label}")
        (stage / "INPUT-SHA256SUMS").write_text(
            "\n".join(input_lines) + "\n", encoding="utf-8"
        )
        render_core.install_stage(stage, output, expected)
    except Exception:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    return len(artifacts), output


def line_range(text: str) -> tuple[int, int]:
    start, separator, end = text.partition("-")
    first, last = int(start), int(end if separator else start)
    if first < 1 or last < first:
        fail(f"author line range {text!r} is not an ascending 1-based range")
    return first, last


def validate_author_ranges(targets: Sequence[Target]) -> None:
    """Author line ranges within one corpus must not collide.

    The workbench archives the published targets' blocks and sub-blocks, so
    cross-corpus sharing is by design.  Within one corpus, a partial overlap
    means a block boundary is wrong on at least one side -- the mechanism
    behind every superimposed author panel found in review -- and an
    identical range is legal only when every owner records
    extraction_override: a shared composite block is a decision, never an
    accident.
    """
    by_key: dict[tuple[str, Path], list[Target]] = {}
    for target in targets:
        if target.author_source is not None and target.author_lines is not None:
            by_key.setdefault((target.corpus, target.author_source), []).append(target)
    problems: list[str] = []
    for (corpus, source), owners in sorted(by_key.items()):
        spans = sorted(
            (line_range(target.author_lines), target.id, target) for target in owners
        )
        for ((a_start, a_end), _, first), ((b_start, b_end), _, second) in zip(
            spans, spans[1:]
        ):
            if b_start > a_end:
                continue
            if (a_start, a_end) == (b_start, b_end):
                undeclared = [
                    target.id
                    for target in (first, second)
                    if target.extraction_override is None
                ]
                if undeclared:
                    problems.append(
                        f"{corpus} {source.as_posix()}: {first.id} and "
                        f"{second.id} share lines {a_start}-{a_end} without "
                        "extraction_override on " + ", ".join(undeclared)
                    )
            else:
                problems.append(
                    f"{corpus} {source.as_posix()}: {first.id} "
                    f"({a_start}-{a_end}) and {second.id} ({b_start}-{b_end}) "
                    "overlap"
                )
    if problems:
        fail("author line ranges collide:\n" + "\n".join(problems))


def extract_author_block(target: Target, source_root: Path, destination: Path) -> None:
    if target.author_source is None or target.author_lines is None:
        fail(f"{target.id} has no author-source block")
    source = source_root / target.author_source
    try:
        lines = source.read_text(encoding="utf-8").splitlines(keepends=True)
    except FileNotFoundError:
        fail(f"{target.id}: author source does not exist: {source}")
    except (OSError, UnicodeError) as exc:
        fail(f"{target.id}: cannot read author source {source}: {exc}")
    start, end = line_range(target.author_lines)
    if end > len(lines):
        fail(f"{target.id}: author line range {target.author_lines} exceeds {len(lines)} lines")
    raw_block = "".join(lines[start - 1:end])
    activated: list[str] = []
    path_continues = False
    for line in raw_block.splitlines():
        match = re.match(r"^(\s*)(%+)(?:\s?)(.*)$", line)
        if match and len(match.group(2)) > 1:
            # Section labels and deliberately disabled alternatives use %% or
            # %%% in the author workbench.  They are provenance, not TeX.
            activated.append(line)
            path_continues = False
            continue
        candidate = match.group(1) + match.group(3) if match else line
        stripped = candidate.strip()
        # A TikZ path may continue on the next physical line with a bare
        # coordinate.  Keep that line active whether or not the workbench
        # block itself was commented out for archival storage.
        if (
            stripped
            and not path_continues
            and not stripped.startswith(("\\", "{", "}"))
        ):
            candidate = "% " + candidate
        activated.append(candidate)
        if stripped:
            path_continues = not candidate.lstrip().startswith("%") and stripped.endswith("--")
    block = "\n".join(activated)
    begin_document = next(
        (index for index, line in enumerate(lines) if "\\begin{document}" in line),
        None,
    )
    if begin_document is None:
        fail(f"{target.id}: author source has no \\begin{{document}}: {source}")
    preamble = "".join(lines[:begin_document])
    if "\\documentclass" not in preamble:
        fail(f"{target.id}: author source has no document class: {source}")
    preamble = re.sub(
        r"\\documentclass(?:\[[^]]*\])?\{[^}]+\}",
        r"\\documentclass[tikz,border=8pt]{standalone}",
        preamble,
        count=1,
    )
    block = re.sub(r"\\(?:begin|end)\{document\}", "", block)
    has_tikz_begin = "\\begin{tikzpicture}" in block
    has_tikz_end = "\\end{tikzpicture}" in block
    if not has_tikz_begin and not has_tikz_end:
        block = "\n".join((r"\begin{tikzpicture}", block, r"\end{tikzpicture}"))
    elif has_tikz_begin and not has_tikz_end:
        block += "\n" + r"\end{tikzpicture}"
    elif has_tikz_end and not has_tikz_begin:
        block = r"\begin{tikzpicture}" + "\n" + block
    document = "\n".join(
        (
            preamble,
            r"\begin{document}",
            block,
            r"\end{document}",
            "",
        )
    )
    destination.write_text(document, encoding="utf-8")


def compile_reference(target: Target, source_root: Path, work: Path) -> Path:
    reference_dir = work / "references" / target.id
    reference_dir.mkdir(parents=True)
    source = reference_dir / f"{target.id}-reference.tex"
    extract_author_block(target, source_root, source)
    env = tex_environment(reference_dir)
    run(
        [
            require_tool("timeout"),
            "120",
            require_tool("xelatex"),
            "-interaction=nonstopmode",
            "-halt-on-error",
            source.name,
        ],
        cwd=reference_dir,
        timeout=125,
        env=env,
        label=f"author-source reference {target.id}",
    )
    pdf = source.with_suffix(".pdf")
    if not pdf.is_file():
        fail(f"{target.id}: author-source reference produced no PDF")
    return pdf


def compile_comparison(
    results: list[BuildResult], source_root: Path, work: Path, jobs: int
) -> Path:
    if not source_root.is_dir():
        fail(f"source root does not exist: {source_root}")
    references: dict[str, Path] = {}
    mapped = [result.target for result in results if result.target.author_source is not None]
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(compile_reference, target, source_root, work): target
            for target in mapped
        }
        for future in concurrent.futures.as_completed(futures):
            target = futures[future]
            try:
                references[target.id] = future.result()
            except Exception as exc:
                errors.append(f"{target.id}: {exc}")
    if errors:
        fail("author-source comparisons failed:\n" + "\n".join(errors))

    index = work / "comparison-index.tex"
    lines = ["% Generated by scripts/tenkz_rmp.py; do not edit."]
    for result in results:
        target = result.target
        if target.paper_context_only:
            lines.append(
                r"\RMPComparisonContextOnly"
                + "{" + tex_escape(target.id) + "}"
                + "{" + result.pdf.as_posix() + "}"
                + "{" + tex_escape(target.source) + "}"
            )
        else:
            lines.append(
                r"\RMPComparison"
                + "{" + tex_escape(target.id) + "}"
                + "{" + result.pdf.as_posix() + "}"
                + "{" + references[target.id].as_posix() + "}"
                + "{" + tex_escape(target.author_lines or "") + "}"
            )
    index.write_text("\n".join(lines) + "\n", encoding="utf-8")
    document = work / "comparison.tex"
    document.write_text(
        "\n".join(
            (
                r"\documentclass[10pt]{article}",
                r"\usepackage[a4paper,landscape,margin=14mm]{geometry}",
                r"\usepackage{graphicx,xcolor,fancyhdr}",
                r"\pagestyle{fancy}\fancyhf{}\rhead{tenkz RMP source comparison}\cfoot{\thepage}",
                r"\newcommand\RMPComparison[4]{\clearpage\section*{#1}\noindent"
                r"\begin{minipage}[t]{.48\textwidth}\centering\textbf{canonical tenkz}\par\medskip"
                r"\includegraphics[width=\linewidth,height=.72\textheight,"
                r"keepaspectratio]{#2}\end{minipage}\hfill"
                r"\begin{minipage}[t]{.48\textwidth}\centering"
                r"\textbf{author source, lines #4}\par\medskip"
                r"\includegraphics[width=\linewidth,height=.72\textheight,"
                r"keepaspectratio]{#3}\end{minipage}}",
                r"\newcommand\RMPComparisonContextOnly[3]{\clearpage\section*{#1}\centering"
                r"\includegraphics[width=.65\linewidth,height=.72\textheight,"
                r"keepaspectratio]{#2}\par\medskip"
                r"\textbf{paper-context-only}\quad #3}",
                r"\begin{document}",
                rf"\input{{{index.as_posix()}}}",
                r"\end{document}",
                "",
            )
        ),
        encoding="utf-8",
    )
    result = run(
        [
            require_tool("timeout"),
            "180",
            require_tool("xelatex"),
            "-interaction=nonstopmode",
            "-halt-on-error",
            document.name,
        ],
        cwd=work,
        timeout=185,
        env=tex_environment(work),
        label="comparison book XeLaTeX",
    )
    (work / "comparison-xelatex.txt").write_text(result.stdout, encoding="utf-8")
    log = document.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
    overfull = [
        line for line in log.splitlines()
        if line.startswith("Overfull \\hbox") or line.startswith("Overfull \\vbox")
    ]
    if overfull:
        fail("comparison book has overfull/clipped boxes:\n" + "\n".join(overfull[:20]))
    pdf = document.with_suffix(".pdf")
    if not pdf.is_file() or pdf.stat().st_size == 0:
        fail("comparison book produced no PDF")
    return pdf


def positive_jobs() -> int:
    raw = os.environ.get("TENKZ_RMP_JOBS", "4")
    if re.fullmatch(r"[1-9][0-9]*", raw) is None:
        fail(f"TENKZ_RMP_JOBS must be a positive integer, got {raw!r}")
    return int(raw)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Compile, audit, render, and compare the source-first tenkz RMP benchmark."
    )
    subparsers = result.add_subparsers(dest="command", required=True)
    for command in ("check", "book", "render", "compare"):
        subparser = subparsers.add_parser(command)
        if command == "check":
            selection = subparser.add_mutually_exclusive_group(required=True)
            selection.add_argument("--id", dest="target_id", metavar="TARGET")
            selection.add_argument("--section", choices=SECTIONS)
            selection.add_argument("--all", action="store_true")
        else:
            # These commands install corpus-level artifacts at stable paths;
            # allowing a partial selection could silently replace the final
            # artifact with an incomplete book, render tree, or comparison.
            subparser.add_argument("--all", action="store_true", required=True)
        if command == "compare":
            subparser.add_argument("--source-root", required=True, type=Path)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        manifest = Path(os.environ.get("TENKZ_RMP_MANIFEST", DEFAULT_MANIFEST))
        targets = load_manifest(manifest)
        selected = select_targets(targets, args)
        jobs = positive_jobs()
        # The verdict ledger is validated before any compilation: it covers
        # every target regardless of selection, and a broken ledger should
        # fail in seconds, not after 130 builds.
        verdicts = load_verdicts(targets)
        validate_verdict_consistency(targets, verdicts)
        if args.command == "compare" and not args.source_root.is_dir():
            fail(f"source root does not exist: {args.source_root}")
        with tempfile.TemporaryDirectory(prefix="tenkz-rmp-") as temporary:
            work = Path(temporary)
            results = compile_targets(selected, work, jobs)
            if args.command == "check":
                counts = verdict_histogram(verdicts)
                histogram = " | ".join(
                    f"{status} {counts[status]}" for status in VERDICT_STATUSES
                )
                pairing_counts: dict[str, int] = {state: 0 for state in PAIRING_STATES}
                for verdict in verdicts.values():
                    pairing_counts[verdict.pairing] += 1
                pairing_line = " | ".join(
                    f"{state} {count}" for state, count in pairing_counts.items() if count
                )
                print(
                    "PASS: validated, compiled, linted, and audited "
                    f"{len(results)} RMP target(s)"
                )
                print(f"Verdicts: {histogram}")
                print(f"Pairing:  {pairing_line}")
                return 0
            if args.command in {"book", "render"}:
                book = compile_book(results, work)
                install_pdf(book, BOOK_OUTPUT)
                if args.command == "book":
                    print(f"PASS: wrote benchmark book to {BOOK_OUTPUT}")
                    return 0
                png_count, destination = transactional_render(results, book, manifest)
                print(f"PASS: wrote benchmark book to {BOOK_OUTPUT}")
                print(f"PASS: rendered {png_count} target/book page(s) to {destination}")
                print(f"Checksums: {destination / 'SHA256SUMS'}")
                return 0
            comparison = compile_comparison(results, args.source_root.resolve(), work, jobs)
            install_pdf(comparison, COMPARE_OUTPUT)
            print(f"PASS: wrote source-only comparison book to {COMPARE_OUTPUT}")
            return 0
    except (OSError, RMPError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
