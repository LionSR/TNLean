#!/usr/bin/env python3
"""Source lint for `.tex` files using the tenkz picture languages.

Rules (findings exit 1 unless escaped):

  dots     Literal `...`, `\\ldots`, or `\\cdots` inside a tenkz body.
           An ellipsis cell interrupts
           the implicit wire; literal dots typeset ink that the event
           stream cannot see, so the audited contraction graph and the
           printed picture diverge.  `\\tn[skin=dots]` is the only legal
           ellipsis.  Dots inside `[...]` option groups are exempt: a
           label value such as `ports={90:physical:$i_1\\cdots i_L$}` is
           math content of a leg label, not a wire cell.

  raw-ink  Raw TikZ ink inside any tenkz-family body (`line width=`,
           `draw=`, `fill=`, `color=`, or raw `\\draw`/`\\fill`/
           `\\filldraw`/`\\shade`/`\\node`/`\\path`/`\\tikzset`).  The
           theme owns ink: a literal stroke or color bypasses the
           two-layer theme/semantic split, so the picture stops
           restyling under `\\tnset` and diverges between print and
           dark builds.

  rmp-*    Canonical RMP case files additionally require the six provenance
           headers, preamble-free source, canonical spellings, public names,
           at most 88 characters per line, and at most 100 lines per case.
           The buried spellings come from the registry's tombstone rows and
           are reported with the migration each row states, so retiring a
           spelling needs no edit here.  These rules read case files alone:
           a chapter's prose may write a dead word as an English word.

Escape: a comment `% tenkz-lint: allow <rule> <reason>` on the finding's
line or the line directly above suppresses that rule there (`allow all`
suppresses every rule).  Escaped findings are reported but do not fail.

Usage: tenkz_lint.py FILE_OR_GLOB [FILE_OR_GLOB ...]
Exit status: 1 iff at least one unescaped finding was reported.
"""

from __future__ import annotations

import glob
import json
import re
import sys
from bisect import bisect_right
from dataclasses import dataclass
from pathlib import Path

from tenkz_audit import ENVIRONMENT_LANGS
from tenkz_language import (
    Entry,
    load_registry,
    parse_status,
    tombstone_rows,
    tombstone_shape,
)
from tenkzlib.texcase import (
    TeXEnvironmentNestingError,
    match_group,
    scan_constructs,
    strip_comments,
)

# Bodies scanned for the dots rule: the grid languages whose cells feed
# the implicit wire.
DOTS_ENVS = set(ENVIRONMENT_LANGS)

# Bodies scanned for the raw-ink rule: every tenkz-family body -- the
# theme contract covers every sub-language.
INK_ENVS = set(ENVIRONMENT_LANGS)

DOTS_PATTERNS = [
    ("dots", re.compile(r"\\ldots\b|\\cdots\b|(?<!\.)\.\.\.(?!\.)")),
]

INK_PATTERNS = [
    ("raw-ink", re.compile(
        r"line\s+width\s*=|(?<![\w@])(?:draw|fill|color)\s*=|"
        r"\\(?:draw|fill|filldraw|shade|node|path|tikzset)\b")),
]

ESCAPE_RE = re.compile(r"%\s*tenkz-lint:\s*allow\s+(\S+)(?:\s+(.*\S))?")


def registry_alias_patterns() -> list[re.Pattern[str]]:
    """Safe source patterns for compatibility keys declared by the registry."""
    aliases = {
        entry.fields[1]
        for entry in load_registry()
        if entry.kind == "key" and parse_status(entry.fields[4])[0] == "alias"
    }
    value_aliases = {
        entry.fields[1]
        for entry in load_registry()
        if entry.kind == "alias"
    }
    patterns = [
        re.compile(r"\b" + re.escape(name).replace(r"\ ", r"\s+") + r"(?:\s*=|\b)")
        for name in sorted(aliases)
    ]
    patterns.extend(
        re.compile(re.escape(spelling).replace(r"\ ", r"\s*").replace("=", r"\s*=\s*"))
        for spelling in sorted(value_aliases)
    )
    return patterns


def tombstone_patterns(entries: list[Entry]) -> list[tuple[re.Pattern[str], str]]:
    """Source patterns and migrations for the spellings a ledger buries.

    A `key=value` row is a word struck from a live alphabet, so the pattern is
    that spelling, bounded on both sides: without a left boundary a row on
    `form=` would be read out of a `transform=` ending in the same word.  The
    value may arrive in a brace group, which is ordinary key-value spelling
    and reaches the parser as the bare word.  A row spelled with a leading
    backslash is a command, whose own backslash is where it starts: a word
    boundary before it would match nothing, since neither the backslash nor
    the space before it is a word character.  An environment is named where a
    document names one, in the argument of `\\begin` or `\\end`.  A bare row
    is a key that no longer exists; where its word survives as the value of a
    live enum, the pattern steps over that live spelling, which is where a
    reader of the dead one should be.

    Every spelling arrives from `tombstone_rows` with the registry's `~`
    already read as the space a document writes, so a multi-word key is
    matched the way source spells it rather than the way the registry does.
    A row stating no spelling gets no pattern; the language check reports it.
    """
    enum_owners: dict[str, set[str]] = {}
    for entry in entries:
        if entry.kind != "key":
            continue
        enum = re.fullmatch(r"enum\(([^)]*)\)", entry.fields[2])
        if enum is None:
            continue
        for word in enum.group(1).split("|"):
            enum_owners.setdefault(word, set()).add(entry.fields[1].replace("~", " "))
    patterns: list[tuple[re.Pattern[str], str]] = []
    for scope, spelling, migration in sorted(tombstone_rows(entries)):
        key, _separator, value = spelling.partition("=")
        key, value = key.strip(), value.strip()
        shape = tombstone_shape(scope, spelling)
        if shape == "malformed":
            continue
        if shape == "command":
            expression = re.escape(spelling) + r"(?![A-Za-z])"
        elif shape == "environment":
            expression = (
                r"\\(?:begin|end)\s*\{\s*"
                + re.escape(spelling)
                + r"\s*\}"
            )
        elif shape == "value":
            expression = (
                r"(?<![\w-])"
                + re.escape(key).replace(r"\ ", r"\s+")
                + r"\s*=\s*\{?\s*"
                + re.escape(value).replace(r"\ ", r"\s*")
                + r"(?![\w-])"
            )
        else:
            # A lookbehind takes no variable width, so a live owner is stepped
            # over as the source spells it with no space around the equals.
            # A spaced `owner = word` is therefore reported, which over-reports
            # a live spelling rather than passing a dead one, and is what the
            # hardcoded expression this replaced did.  Matching only where a
            # key may appear would trade that for a possible under-report,
            # which is the failure this ledger exists to prevent.
            expression = (
                "".join(
                    f"(?<!{re.escape(owner)}=)"
                    for owner in sorted(enum_owners.get(key, set()))
                )
                + r"\b"
                + re.escape(key).replace(r"\ ", r"\s+")
                + r"\b"
            )
        patterns.append((re.compile(expression), migration))
    return patterns


def registry_tombstone_patterns() -> list[tuple[re.Pattern[str], str]]:
    """The buried spellings the registry itself records."""
    return tombstone_patterns(load_registry())


RMP_REGISTRY_ALIAS_PATTERNS = registry_alias_patterns()
RMP_REGISTRY_TOMBSTONE_PATTERNS = registry_tombstone_patterns()


@dataclass
class Finding:
    path: Path
    line: int
    rule: str
    snippet: str
    allowed: bool
    # Where a buried spelling's meaning went, reported with the finding.
    migration: str = ""


@dataclass
class Body:
    name: str
    start: int  # offset of the body's first character in the stripped source
    text: str


def scan_bodies(src: str) -> list[Body]:
    """tenkz-family bodies in a comment-stripped source: environment
    bodies (options group excluded)."""
    return [
        Body(construct.name, construct.body_start, construct.body)
        for construct in scan_constructs(src)
    ]


def mask_option_groups(body: str) -> str:
    """Blank out `[...]` option groups (offset-preserving): leg and bond
    labels live there, and label math may carry `\\cdots` legitimately."""
    buf = list(body)
    i = 0
    while i < len(buf):
        c = buf[i]
        if c == "\\":
            i += 2
            continue
        if c == "[":
            closed = match_group(body, i, "[", "]")
            if closed == -1:
                break
            for j in range(i, closed):
                if buf[j] != "\n":
                    buf[j] = " "
            i = closed
            continue
        i += 1
    return "".join(buf)


def collect_escapes(src: str) -> dict[int, list[str]]:
    """line number -> rules allowed by `% tenkz-lint: allow <rule> <reason>`."""
    escapes: dict[int, list[str]] = {}
    for lineno, line in enumerate(src.split("\n"), 1):
        m = ESCAPE_RE.search(line)
        if m:
            escapes.setdefault(lineno, []).append(m.group(1))
    return escapes


def lint_file(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8")
    escapes = collect_escapes(raw)
    src = strip_comments(raw)
    line_starts = [0] + [i + 1 for i, c in enumerate(src) if c == "\n"]
    raw_lines = raw.split("\n")

    def line_of(offset: int) -> int:
        return bisect_right(line_starts, offset)

    def escaped(lineno: int, rule: str) -> bool:
        for ln in (lineno, lineno - 1):
            for allowed in escapes.get(ln, []):
                if allowed in (rule, "all"):
                    return True
        return False

    findings: list[Finding] = []
    seen: set[tuple[int, str]] = set()  # one report per (line, rule)

    # A rule is (name, pattern), and a buried spelling adds the migration it
    # names as a third element.
    def scan(text: str, base: int, rules: list[tuple]) -> None:
        for rule, pat, *migration in rules:
            for m in pat.finditer(text):
                offset = base + m.start()
                lineno = line_of(offset)
                key = (lineno, rule)
                if key in seen:
                    continue
                seen.add(key)
                snippet = raw_lines[lineno - 1].strip() if lineno <= len(raw_lines) else ""
                findings.append(Finding(path, lineno, rule, snippet,
                                        escaped(lineno, rule),
                                        migration[0] if migration else ""))

    try:
        bodies = scan_bodies(src)
    except TeXEnvironmentNestingError as error:
        findings.append(
            Finding(path, 1, "environment-nesting", str(error), False)
        )
        bodies = []
    for body in bodies:
        if body.name in DOTS_ENVS:
            scan(mask_option_groups(body.text), body.start, DOTS_PATTERNS)
        if body.name in INK_ENVS:
            scan(body.text, body.start, INK_PATTERNS)
    if "rmp" in path.parts and "cases" in path.parts:
        required = ("Target", "Formula", "Ink", "Boundary", "Source", "Capabilities")
        for header in required:
            if not re.search(rf"^%\s*{header}:\s*\S", raw, re.MULTILINE):
                findings.append(Finding(
                    path, 1, "rmp-header", f"missing % {header}: header", False))
        source_rules = [
            ("rmp-preamble", re.compile(r"\\(?:documentclass|usepackage|begin\{document\})")),
            ("rmp-private", re.compile(r"\\(?:__tenkz|tenkz@|tenkz_[A-Za-z])")),
            ("rmp-macro", re.compile(r"\\(?:newcommand|def|NewDocumentCommand)\b")),
            ("rmp-raw-ink", re.compile(r"\\(?:draw|fill|filldraw|shade|node|path|tikzset)\b")),
            ("rmp-metadata", re.compile(r"^%\s*Fixture\s*:", re.MULTILINE)),
        ]
        source_rules.extend(("rmp-alias", pattern) for pattern in RMP_REGISTRY_ALIAS_PATTERNS)
        source_rules.extend(
            ("rmp-alias", pattern, migration)
            for pattern, migration in RMP_REGISTRY_TOMBSTONE_PATTERNS
        )
        scan(src, 0, source_rules)
        if len(raw_lines) > 100:
            findings.append(Finding(
                path, 101, "rmp-lines", f"{len(raw_lines)} lines; maximum is 100", False))
        for lineno, line in enumerate(raw_lines, 1):
            if len(line) > 88:
                findings.append(Finding(
                    path, lineno, "rmp-width", line.strip(),
                    escaped(lineno, "rmp-width")))
    findings.sort(key=lambda f: (f.line, f.rule))
    return findings


def expand_args(args: list[str]) -> list[Path]:
    paths: list[Path] = []
    for a in args:
        if any(ch in a for ch in "*?["):
            paths.extend(Path(p) for p in sorted(glob.glob(a)))
        else:
            paths.append(Path(a))
    uniq: list[Path] = []
    seen: set[Path] = set()
    for p in paths:
        if p not in seen:
            seen.add(p)
            uniq.append(p)
    return uniq


# --- Implementation census (ratcheted) --------------------------------------
#
# Two debt meters over tex/tenkz/*.code.tex, reported per file and checked
# against a manifest-backed baseline.  A shrink updates the baseline in the
# same change; any unrecorded growth fails.  The renderer-primitive lockout
# additionally scans every package .tex/.sty source, including the load map
# and generated language registry.

RENDER_STAGE_FILES = {"tenkz-render.code.tex"}
CENSUS_BASELINE = Path("tests/tenkz/render-census-baseline.json")
# The metric registry IS the table of named constants; its decimals are
# the point, not the debt.
METRIC_TABLE_FILES = {"tenkz-metric.code.tex"}
# The pgf alternative names DRAWING primitives only; the pgfkeys keyval
# machinery is parser plumbing that legitimately lives outside the renderer.
_INK_TOKEN = re.compile(
    r"\\(?:draw|path|node|fill|filldraw|shade"
    r"|pgf(?:path|usepath|text|node|setlinewidth|setstrokecolor"
    r"|setfillcolor|stroke|fill|transform)[a-z@]*)\b"
)
# Saving geometry for later string surgery creates no visible ink.  Keep this
# state-owner operation out of the raw-rendering debt meter.
_SAVED_PATH_CAPTURE = re.compile(r"\\path\s*\[([^]]*\bspath/save\s*=[^]]*)\]")
_CAPTURE_ONLY_OPTIONS = re.compile(
    r"^\s*spath/save\s*=\s*(?:\{[^{}]*\}|[^,\]]+)\s*"
    r"(?:,\s*(?:use~Hobby~shortcut|rounded~corners\s*=\s*[^,\]]+)\s*)?$"
)
_DECIMAL = re.compile(r"(?<![\w@.])\d*\.\d+")
# Only metric-table DEFINITIONS are exempt; a stray literal multiplying a
# metric macro in drawing code is exactly the debt this meter measures.
_METRIC_LINE = re.compile(r"\\def\\tenkz@(?:r@[a-z]+|basepitch|pitch)\b|\\tenkz@pitch=")
_RENDER_PRIMITIVE_REF = re.compile(r"\\__tenkz_ink_[A-Za-z@:_]+")


def ink_token_count(line: str) -> int:
    captures = sum(
        _CAPTURE_ONLY_OPTIONS.fullmatch(match.group(1)) is not None
        for match in _SAVED_PATH_CAPTURE.finditer(line)
    )
    return len(_INK_TOKEN.findall(line)) - captures


def census(repo: Path) -> int:
    ink_total = decimal_total = 0
    ink_by_file: dict[str, int] = {}
    decimal_by_file: dict[str, int] = {}
    primitive_violations: list[tuple[Path, int, str]] = []
    package_dir = repo / "tex" / "tenkz"
    package_sources = sorted(
        path for path in package_dir.iterdir()
        if path.is_file() and path.suffix in {".tex", ".sty"}
    )
    for path in package_sources:
        is_census_source = path.name.endswith(".code.tex")
        is_renderer = path.name in RENDER_STAGE_FILES
        ink = decimals = 0
        for lineno, line in enumerate(
            strip_comments(path.read_text(encoding="utf-8")).splitlines(), 1
        ):
            if not is_renderer:
                if is_census_source:
                    ink += ink_token_count(line)
                primitive_violations.extend(
                    (path, lineno, match.group())
                    for match in _RENDER_PRIMITIVE_REF.finditer(line)
                )
            if not is_census_source:
                continue
            if path.name in METRIC_TABLE_FILES:
                continue
            if not _METRIC_LINE.search(line):
                decimals += len(_DECIMAL.findall(line))
        if not is_census_source:
            continue
        ink_by_file[path.name] = ink
        decimal_by_file[path.name] = decimals
        ink_total += ink
        decimal_total += decimals
        print(f"tenkz-census: {path.name}: {ink} ink token(s), "
              f"{decimals} decimal literal(s) outside the metric table")
    print(f"tenkz-census: WARN totals: {ink_total} ink token(s) outside the "
          f"render stage, {decimal_total} stray decimal literal(s)")
    for path, lineno, primitive in primitive_violations:
        print(
            f"{path}:{lineno}: FAIL: render primitive {primitive} is owned by "
            "tenkz-render.code.tex",
            file=sys.stderr,
        )
    actual = {
        "raw_ink": {"by_file": ink_by_file, "total": ink_total},
        "decimal_literals": {
            "by_file": decimal_by_file,
            "total": decimal_total,
        },
    }
    baseline_path = repo / CENSUS_BASELINE
    try:
        expected = json.loads(baseline_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(
            f"{baseline_path}: FAIL: cannot read render census baseline: {exc}",
            file=sys.stderr,
        )
        return 1
    census_mismatch = actual != expected
    if census_mismatch:
        print(
            f"{baseline_path}: FAIL: render census differs from the recorded "
            "baseline; shrink the debt or update the manifest in the same change",
            file=sys.stderr,
        )
        for meter in ("raw_ink", "decimal_literals"):
            expected_meter = expected.get(meter, {})
            if actual[meter] != expected_meter:
                print(
                    f"  {meter}: expected {expected_meter}, got {actual[meter]}",
                    file=sys.stderr,
                )
    return 1 if primitive_violations or census_mismatch else 0


def main(argv: list[str]) -> int:
    if "--census" in argv:
        return census(Path(__file__).resolve().parent.parent)
    args = [a for a in argv if not a.startswith("-")]
    if "-h" in argv or "--help" in argv or not args:
        print(__doc__.strip().splitlines()[0])
        print("usage: tenkz_lint.py FILE_OR_GLOB [FILE_OR_GLOB ...]")
        return 0 if ("-h" in argv or "--help" in argv) else 2
    paths = expand_args(args)
    if not paths:
        print("tenkz_lint: no files matched", file=sys.stderr)
        return 2
    total = 0
    failed = 0
    scanned = 0
    for path in paths:
        if not path.exists():
            print(f"tenkz_lint: no such file: {path}", file=sys.stderr)
            failed += 1
            continue
        scanned += 1
        for f in lint_file(path):
            total += 1
            status = "allowed" if f.allowed else "FINDING"
            migration = f" ({f.migration})" if f.migration else ""
            print(f"{f.path}:{f.line}: [{f.rule}] {status}: {f.snippet}{migration}")
            if not f.allowed:
                failed += 1
    print(f"tenkz-lint: {scanned} file(s) scanned, {total} finding(s), "
          f"{failed} unescaped")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
