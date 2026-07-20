#!/usr/bin/env python3
"""Source lint for `.tex` files using the tenkz picture languages.

Rules (findings exit 1 unless escaped):

  dots     Literal `...`, `\\ldots`, or `\\cdots` inside a tenkz,
           tenkzlattice, or tenkzplanes body (or a `\\tnpic` body, which
           is a tenkz body by construction).  An ellipsis cell interrupts
           the implicit wire; literal dots typeset ink that the event
           stream cannot see, so the audited contraction graph and the
           printed picture diverge.  `\\tndots` is the only legal
           ellipsis.  Dots inside `[...]` option groups are exempt: a
           label value such as `up={$i_1\\cdots i_L$}` is math content of
           a leg label, not a wire cell (spec benchmark B4 sanctions it).

  raw-ink  Raw TikZ ink inside any tenkz-family body (`line width=`,
           `draw=`, `fill=`, `color=`, or raw `\\draw`/`\\fill`/
           `\\filldraw`/`\\shade`/`\\node`/`\\path`/`\\tikzset`).  The
           theme owns ink: a literal stroke or color bypasses the
           two-layer theme/semantic split, so the picture stops
           restyling under `\\tnset` and diverges between print and
           dark builds.

Escape: a comment `% tenkz-lint: allow <rule> <reason>` on the finding's
line or the line directly above suppresses that rule there (`allow all`
suppresses every rule).  Escaped findings are reported but do not fail.

Usage: tenkz_lint.py FILE_OR_GLOB [FILE_OR_GLOB ...]
Exit status: 1 iff at least one unescaped finding was reported.
"""

from __future__ import annotations

import glob
import re
import sys
from bisect import bisect_right
from dataclasses import dataclass
from pathlib import Path

from tenkz_audit import ENVIRONMENT_LANGS

# Bodies scanned for the dots rule: the grid languages whose cells feed
# the implicit wire.  (tenkzcd cells are math objects and tenkzfree has
# no implicit wire, so a literal ellipsis there is ordinary math.)
DOTS_ENVS = set(ENVIRONMENT_LANGS) - {"tenkzcd", "tenkzfree"}

# Bodies scanned for the raw-ink rule: every tenkz-family body -- the
# theme contract covers all five sub-languages.
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


@dataclass
class Finding:
    path: Path
    line: int
    rule: str
    snippet: str
    allowed: bool
    reason: str = ""


def strip_comments(src: str) -> str:
    """Blank out unescaped `%`-comments, preserving offsets/line numbers."""
    out: list[str] = []
    for line in src.split("\n"):
        buf = list(line)
        i = 0
        while i < len(buf):
            if buf[i] == "\\":
                i += 2
                continue
            if buf[i] == "%":
                for j in range(i, len(buf)):
                    buf[j] = " "
                break
            i += 1
        out.append("".join(buf))
    return "\n".join(out)


def _match_group(src: str, i: int, open_ch: str, close_ch: str) -> int:
    """Offset one past the group opening at `src[i]`, brace-aware: a `]`
    inside `{...}` does not close a `[...]` group.  Works for both brace
    and bracket groups.  Returns -1 if unbalanced."""
    depth_group = 0
    depth_brace = 0
    while i < len(src):
        c = src[i]
        if c == "\\":
            i += 2
            continue
        if c == open_ch and (open_ch == "{" or depth_brace == 0):
            depth_group += 1
        elif c == close_ch and (close_ch == "}" or depth_brace == 0):
            depth_group -= 1
            if depth_group == 0:
                return i + 1
        elif c == "{":
            depth_brace += 1
        elif c == "}":
            depth_brace -= 1
        i += 1
    return -1


@dataclass
class Body:
    name: str
    start: int  # offset of the body's first character in the stripped source
    text: str


def _find_env_end(src: str, name: str, pos: int) -> "re.Match[str] | None":
    """Match of the `\\end{name}` closing the `\\begin{name}` whose body
    starts at `pos`, depth-counting nested same-name environments so an
    inner `\\end` never closes the outer body.  None if unclosed."""
    token_re = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for tok in token_re.finditer(src, pos):
        depth += 1 if tok.group(1) == "begin" else -1
        if depth == 0:
            return tok
    return None


def scan_bodies(src: str) -> list[Body]:
    """tenkz-family bodies in a comment-stripped source: environment
    bodies (options group excluded) and balanced `\\tnpic` arguments."""
    bodies: list[Body] = []
    env_re = re.compile(r"\\begin\{(tenkz(?:cd|lattice|free|planes)?)\}")
    for m in env_re.finditer(src):
        name = m.group(1)
        end_m = _find_env_end(src, name, m.end())
        body_start = m.end()
        if src[body_start:body_start + 1] == "[":
            closed = _match_group(src, body_start, "[", "]")
            if closed != -1:
                body_start = closed
        body_end = end_m.start() if end_m else len(src)
        bodies.append(Body(name, body_start, src[body_start:body_end]))
    for m in re.finditer(r"\\tnpic\b", src):
        i = m.end()
        while i < len(src) and src[i] in " \t\n":
            i += 1
        if src[i:i + 1] == "[":
            closed = _match_group(src, i, "[", "]")
            if closed == -1:
                continue
            i = closed
            while i < len(src) and src[i] in " \t\n":
                i += 1
        if src[i:i + 1] != "{":
            continue
        closed = _match_group(src, i, "{", "}")
        if closed == -1:
            continue
        bodies.append(Body("tnpic", i + 1, src[i + 1:closed - 1]))
    return bodies


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
            closed = _match_group(body, i, "[", "]")
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

    def scan(text: str, base: int, rules: list[tuple[str, re.Pattern[str]]]) -> None:
        for rule, pat in rules:
            for m in pat.finditer(text):
                offset = base + m.start()
                lineno = line_of(offset)
                key = (lineno, rule)
                if key in seen:
                    continue
                seen.add(key)
                snippet = raw_lines[lineno - 1].strip() if lineno <= len(raw_lines) else ""
                findings.append(Finding(path, lineno, rule, snippet,
                                        escaped(lineno, rule)))

    for body in scan_bodies(src):
        if body.name in DOTS_ENVS:
            scan(mask_option_groups(body.text), body.start, DOTS_PATTERNS)
        if body.name in INK_ENVS:
            scan(body.text, body.start, INK_PATTERNS)
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


def main(argv: list[str]) -> int:
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
            print(f"{f.path}:{f.line}: [{f.rule}] {status}: {f.snippet}")
            if not f.allowed:
                failed += 1
    print(f"tenkz-lint: {scanned} file(s) scanned, {total} finding(s), "
          f"{failed} unescaped")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
