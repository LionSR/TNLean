#!/usr/bin/env python3
"""Check the shared blueprint figures and the contract external notes rely on.

``blueprint/src/figures/<name>.tex`` holds one tensor-network display per file.
Chapters include a figure with the literal ``\\input{figures/<name>}``; external
documents load ``blueprint/src/tnleanfigures.sty`` and write ``\\tnfigure{<name>}``.
Three consumers compile the same file (the print build, the standalone web
picture units and the notes), so a figure may assume only what all three
supply: tenkz, ``macros/diagrams.tex``, amsmath/amssymb, the four label macros
``tnleanfigures.sty`` provides, and its own ``\\tnl<Tag><Role>`` label macros,
declared with ``\\providecommand`` inside each picture body that uses them.

Checks:

* figure files: flat ``[a-z0-9_]+.tex`` names, ASCII only, a ``% Figure`` /
  ``% Owner:`` / ``% Used by:`` header, exactly one top-level display
  (``tenkzequation``, ``tenkz`` or ``tikzcd``, or one picture in ``center``)
  and nothing else outside comments, no blank line inside it, no
  ``\\label``/``\\lean``/``\\uses``/``\\leanok``/``\\notready``/refs/cites/
  definitions/inputs, no theorem-like environment or raw ``tikzpicture``, no
  blueprint macro outside the provided four, no ``\\tnset``/``\\tndeclare``/
  ``\\tikzset``/``\\providecommand`` outside a picture body, and every
  ``\\tnl...`` label macro declared in the body that uses it, with one default
  per file, listed in the header, and owned by one file only;
* hosts (chapters, appendices, content routers): every ``\\input{figures/...}``
  resolves, stands on its own line and lies outside any ``tenkzequation``;
  ``\\tnfigure`` is never used there; each figure's ``Owner:`` line names
  exactly the hosts that input it, or ``none``;
* ``tnleanfigures.sty`` provides ``\\ket``, ``\\bra``, ``\\C``, ``\\spn`` with the
  meanings ``macros/common.tex`` gives them;
* one compile (pdflatex by default, the notes' engine) of a plain ``article``
  with only ``\\usepackage{tnleanfigures}`` that typesets every figure, then
  every parametrized figure again under ``\\newcommand`` overrides.  Without a
  TeX engine or tenkz the compile is skipped with a message, unless
  ``--require-tex`` is given (the default under GitHub Actions, so the
  discovering runner ``scripts/run_diagram_tests.py`` needs no flag).

The static checks are also run on a synthetic figure and on mutations of it,
each of which must be rejected.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from blueprint_tex_tree import INPUT_RE, SOURCE_ROOT, input_path, strip_line_comment
from tenkz_paths import TenkzMissing, tenkz_tex

FIGURES = "figures"
PACKAGE = "tnleanfigures.sty"
COMMON = "macros/common.tex"
FIGURE_NAME_RE = re.compile(r"[a-z0-9_]+\.tex")
# Host paths as hosts are recorded (relative to blueprint/src), so the
# ``Owner:`` line can be compared with the actual hosts in both directions.
HOST_RE = re.compile(
    r"(?<![\w/.-])(?:(?:chapter|appendix)/[A-Za-z0-9_./-]+?\.tex|content(?:_ft_mps)?\.tex)"
)
ALLOWED_NON_FIGURES = {"README.md", ".gitkeep"}
PROVIDED = ("ket", "bra", "C", "spn")

DISPLAY_ENVS = {"tenkzequation", "tenkz", "tikzcd"}
PICTURE_ENVS = {"tenkz", "tikzcd"}
FORBIDDEN_ENVS = {
    "theorem", "proposition", "lemma", "corollary", "definition", "remark",
    "example", "proof", "conjecture", "notation", "claim", "tikzpicture",
    "figure", "figure*", "table", "samepage",
}
FORBIDDEN_COMMANDS = (
    "label", "lean", "leanok", "uses", "notready", "ref", "eqref", "cref",
    "Cref", "autoref", "pageref", "cite", "citep", "citet", "input", "include",
    "tnfigure", "newcommand", "renewcommand", "def", "gdef", "edef", "xdef",
    "let", "DeclareMathOperator", "NewDocumentCommand", "usepackage",
    "RequirePackage", "newtheorem",
)
BODY_ONLY_COMMANDS = ("tnset", "tndeclare", "tikzset", "providecommand")

ENV_TOKEN_RE = re.compile(r"\\(begin|end)\{([^}]+)\}")
TNL_RE = re.compile(r"\\tnl[A-Z][A-Za-z]*")
TNL_NAME_RE = re.compile(r"\\tnl[A-Z][a-z]*[A-Z][A-Za-z]*")
PROVIDE_RE = re.compile(r"\\providecommand\s*(\{\s*)?(\\[A-Za-z]+)")
DEFINITION_RE = re.compile(
    r"\\(newcommand|DeclareMathOperator)(\*?)\s*\{?\s*\\([A-Za-z]+)\s*\}?"
)


@dataclass(frozen=True)
class Env:
    """One environment occurrence in comment-stripped text."""

    name: str
    start: int
    body_start: int
    body_end: int
    end: int
    depth: int


def strip_comments(text: str) -> str:
    """Remove TeX comments, keeping every newline so offsets map to lines."""
    return "\n".join(strip_line_comment(line) for line in text.split("\n"))


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def braced(text: str, start: int) -> tuple[str, int]:
    """Return the balanced ``{...}`` group at ``text[start]`` and the offset after it."""
    if start >= len(text) or text[start] != "{":
        raise ValueError("expected '{'")
    depth = 0
    index = start
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2  # a control symbol such as \{ never opens or closes a group
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index], index + 1
        index += 1
    raise ValueError("unbalanced braces")


def environments(text: str) -> list[Env]:
    """Parse ``\\begin``/``\\end`` pairs; raise ``ValueError`` on a mismatch."""
    stack: list[tuple[str, int, int]] = []
    found: list[Env] = []
    for match in ENV_TOKEN_RE.finditer(text):
        kind, name = match.groups()
        if kind == "begin":
            stack.append((name, match.start(), match.end()))
            continue
        if not stack or stack[-1][0] != name:
            raise ValueError(f"line {line_of(text, match.start())}: unmatched \\end{{{name}}}")
        _, start, body_start = stack.pop()
        found.append(Env(name, start, body_start, match.start(), match.end(), len(stack)))
    if stack:
        name, start, _ = stack[-1]
        raise ValueError(f"line {line_of(text, start)}: unclosed \\begin{{{name}}}")
    return sorted(found, key=lambda env: env.start)


def command_re(names: tuple[str, ...]) -> re.Pattern[str]:
    return re.compile(r"\\(" + "|".join(map(re.escape, names)) + r")(?![A-Za-z@])")


def provided_defaults(body: str) -> list[tuple[str, str, int]]:
    """Return ``(macro, default, offset)`` for each ``\\providecommand`` in ``body``."""
    out = []
    for match in PROVIDE_RE.finditer(body):
        macro = match.group(2)
        cursor = match.end()
        if match.group(1):
            close = body.index("}", cursor)
            cursor = close + 1
        while cursor < len(body) and body[cursor].isspace():
            cursor += 1
        default, _ = braced(body, cursor)
        out.append((macro, default.strip(), match.start()))
    return out


def blueprint_macros(common: str) -> dict[str, tuple[int, str]]:
    """Map each macro ``macros/common.tex`` creates to ``(arity, meaning)``."""
    text = strip_comments(common)
    macros: dict[str, tuple[int, str]] = {}
    for match in DEFINITION_RE.finditer(text):
        kind, star, name = match.groups()
        cursor = match.end()
        arity = 0
        if kind == "newcommand":
            arity_match = re.match(r"\s*\[(\d)\]", text[cursor:])
            if arity_match:
                arity = int(arity_match.group(1))
                cursor += arity_match.end()
        while text[cursor].isspace():
            cursor += 1
        body, _ = braced(text, cursor)
        if kind == "DeclareMathOperator":
            body = f"\\operatorname{star}{{{body}}}"
        macros[name] = (arity, " ".join(body.split()))
    return macros


def package_macros(package: str) -> dict[str, tuple[int, str]]:
    """Map each macro ``tnleanfigures.sty`` provides to ``(arity, meaning)``."""
    text = strip_comments(package)
    macros: dict[str, tuple[int, str]] = {}
    for match in re.finditer(r"\\providecommand\s*\{\\([A-Za-z]+)\}(?:\[(\d)\])?", text):
        cursor = match.end()
        while text[cursor].isspace():
            cursor += 1
        body, _ = braced(text, cursor)
        macros[match.group(1)] = (int(match.group(2) or 0), " ".join(body.split()))
    return macros


def check_figure(
    name: str,
    raw: str,
    forbidden_macros: set[str],
    owners: list[str] | None,
) -> list[str]:
    """Return findings for one figure file; ``owners`` is the list of host paths."""
    findings: list[str] = []

    def fail(line: int, message: str) -> None:
        findings.append(f"figures/{name}.tex:{line}: {message}")

    for number, line in enumerate(raw.split("\n"), start=1):
        if not line.isascii():
            fail(number, "non-ASCII character (figures must compile under pdflatex)")

    lines = raw.split("\n")
    if not lines or lines[0].strip() != f"% Figure {name}.":
        fail(1, f"first line must be '% Figure {name}.'")
    owner_lines = [line for line in lines if line.startswith("% Owner:")]
    if len(owner_lines) != 1:
        fail(1, "header needs exactly one '% Owner:' line")
    if not any(line.startswith("% Used by:") for line in lines):
        fail(1, "header needs a '% Used by:' line")
    if owners is not None and len(owner_lines) == 1:
        owner = owner_lines[0].removeprefix("% Owner:").strip()
        declared = set(HOST_RE.findall(owner))
        for host in sorted(set(owners) - declared):
            fail(1, f"'% Owner:' must name {host}, which inputs this figure")
        for host in sorted(declared - set(owners)):
            fail(1, f"'% Owner:' names {host}, which does not input this figure")
        if not owners and not owner.startswith("none"):
            fail(1, "no chapter inputs this figure, so '% Owner:' must start with 'none'")

    text = strip_comments(raw)
    try:
        envs = environments(text)
    except ValueError as error:
        fail(1, f"environment structure: {error}")
        return findings

    top = [env for env in envs if env.depth == 0]
    if len(top) != 1:
        fail(1, f"expected exactly one top-level display, found {len(top)}")
    for env in top:
        if env.name == "center":
            inner = [e for e in envs if e.depth == 1 and env.start < e.start < env.end]
            if len(inner) != 1 or inner[0].name not in PICTURE_ENVS:
                fail(line_of(text, env.start), "a top-level center must hold one tenkz or tikzcd")
        elif env.name not in DISPLAY_ENVS:
            fail(line_of(text, env.start), f"top-level \\begin{{{env.name}}} is not a display")
        # Check the raw lines: stripping comments blanks comment-only lines, which TeX
        # does not read as a paragraph break (provenance comments may sit inside).
        first, last = line_of(text, env.start), line_of(text, env.end)
        for number in range(first + 1, last):
            if not lines[number - 1].strip():
                fail(number, "blank line inside the display")
    outside = text
    for env in reversed(top):
        outside = outside[: env.start] + " " * (env.end - env.start) + outside[env.end :]
    for match in re.finditer(r"\S+", outside):
        fail(line_of(text, match.start()), f"text outside the display: {match.group(0)!r}")
        break

    for env in envs:
        if env.name in FORBIDDEN_ENVS:
            fail(line_of(text, env.start), f"forbidden environment {env.name}")
    for match in command_re(FORBIDDEN_COMMANDS).finditer(text):
        fail(line_of(text, match.start()), f"forbidden command \\{match.group(1)}")
    if forbidden_macros:
        for match in command_re(tuple(sorted(forbidden_macros))).finditer(text):
            fail(
                line_of(text, match.start()),
                f"\\{match.group(1)} comes from macros/common.tex, which notes do not load;"
                " use a provided macro or add it to tnleanfigures.sty",
            )

    pictures = [env for env in envs if env.name in PICTURE_ENVS]
    in_body = bytearray(len(text))
    for env in pictures:
        in_body[env.body_start : env.body_end] = b"\1" * (env.body_end - env.body_start)
    for match in command_re(BODY_ONLY_COMMANDS).finditer(text):
        if not in_body[match.start()]:
            fail(line_of(text, match.start()), f"\\{match.group(1)} outside a picture body")

    defaults: dict[str, str] = {}
    for env in pictures:
        body = text[env.body_start : env.body_end]
        try:
            declared = provided_defaults(body)
        except ValueError as error:
            fail(line_of(text, env.body_start), f"\\providecommand: {error}")
            continue
        first_declared: dict[str, int] = {}
        for macro, default, offset in declared:
            line = line_of(text, env.body_start + offset)
            if not TNL_NAME_RE.fullmatch(macro):
                fail(line, f"{macro}: \\providecommand is only for \\tnl<Tag><Role> label macros")
                continue
            first_declared.setdefault(macro, offset)
            if defaults.setdefault(macro, default) != default:
                fail(line, f"{macro} has two defaults in one file")
        for match in TNL_RE.finditer(body):
            macro = match.group(0)
            if body[: match.start()].rstrip().endswith(("\\providecommand{", "\\providecommand")):
                continue
            if macro not in first_declared or first_declared[macro] > match.start():
                fail(
                    line_of(text, env.body_start + match.start()),
                    f"{macro} is used before this picture body declares it"
                    " (the web build compiles each body alone)",
                )
    for match in TNL_RE.finditer(text):
        if not in_body[match.start()]:
            fail(line_of(text, match.start()), f"{match.group(0)} outside a picture body")
    if defaults:
        header = " ".join(line for line in lines if line.startswith("% Label macros:"))
        for macro in defaults:
            if not re.search(re.escape(macro) + r"(?![A-Za-z])", header):
                fail(1, f"'% Label macros:' header must list {macro}")
    return findings


def figure_label_macros(raw: str) -> set[str]:
    return {macro for macro, _, _ in provided_defaults(strip_comments(raw))}


def host_files(src: Path) -> list[Path]:
    hosts = [src / "content.tex", src / "content_ft_mps.tex"]
    hosts += sorted((src / "chapter").rglob("*.tex"))
    hosts += sorted((src / "appendix").rglob("*.tex"))
    return [path for path in hosts if path.is_file()]


def check_hosts(src: Path) -> tuple[list[str], dict[str, list[str]]]:
    """Check figure inputs in hosts; return findings and figure -> hosts."""
    findings: list[str] = []
    users: dict[str, list[str]] = {}
    for path in host_files(src):
        rel = path.relative_to(src).as_posix()
        raw = path.read_text(encoding="utf-8")
        text = strip_comments(raw)
        displays = [
            (m.start(), m.end())
            for m in re.finditer(r"\\begin\{tenkzequation\}[\s\S]*?\\end\{tenkzequation\}", text)
        ]
        for match in re.finditer(r"\\tnfigure(?![A-Za-z])", text):
            findings.append(
                f"{rel}:{line_of(text, match.start())}: chapters use the literal"
                " \\input{figures/<name>}, not \\tnfigure"
            )
        for match in INPUT_RE.finditer(text):
            target = match.group(1)
            if not target.startswith(f"{FIGURES}/"):
                continue
            line = line_of(text, match.start())
            where = f"{rel}:{line}"
            stem = target.removeprefix(f"{FIGURES}/").removesuffix(".tex")
            if not FIGURE_NAME_RE.fullmatch(f"{stem}.tex"):
                findings.append(f"{where}: figure name {target!r} is not flat [a-z0-9_]+")
            if not input_path(target, src).is_file():
                findings.append(
                    f"{where}: \\input{{{target}}} does not resolve under blueprint/src"
                )
            if text.split("\n")[line - 1].strip() != match.group(0):
                findings.append(f"{where}: \\input{{{target}}} must stand alone on its line")
            if any(start < match.start() < end for start, end in displays):
                findings.append(f"{where}: \\input{{{target}}} inside a tenkzequation")
            users.setdefault(stem, []).append(rel)
    return findings, users


def check_package(src: Path) -> list[str]:
    common = blueprint_macros((src / COMMON).read_text(encoding="utf-8"))
    provided = package_macros((src / PACKAGE).read_text(encoding="utf-8"))
    findings = []
    if sorted(provided) != sorted(PROVIDED):
        findings.append(f"{PACKAGE}: provides {sorted(provided)}, expected {sorted(PROVIDED)}")
    for name, meaning in provided.items():
        if name not in common:
            findings.append(f"{PACKAGE}: \\{name} is not defined in {COMMON}")
        elif common[name] != meaning:
            findings.append(
                f"{PACKAGE}: \\{name} is {meaning}, but {COMMON} defines {common[name]}"
            )
    return findings


def static_checks(src: Path) -> tuple[list[str], list[str], dict[str, set[str]]]:
    """Run every static check; return findings, figure names and label macros."""
    findings: list[str] = []
    figures_dir = src / FIGURES
    names: list[str] = []
    if not figures_dir.is_dir():
        return [f"{FIGURES}/ is missing"], [], {}
    for entry in sorted(figures_dir.iterdir()):
        if entry.name in ALLOWED_NON_FIGURES:
            continue
        if entry.is_dir() or not FIGURE_NAME_RE.fullmatch(entry.name):
            findings.append(
                f"{FIGURES}/{entry.name}: only flat [a-z0-9_]+.tex figure files belong here"
            )
            continue
        names.append(entry.name.removesuffix(".tex"))

    findings += check_package(src)
    host_findings, users = check_hosts(src)
    findings += host_findings
    common = blueprint_macros((src / COMMON).read_text(encoding="utf-8"))
    forbidden = set(common) - set(PROVIDED)
    labels: dict[str, set[str]] = {}
    owners_of_macro: dict[str, str] = {}
    for name in names:
        raw = (figures_dir / f"{name}.tex").read_text(encoding="utf-8")
        findings += check_figure(name, raw, forbidden, users.get(name, []))
        try:
            labels[name] = figure_label_macros(raw)
        except ValueError:
            labels[name] = set()
        for macro in labels[name]:
            other = owners_of_macro.setdefault(macro, name)
            if other != name:
                findings.append(
                    f"figures/{name}.tex: {macro} is already owned by figures/{other}.tex"
                )
    return findings, names, labels


SYNTHETIC = r"""% Figure demo_case.
% Owner: none (note-only figure).
% Used by: this test.
% Label macros: \tnlDmLeft{T}
\begin{tenkzequation}
% A comment-only line inside the display is not a blank line.
\tenkzkernel
\begin{tenkz}[rows={op}, cols=1]
\providecommand{\tnlDmLeft}{T}
\tn{\tnlDmLeft}
\end{tenkz}
=
\begin{tenkz}[rows={op}, cols=1]
\providecommand{\tnlDmLeft}{T}
\tn{\ket{0}}
\tn{\tnlDmLeft}
\end{tenkz}
\end{tenkzequation}
"""

MUTATIONS = {
    "label": ("\\tn{\\ket{0}}", "\\tn{\\ket{0}}\\label{fig:x}"),
    "lean": ("\\tenkzkernel", "\\tenkzkernel\\lean{Foo}"),
    "cite": ("=\n", "=\\cite{X}\n"),
    "second display": (
        "\\end{tenkzequation}\n",
        "\\end{tenkzequation}\n\\begin{tenkz}\\end{tenkz}\n",
    ),
    "stray text": ("\\end{tenkzequation}\n", "\\end{tenkzequation}\nand more\n"),
    "non-ascii": ("{T}\n\\tn", "{\u03c4}\n\\tn"),
    "blank line": ("=\n", "=\n\n"),
    "tikzpicture": ("=\n", "=\\begin{tikzpicture}\\end{tikzpicture}\n"),
    "theorem env": ("\\begin{tenkzequation}", "\\begin{theorem}\\begin{tenkzequation}"),
    "common macro": ("\\tn{\\ket{0}}", "\\tn{\\Tr}"),
    "undeclared label": ("\\providecommand{\\tnlDmLeft}{T}\n\\tn{\\ket", "\\tn{\\ket"),
    "use before declare": (
        "\\providecommand{\\tnlDmLeft}{T}\n\\tn{\\tnlDmLeft}",
        "\\tn{\\tnlDmLeft}\n\\providecommand{\\tnlDmLeft}{T}",
    ),
    "two defaults": (
        "\\providecommand{\\tnlDmLeft}{T}\n\\tn{\\ket",
        "\\providecommand{\\tnlDmLeft}{S}\n\\tn{\\ket",
    ),
    "setting outside body": ("\\tenkzkernel", "\\tenkzkernel\\tnset{pitch=5mm}"),
    "foreign provide": (
        "\\providecommand{\\tnlDmLeft}{T}\n\\tn{\\tnlDmLeft}",
        "\\providecommand{\\foo}{T}\n\\providecommand{\\tnlDmLeft}{T}\n\\tn{\\tnlDmLeft}",
    ),
    "newcommand": ("\\tenkzkernel", "\\tenkzkernel\\newcommand{\\x}{y}"),
    "nested input": ("=\n", "=\\input{figures/other}\n"),
    "header name": ("% Figure demo_case.", "% Figure other."),
    "header owner": ("% Owner: none (note-only figure).\n", ""),
    "unlisted label": ("% Label macros: \\tnlDmLeft{T}\n", ""),
}


def self_test(src: Path) -> list[str]:
    """Check that the synthetic figure passes and each mutation is rejected."""
    common = blueprint_macros((src / COMMON).read_text(encoding="utf-8"))
    forbidden = set(common) - set(PROVIDED)
    failures = []
    clean = check_figure("demo_case", SYNTHETIC, forbidden, [])
    if clean:
        failures.append(f"synthetic figure rejected: {clean}")
    owned = check_figure("demo_case", SYNTHETIC, forbidden, ["chapter/ch99_demo.tex"])
    if not owned:
        failures.append("mutation 'owner mismatch' was accepted")
    stale = SYNTHETIC.replace(
        "% Owner: none (note-only figure).",
        "% Owner: chapter/ch99_demo.tex (demo) and chapter/ch98_stale.tex (demo).",
        1,
    )
    if not check_figure("demo_case", stale, forbidden, ["chapter/ch99_demo.tex"]):
        failures.append("mutation 'stale owner' was accepted")
    for label, (old, new) in MUTATIONS.items():
        assert SYNTHETIC.count(old) >= 1, label
        if not check_figure("demo_case", SYNTHETIC.replace(old, new, 1), forbidden, []):
            failures.append(f"mutation {label!r} was accepted")
    return failures


# A host value no figure draws by itself, so the PDF text shows the override won.
OVERRIDE = "QQQ"


def contract_document(names: list[str], labels: dict[str, set[str]]) -> str:
    """Build the note-contract document: defaults, then host overrides."""
    lines = [
        r"\documentclass{article}",
        r"\usepackage{tnleanfigures}",
        r"\begin{document}",
        f"Note contract: {len(names)} shared figures with default labels.",
    ]
    lines += [f"\\tnfigure{{{name}}}" for name in names]
    overridden = sorted(name for name in names if labels.get(name))
    if overridden:
        lines.append(r"\clearpage Host overrides via \verb|\newcommand|.")
        for macro in sorted(set().union(*(labels[name] for name in overridden))):
            lines.append(f"\\newcommand{{{macro}}}{{{OVERRIDE}}}")
        lines += [f"\\tnfigure{{{name}}}" for name in overridden]
    lines.append(r"\end{document}")
    return "\n".join(lines) + "\n"


def compile_contract(
    src: Path, names: list[str], labels: dict[str, set[str]], engine: str, require: bool
) -> list[str]:
    """Compile the note contract; return findings (empty on success or skip)."""

    def skip(reason: str) -> list[str]:
        if require:
            return [f"note-contract compile required but unavailable: {reason}"]
        print(f"SKIP: note-contract compile ({reason})")
        return []

    exe = shutil.which(engine)
    if exe is None:
        return skip(f"{engine} not found on PATH")
    try:
        tenkz_dir: Path | None = tenkz_tex()
    except TenkzMissing as error:
        if require:
            # CI must render with the pin, exactly like the blueprint, not a fallback.
            return [f"note-contract compile required but the tenkz pin is missing: {error}"]
        tenkz_dir = None
        fallback = subprocess.run(
            ["kpsewhich", "tikz-tensor-networks.sty"],
            check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        ) if shutil.which("kpsewhich") else None
        if fallback is None or not fallback.stdout.strip():
            return skip(f"{error}; no tikz-tensor-networks.sty fallback either")
        print(f"NOTE: pinned tenkz missing ({error}); compiling with the installed "
              f"tikz-tensor-networks fallback {fallback.stdout.strip()}")
    with tempfile.TemporaryDirectory(prefix="tnleanfigures-contract-") as tmp:
        work = Path(tmp)
        (work / "contract.tex").write_text(contract_document(names, labels), encoding="utf-8")
        env = os.environ.copy()
        # blueprint/src is non-recursive on purpose, as in the notes: figures/<name>
        # and macros/diagrams resolve, chapter files do not leak in by bare name.
        parts = [str(work), str(src)]
        if tenkz_dir is not None:
            parts.append(f"{tenkz_dir}//")
        env["TEXINPUTS"] = os.pathsep.join(parts) + os.pathsep + env.get("TEXINPUTS", "")
        for key, value in (
            ("pool_size", "12500000"), ("main_memory", "12000000"),
            ("extra_mem_top", "8000000"), ("extra_mem_bot", "8000000"),
        ):
            env.setdefault(key, value)
        env["max_print_line"] = "10000"  # unwrapped log lines, so file paths stay greppable
        run = subprocess.run(
            [exe, "-interaction=nonstopmode", "-halt-on-error", "contract.tex"],
            cwd=work, env=env, check=False, text=True, errors="replace",
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800,
        )
        if run.returncode or not (work / "contract.pdf").is_file():
            tail = "\n".join(run.stdout.splitlines()[-40:])
            return [f"note-contract compile with {engine} failed (exit {run.returncode}):\n{tail}"]
        log = (work / "contract.log").read_text(encoding="utf-8", errors="replace")
        expected = sum(len(labels[name]) for name in names if labels.get(name))
        pdftotext = shutil.which("pdftotext")
        if expected and pdftotext:
            text = subprocess.run(
                [pdftotext, "contract.pdf", "-"], cwd=work, check=False, text=True,
                errors="replace", stdout=subprocess.PIPE,
            ).stdout
            if text.count(OVERRIDE) < expected:
                return [
                    f"host overrides did not win: {text.count(OVERRIDE)} of at least"
                    f" {expected} label macros show the \\newcommand value"
                ]
        used = re.findall(r"\(([^()\s]*(?:tenkz|tikz-tensor-networks)\.sty)", log)
        print(f"PASS: note contract compiled with {engine}: {len(names)} figures,"
              f" {sum(1 for n in names if labels.get(n))} overridden;"
              f" tenkz from {used[0] if used else 'unknown'}")
    return []


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--src", type=Path, default=SOURCE_ROOT, help="blueprint/src root")
    parser.add_argument("--engine", default="pdflatex", help="TeX engine for the contract")
    parser.add_argument("--require-tex", action="store_true",
                        default=os.environ.get("GITHUB_ACTIONS") == "true",
                        help="fail instead of skipping when the compile cannot run"
                        " with the pinned tenkz (the default under GitHub Actions)")
    parser.add_argument("--no-compile", action="store_true", help="static checks only")
    args = parser.parse_args()
    src = args.src.resolve()

    failures = self_test(src)
    findings, names, labels = static_checks(src)
    failures += findings
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        return 1
    print(f"PASS: {len(names)} shared figures, hosts and tnleanfigures.sty pass the static checks;"
          f" {len(MUTATIONS) + 2} mutations rejected")
    if args.no_compile:
        return 0
    compile_failures = compile_contract(src, names, labels, args.engine, args.require_tex)
    for failure in compile_failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    return 1 if compile_failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
