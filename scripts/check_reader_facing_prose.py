#!/usr/bin/env python3
"""Reject newly added reader-facing prose that uses tracker or label shorthand."""

from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
from typing import Iterable


ISSUE_REF_RE = re.compile(
    r"(?i)(?:issues?\s*)?#\d+(?:/#\d+)*|issues?\s*\\#\d+(?:/\\#\d+)*|"
    r"Issue~\\#\d+|https://github\.com/[^\s}]+/issues/\d+"
)
LEAN_CODE_SPAN_RE = re.compile(r"`([^`\n]+)`")
LEAN_PATH_LIKE_CODE_SPAN_RE = re.compile(
    r"^(?:\.?/)?(?:TNLean|docs|blueprint|scripts|Papers|Notes|\.github|\.lake)/"
    r"|^(?!\d+\.\.)[\w./-]+\.[A-Za-z][\w-]*$"
)
LATEX_MATH_MACROS = (
    r"le|ge|lt|gt|ne|sum|prod|ker|operatorname|mathrm|mathbb|mathcal|span|"
    r"tr|alpha|beta|gamma|delta|epsilon|varepsilon|zeta|eta|theta|vartheta|"
    r"iota|kappa|lambda|mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|varphi|chi|"
    r"psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Upsilon|Phi|Psi|Omega|"
    r"partial|in|subset|otimes|perp|circ|top|bot|implies|to|iff"
)
LEAN_MATH_CODE_SPAN_TRIGGER_RE = re.compile(
    r"[≤≥<>≠=+\-*/^²³¹⁻₀₁₂₃₄₅₆₇₈₉ᵢⱼᵏᵐⁿ∘⊗∑∏·"
    r"αβγδεζηθικλμνξοπρστυφχψω"
    r"ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"
    r"∂∈∉⊆⊂∪∩∖‖⟪⟫ᗮ⊤⊥⟹⇒→↔]"
    rf"|\\(?:{LATEX_MATH_MACROS})\b"
    r"|\b[A-Za-z]_[A-Za-z0-9α-ωΑ-Ω]"
    r"|\b[A-Za-zα-ωΑ-Ω][A-Za-z0-9α-ωΑ-Ω]*_\{[A-Za-z0-9α-ωΑ-Ω]+\}"
)
LEAN_SYMBOLIC_SUBSCRIPT_TOKEN_RE = re.compile(
    r"[A-Za-z]_(?:[A-Za-z0-9α-ωΑ-Ω]|[α-ωΑ-Ω][A-Za-z0-9α-ωΑ-Ω]*|[A-Z0-9]{2,})"
)
LEAN_SYMBOLIC_SCRIPT_TOKEN_RE = re.compile(
    r"[A-Za-zα-ωΑ-Ω][₀₁₂₃₄₅₆₇₈₉ᵢⱼᵏᵐⁿ⁰¹²³⁴⁵⁶⁷⁸⁹¹²³⁻]+"
)
LEAN_IDENTIFIER = (
    r"[A-Za-z_α-ωΑ-Ω]"
    r"[A-Za-z0-9_'.α-ωΑ-Ω₀₁₂₃₄₅₆₇₈₉"
    r"⁰¹²³⁴⁵⁶⁷⁸⁹ᵢⱼᵏᵐⁿ]*"
)
LEAN_NAMED_ARG_CONTENT_RE = re.compile(rf"{LEAN_IDENTIFIER}\s*:=\s*(?:{LEAN_IDENTIFIER}|\d+)")
LEAN_NAMED_ARG = rf"\(\s*{LEAN_IDENTIFIER}\s*:=\s*(?:{LEAN_IDENTIFIER}|\d+)\s*\)"
LEAN_PAREN_ARG = r"\([^=≤≥<>≠ᗮ⊤⊥]*\)"
LEAN_APPLIED_REFERENCE_RE = re.compile(
    rf"^{LEAN_IDENTIFIER}(?:\s+(?:{LEAN_IDENTIFIER}|\d+|{LEAN_NAMED_ARG}|"
    rf"{LEAN_PAREN_ARG}))*$"
)
LEAN_PAREN_ARG_RE = re.compile(r"\(([^()]*)\)")
LEAN_PAREN_FORMULA_TRIGGER_RE = re.compile(
    r"[≤≥<>≠=+\-*/^∘⊗∑∏·∈∉⊆⊂∪∩∖‖⟪⟫ᗮ⊤⊥⟹⇒→↔]"
    rf"|\\(?:{LATEX_MATH_MACROS})\b"
)
LEAN_TYPE_CONSTRUCTOR_RE = re.compile(
    r"\b(?:NSiteSpace|EuclideanSpace|WithLp|Cfg|Fin|Matrix|Submodule|Type|Prop)\b"
)
LEAN_TYPE_ATOM = rf"(?:{LEAN_IDENTIFIER}|\([^()\n]+\))"
LEAN_GENERIC_ARROW_TYPE_RE = re.compile(
    rf"^{LEAN_TYPE_ATOM}(?:\s*(?:→ₗ\[[^\]\n]+\]|→)\s*{LEAN_TYPE_ATOM})+$"
)
BLUEPRINT_LABEL_TEXTTT_RE = re.compile(r"\\texttt\{(?:thm|lem|def|prop|cor|eq):[^}]*\}")
IGNORED_TEX_MACRO_RE = re.compile(r"\\(?:label|ref|eqref|uses|lean)\{[^}]*\}")
BLUEPRINT_ENTRYPOINTS = {
    Path("blueprint/src/content.tex"),
    Path("blueprint/src/print.tex"),
    Path("blueprint/src/web.tex"),
}


@dataclass(frozen=True)
class AddedLine:
    path: Path
    line_no: int
    text: str


@dataclass(frozen=True)
class Finding:
    path: Path
    line_no: int
    message: str
    text: str


def _merge_base(base_ref: str) -> str:
    return subprocess.run(
        ["git", "merge-base", base_ref, "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()


def _git_diff(base_ref: str) -> str:
    merge_base = _merge_base(base_ref)
    return subprocess.run(
        [
            "git",
            "diff",
            "--unified=0",
            merge_base,
            "HEAD",
            "--",
            "TNLean.lean",
            ":(glob)TNLean/**/*.lean",
            "blueprint/src/content.tex",
            "blueprint/src/print.tex",
            "blueprint/src/web.tex",
            ":(glob)blueprint/src/chapter/*.tex",
        ],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout


def added_lines(diff_base: str) -> list[AddedLine]:
    lines: list[AddedLine] = []
    current_path: Path | None = None
    new_line: int | None = None
    hunk_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@")
    for raw in _git_diff(diff_base).splitlines():
        if raw.startswith("+++ b/"):
            current_path = Path(raw.removeprefix("+++ b/"))
            continue
        if raw.startswith("+++ /dev/null"):
            current_path = None
            continue
        hunk_match = hunk_re.match(raw)
        if hunk_match:
            new_line = int(hunk_match.group(1))
            continue
        if current_path is None or new_line is None:
            continue
        if raw.startswith("+"):
            lines.append(AddedLine(current_path, new_line, raw[1:]))
            new_line += 1
        elif raw.startswith("-"):
            continue
        elif raw.startswith(" "):
            new_line += 1
    return lines


def lean_files(root: Path) -> Iterable[Path]:
    root_module = root / "TNLean.lean"
    if root_module.exists():
        yield root_module.relative_to(root)
    for path in (root / "TNLean").glob("**/*.lean"):
        if "Archive" not in path.relative_to(root).parts:
            yield path.relative_to(root)


def blueprint_files(root: Path) -> Iterable[Path]:
    for rel_path in BLUEPRINT_ENTRYPOINTS:
        path = root / rel_path
        if path.exists():
            yield path
    yield from (root / "blueprint" / "src" / "chapter").glob("*.tex")


def lean_comment_lines(path: Path) -> set[int]:
    """Return line numbers lying inside Lean comments or docstrings."""
    comment_lines: set[int] = set()
    depth = 0
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith("--", i):
                comment_lines.add(line_no)
                break
            if line.startswith("/-", i):
                depth += 1
                comment_lines.add(line_no)
                i += 2
                continue
            if depth > 0:
                comment_lines.add(line_no)
                if line.startswith("-/", i):
                    depth -= 1
                    i += 2
                    continue
            i += 1
        if depth > 0:
            comment_lines.add(line_no)
    return comment_lines


def strip_tex_comment(text: str) -> str:
    escaped = False
    for i, char in enumerate(text):
        if char == "\\" and not escaped:
            escaped = True
            continue
        if char == "%" and not escaped:
            return text[:i]
        escaped = False
    return text


def normalized_tex_prose(text: str) -> str:
    return IGNORED_TEX_MACRO_RE.sub("", strip_tex_comment(text))


def is_backtick_math(span: str) -> bool:
    """Whether a Lean comment code span is mathematical notation, not an identifier."""
    if LEAN_PATH_LIKE_CODE_SPAN_RE.search(span):
        return False
    if span.startswith("*") or span.endswith("*"):
        return False
    has_math_trigger = LEAN_MATH_CODE_SPAN_TRIGGER_RE.search(span) is not None
    if not has_math_trigger:
        return False
    if is_lean_type_expression_code_span(span):
        return False
    tokens = span.split()
    applied_reference = LEAN_APPLIED_REFERENCE_RE.fullmatch(span) is not None
    if len(tokens) > 1 and applied_reference:
        if any(
            not LEAN_NAMED_ARG_CONTENT_RE.fullmatch(arg.strip())
            and LEAN_PAREN_FORMULA_TRIGGER_RE.search(arg)
            for arg in LEAN_PAREN_ARG_RE.findall(span)
        ):
            return True
        return False
    if any(
        LEAN_SYMBOLIC_SUBSCRIPT_TOKEN_RE.fullmatch(token)
        or LEAN_SYMBOLIC_SCRIPT_TOKEN_RE.fullmatch(token)
        for token in tokens
    ):
        return True
    if applied_reference:
        return False
    return True


def is_lean_type_expression_code_span(span: str) -> bool:
    """Whether a code span is a Lean type expression rather than mathematical notation."""
    if re.search(r"[{}]", span):
        return False
    if LEAN_GENERIC_ARROW_TYPE_RE.fullmatch(span):
        return True
    if LEAN_TYPE_CONSTRUCTOR_RE.search(span) is None:
        return False
    return re.search(r"(?:=|:|→|↔|≃)", span) is not None


def check_lean_line(
    path: Path,
    line_no: int,
    text: str,
    *,
    check_math_code_spans: bool = True,
) -> Finding | None:
    if ISSUE_REF_RE.search(text):
        return Finding(
            path,
            line_no,
            "Lean docstrings and comments should cite the mathematical note, not an issue number.",
            text,
        )
    if check_math_code_spans and any(
        is_backtick_math(match.group(1)) for match in LEAN_CODE_SPAN_RE.finditer(text)
    ):
        return Finding(
            path,
            line_no,
            "Lean comments should write mathematical expressions in \\(...\\), not backtick code spans.",
            text,
        )
    return None


def check_blueprint_line(path: Path, line_no: int, text: str) -> list[Finding]:
    prose = normalized_tex_prose(text)
    if not prose.strip():
        return []
    findings: list[Finding] = []
    if ISSUE_REF_RE.search(prose):
        findings.append(
            Finding(
                path,
                line_no,
                "Blueprint prose should not refer to issue numbers; use a LaTeX comment if needed.",
                text,
            )
        )
    if BLUEPRINT_LABEL_TEXTTT_RE.search(prose):
        findings.append(
            Finding(
                path,
                line_no,
                "Blueprint prose should use mathematical references, not \\texttt{thm:/lem:/def:...} labels.",
                text,
            )
        )
    return findings


def is_blueprint_prose_path(path: Path) -> bool:
    return path in BLUEPRINT_ENTRYPOINTS or (
        len(path.parts) == 4
        and path.parts[:3] == ("blueprint", "src", "chapter")
        and path.suffix == ".tex"
    )


def checks_lean_math_code_spans(path: Path) -> bool:
    return path.parts[:3] == ("TNLean", "MPS", "ParentHamiltonian")


def check_added_lines(lines: Iterable[AddedLine]) -> list[Finding]:
    findings: list[Finding] = []
    lean_comment_cache: dict[Path, set[int]] = {}
    for added in lines:
        if added.path.suffix == ".lean":
            if "Archive" in added.path.parts:
                continue
            comment_lines = lean_comment_cache.setdefault(
                added.path, lean_comment_lines(added.path)
            )
            if added.line_no in comment_lines:
                finding = check_lean_line(
                    added.path,
                    added.line_no,
                    added.text,
                    check_math_code_spans=checks_lean_math_code_spans(added.path),
                )
                if finding is not None:
                    findings.append(finding)
        elif added.path.suffix == ".tex" and is_blueprint_prose_path(added.path):
            findings.extend(check_blueprint_line(added.path, added.line_no, added.text))
    return findings


def check_all(root: Path) -> list[Finding]:
    findings: list[Finding] = []
    for rel_path in lean_files(root):
        path = root / rel_path
        comment_lines = lean_comment_lines(path)
        for line_no, text in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if line_no in comment_lines:
                finding = check_lean_line(
                    rel_path,
                    line_no,
                    text,
                    check_math_code_spans=checks_lean_math_code_spans(rel_path),
                )
                if finding is not None:
                    findings.append(finding)
    for path in blueprint_files(root):
        rel_path = path.relative_to(root)
        for line_no, text in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            findings.extend(check_blueprint_line(rel_path, line_no, text))
    return findings


def print_findings(findings: list[Finding], *, ci: bool) -> None:
    for finding in findings:
        if ci:
            print(
                f"::error file={finding.path},line={finding.line_no},"
                f"title=Reader-facing prose::{finding.message}"
            )
        print(f"{finding.path}:{finding.line_no}: {finding.message}")
        print(f"  {finding.text}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".", help="repository root")
    parser.add_argument(
        "--diff-base",
        "--base-ref",
        dest="diff_base",
        help="base ref for a merge-base added-line scan; omit for a full scan",
    )
    parser.add_argument("--ci", action="store_true", help="emit GitHub Actions annotations")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    os.chdir(root)
    diff_mode = args.diff_base is not None
    findings = check_added_lines(added_lines(args.diff_base)) if diff_mode else check_all(root)
    if not findings:
        if diff_mode:
            print("✓ No newly added reader-facing prose violations found.")
        else:
            print("✓ No reader-facing prose violations found.")
        return 0
    print_findings(findings, ci=args.ci)
    message = "Reader-facing prose violates docs/prose_style.md."
    if args.ci:
        print(f"::error::{message}")
    else:
        print(message)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
