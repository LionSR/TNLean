#!/usr/bin/env python3
r"""
Blueprint ↔ Lean code synchronisation checker.

Parses the blueprint .tex files for \lean{DeclName} and \leanok annotations,
then greps the Lean source tree for matching declarations.  Reports:

  1. Blueprint references whose Lean declaration cannot be found.
  2. \leanok tags on items whose declaration is missing from the Lean source.
  3. lean_decls entries that don't appear in any .tex file (stale entries).
  4. \lean{} refs that are not listed in lean_decls (missing entries).
  5. Summary statistics (formalization progress per chapter).

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
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|class|structure|inductive|axiom|opaque|alias)\s+"
    r"((?![\d.])[\w']+(?:\.(?![\d.])[\w']+)*)",
    re.MULTILINE,
)
# Matches a line consisting solely of a declaration keyword (with optional
# attribute/modifier prefixes), used to detect multi-line declarations whose
# name appears on the following line.
_LEAN_DECL_KEYWORD_ONLY_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private)\s+)*"
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


def _split_lean_decls(payload: str) -> list[str]:
    """Split the contents of a ``\\lean{...}`` tag into declaration names.

    Blueprint tags are often wrapped across several TeX source lines for
    readability.  Normalising whitespace here keeps the sync checker aligned
    with ``leanblueprint web``, whose generated ``lean_decls`` file includes
    declarations from both one-line and multi-line tags.
    """
    payload = re.sub(r"%[^\n]*\n\s*", "", payload)
    payload = re.sub(r"%[^\n]*$", "", payload)
    normalised = re.sub(r"\s+", " ", payload)
    return [decl.strip() for decl in normalised.split(",") if decl.strip()]


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

    @property
    def ok(self) -> bool:
        return not (
            self.missing_in_lean
            or self.leanok_but_missing
            or self.stale_lean_decls
            or self.missing_from_lean_decls_file
        )


# ---------------------------------------------------------------------------
# Parse Lean source tree
# ---------------------------------------------------------------------------

def collect_file_lean_decls(lean_file: Path, lean_root: Path) -> list[LeanDecl]:
    """Parse one Lean file and return its declarations with approximate spans."""
    text = lean_file.read_text(errors="replace")
    lines = text.splitlines()
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
            indent = len(code) - len(code.lstrip())
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
                )
            )

    return decls + field_decls


def collect_lean_decls(lean_root: Path) -> dict[str, LeanDecl]:
    """Walk all .lean files and return {fqn: LeanDecl}."""
    decls: dict[str, LeanDecl] = {}

    for lean_file in sorted(lean_root.rglob("*.lean")):
        for decl in collect_file_lean_decls(lean_file, lean_root):
            decls[decl.fqn] = decl
            # Also store without namespace prefix if the name already contains
            # dots (e.g. `Foo.bar` at top level), so both spellings match.
            if "." in decl.short_name and decl.fqn != decl.short_name:
                decls[decl.short_name] = decl

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
    """Whether a missing dependency's Lean sources may be fetched over the network.

    The TeX-only "Check blueprint compiles without errors" CI job has no Lean
    toolchain and never runs ``lake exe cache get``, so a cross-volume citation
    into the QICLean dependency (LionSR/TNLean#6622) has no checkout to resolve
    against and reads as missing. Enabling a lightweight, source-only fetch in
    that environment lets the sync check resolve those citations without a full
    Lean build. Off by default locally so a plain checker run never touches the
    network; opt in with ``BLUEPRINT_SYNC_FETCH_DEPS=1``.
    """
    return (
        os.getenv("GITHUB_ACTIONS") == "true"
        or os.getenv("BLUEPRINT_SYNC_FETCH_DEPS") == "1"
    )


def _fetch_dependency_sources(
    package_dir: Path, url: str, rev: str, input_rev: str | None
) -> bool:
    """Shallow-fetch a Lake git dependency's sources at the manifest-pinned rev.

    Only the Lean sources are needed (the sync checker greps declarations, it
    does not build), so this checks the repository out without invoking Lake.
    Returns ``True`` on success; on any failure it prints a one-line reason and
    returns ``False`` so the caller degrades gracefully.
    """
    package_dir.mkdir(parents=True, exist_ok=True)

    def git(*args: str) -> int:
        return subprocess.run(
            ["git", *args],
            cwd=package_dir,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode

    if git("init", "-q") != 0:
        print(f"  (could not initialise git repository in {package_dir})")
        return False
    git("remote", "remove", "origin")
    if git("remote", "add", "origin", url) != 0:
        print(f"  (could not add remote {url})")
        return False
    # Prefer the pinned commit; fall back to the input ref (tag/branch) when the
    # host refuses a bare-SHA fetch, then check the exact commit out.
    for ref in (rev, input_rev):
        if not ref:
            continue
        if git("fetch", "-q", "--depth", "1", "origin", ref) == 0:
            if git("checkout", "-q", "FETCH_HEAD") == 0:
                return True
    print(f"  (could not fetch {url} at {rev})")
    return False


def _resolve_dependency_lean_root(root: Path, package_name: str) -> Path | None:
    """Resolve a Lake dependency's own Lean source root from lake-manifest.json.

    A blueprint entry may cite a declaration that now lives in a separate
    repository TNLean depends on (QICLean, since the quantum-channel
    extraction, LionSR/TNLean#6622): the declaration genuinely exists in
    TNLean's build environment, just not under ``TNLean/``. This walks the
    checked-out dependency the same way ``collect_lean_decls`` walks
    ``TNLean/``, so those citations resolve instead of reading as missing.

    Returns ``None`` and prints a one-line explanation whenever the manifest,
    the package checkout, or its Lean library directory cannot be found --
    for example before ``lake update``/``lake exe cache get`` has run. This
    is a normal, expected condition (not every checkout has resolved every
    dependency), so callers should degrade gracefully rather than fail.
    """
    manifest_path = root / "lake-manifest.json"
    if not manifest_path.is_file():
        print(f"  (dependency '{package_name}' skipped: no lake-manifest.json)")
        return None
    try:
        manifest = json.loads(manifest_path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        print(
            f"  (dependency '{package_name}' skipped: cannot parse "
            f"lake-manifest.json: {error})"
        )
        return None
    packages_dir = manifest.get("packagesDir", ".lake/packages")
    entry = next(
        (p for p in manifest.get("packages", []) if p.get("name") == package_name),
        None,
    )
    if entry is None:
        print(f"  (dependency '{package_name}' skipped: not in lake-manifest.json)")
        return None
    package_dir = root / packages_dir / package_name
    if not package_dir.is_dir():
        url = entry.get("url")
        rev = entry.get("rev")
        if _dependency_fetch_enabled() and entry.get("type") == "git" and url and rev:
            print(
                f"  (dependency '{package_name}' not checked out; fetching "
                f"sources from {url})"
            )
            if not _fetch_dependency_sources(
                package_dir, url, rev, entry.get("inputRev")
            ):
                return None
        else:
            print(
                f"  (dependency '{package_name}' skipped: {package_dir} is not "
                "checked out yet -- run `lake exe cache get` first)"
            )
            return None

    lib_name: str | None = None
    lakefile = package_dir / "lakefile.toml"
    if lakefile.is_file():
        match = re.search(
            r"\[\[lean_lib\]\]\s*\n\s*name\s*=\s*\"([^\"]+)\"", lakefile.read_text()
        )
        if match:
            lib_name = match.group(1)
    candidates = [lib_name] if lib_name else []
    for child in sorted(package_dir.iterdir()):
        if child.is_dir() and child.name.lower() == package_name.lower():
            candidates.append(child.name)
    for candidate in candidates:
        candidate_dir = package_dir / candidate
        if candidate_dir.is_dir():
            return candidate_dir
    print(
        f"  (dependency '{package_name}' skipped: no Lean library directory "
        f"found under {package_dir})"
    )
    return None


# ---------------------------------------------------------------------------
# Run sync check
# ---------------------------------------------------------------------------

def run_sync(
    root: Path,
    *,
    report_file: Path | None = None,
    update_lean_decls: bool = False,
) -> SyncReport:
    lean_root = root / "TNLean"
    blueprint_src = root / "blueprint" / "src"
    lean_decls_path = root / "blueprint" / "lean_decls"

    if not lean_root.is_dir():
        raise FileNotFoundError(f"Lean source directory not found: {lean_root}")
    if not blueprint_src.is_dir():
        raise FileNotFoundError(f"Blueprint source directory not found: {blueprint_src}")

    report = SyncReport()

    # 1. Collect Lean declarations, including the qiclean dependency's own
    # source: a blueprint entry may legitimately cite a declaration that
    # moved there in the quantum-channel extraction (LionSR/TNLean#6622) --
    # it still resolves in TNLean's build environment, just not under
    # TNLean/. TNLean's own declarations take precedence on any name clash.
    print("Scanning Lean source tree …")
    report.lean_decls = collect_lean_decls(lean_root)
    print(f"  Found {len(report.lean_decls)} declarations in Lean source")
    qiclean_root = _resolve_dependency_lean_root(root, "qiclean")
    if qiclean_root is not None:
        qiclean_decls = collect_lean_decls(qiclean_root)
        added = 0
        for fqn, decl in qiclean_decls.items():
            if fqn not in report.lean_decls:
                report.lean_decls[fqn] = decl
                added += 1
        print(
            f"  Found {len(qiclean_decls)} declarations in the qiclean "
            f"dependency ({added} new)"
        )

    # 2. Collect blueprint entries and raw tag names
    print("Scanning blueprint .tex files …")
    all_blueprint_refs = collect_blueprint_lean_refs(blueprint_src)
    all_blueprint_decl_names = {ref.lean_decl for ref in all_blueprint_refs}
    report.blueprint_entries = collect_blueprint_entries(blueprint_src)
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
