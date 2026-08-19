#!/usr/bin/env python3
"""Guard the import direction across the channel/tensor-network boundary.

``TNLean/Channel``, ``TNLean/Entropy``, and (once created) ``TNLean/Kraus``
hold the quantum-channel and entropy theory being prepared for extraction
into a standalone library, QICLean (issue LionSR/TNLean#6560). Until that
extraction lands, these directories — together with the foundation modules
listed in ``scripts/qic_layer0_modules.txt`` — form the QIC-bound set and
must not import the tensor-network side of the monorepo: ``TNLean.MPS``,
``TNLean.QPF``, ``TNLean.Wielandt``, ``TNLean.Spectral``, ``TNLean.PEPS``,
``TNLean.QCA``, or ``TNLean.PiAlgebra``.

A secondary, shrinking-only ratchet (the pattern used by
``check_numbered_lean_files.py``) forbids new ``namespace MPSTensor``
declarations inside ``TNLean/Channel`` and ``TNLean/Entropy`` files outside
a hardcoded allowlist of known offenders.
"""

from __future__ import annotations

import argparse
import ast
from pathlib import Path
import re
import subprocess

from lean_import_syntax import IMPORT_COMMAND_RE, strip_lean_comments

ISSUE_CITATION = "issue LionSR/TNLean#6560"

# Directories whose entire tree is QIC-bound. `TNLean/Kraus` does not exist
# yet (Phase 3 of the tracked extraction creates it); scanning tolerates its
# absence.
QIC_BOUND_DIRECTORIES: tuple[str, ...] = ("TNLean/Channel", "TNLean/Entropy", "TNLean/Kraus")

# Only these two directories are scanned for the `namespace MPSTensor` ratchet;
# `TNLean/Kraus` is not yet populated and manifest-only entries are exempt.
NAMESPACE_CHECK_DIRECTORIES: tuple[str, ...] = ("TNLean/Channel", "TNLean/Entropy")

MANIFEST_PATH = Path("scripts/qic_layer0_modules.txt")

# Module prefixes belonging to the tensor-network side of the boundary. A
# QIC-bound file may not import any of these, exactly or as a sub-module.
FORBIDDEN_PREFIXES: tuple[str, ...] = (
    "TNLean.MPS",
    "TNLean.QPF",
    "TNLean.Wielandt",
    "TNLean.Spectral",
    "TNLean.PEPS",
    "TNLean.QCA",
    "TNLean.PiAlgebra",
)

NAMESPACE_MPSTENSOR_RE = re.compile(r"(?m)^[ \t]*namespace\s+MPSTensor\b")

# Shrinking-only ratchet (see scripts/check_numbered_lean_files.py). Seeded
# with the offender found by
# `rg -l "namespace MPSTensor" TNLean/Channel TNLean/Entropy` when this
# checker was introduced. New entries are rejected; existing entries are
# expected to be cleared by the in-flight edge-cutting PRs tracked under
# ISSUE_CITATION.
NAMESPACE_ALLOWLIST: frozenset[str] = frozenset(
    {
        "TNLean/Channel/PerronFrobenius/Existence.lean",
    }
)


def _forbidden_module(module: str) -> bool:
    return any(
        module == prefix or module.startswith(f"{prefix}.") for prefix in FORBIDDEN_PREFIXES
    )


def imports_of(path: Path) -> tuple[list[tuple[int, str]], str | None]:
    """Return the ``(line, module)`` import commands in *path*, or a parse error.

    Unlike ``lean_import_syntax.pure_import_modules``, this tolerates lines
    that are not import commands: QIC-bound files are ordinary Lean modules,
    not import-only aggregators.
    """
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return [], f"cannot read file: {error}"
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return [], error
    imports: list[tuple[int, str]] = []
    for line_no, line in enumerate(uncommented.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        match = IMPORT_COMMAND_RE.fullmatch(stripped)
        if match is not None:
            imports.append((line_no, match.group(1)))
    return imports, None


def qic_bound_directory_files(root: Path) -> set[Path]:
    """Return QIC-bound ``.lean`` files found by scanning the bound directories."""
    files: set[Path] = set()
    for directory in QIC_BOUND_DIRECTORIES:
        dir_path = root / directory
        if not dir_path.is_dir():
            continue
        files.update(path.relative_to(root) for path in dir_path.rglob("*.lean"))
    return files


def manifest_entries(root: Path) -> tuple[list[tuple[int, Path]], list[str]]:
    """Parse ``MANIFEST_PATH`` and return its ``(line, path)`` entries and errors."""
    manifest_path = root / MANIFEST_PATH
    entries: list[tuple[int, Path]] = []
    errors: list[str] = []
    if not manifest_path.is_file():
        errors.append(f"{MANIFEST_PATH}: manifest file is missing")
        return entries, errors
    for line_no, raw_line in enumerate(
        manifest_path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        entries.append((line_no, Path(line)))
    return entries, errors


def check_manifest_hygiene(root: Path, entries: list[tuple[int, Path]]) -> list[str]:
    """Return an error for every manifest entry whose file no longer exists."""
    errors: list[str] = []
    for line_no, relative in entries:
        if not (root / relative).is_file():
            errors.append(
                f"{MANIFEST_PATH}:{line_no}: stale manifest entry {relative.as_posix()} "
                "— file no longer exists, remove it from the manifest"
            )
    return errors


def check_import_direction(root: Path) -> tuple[list[str], int]:
    """Check the forbidden-import rule; return (errors, files checked)."""
    manifest_entries_list, manifest_errors = manifest_entries(root)
    errors = list(manifest_errors)
    errors.extend(check_manifest_hygiene(root, manifest_entries_list))

    manifest_files = {
        relative for _, relative in manifest_entries_list if (root / relative).is_file()
    }
    targets = qic_bound_directory_files(root) | manifest_files
    checked = 0
    for relative in sorted(targets, key=lambda path: path.as_posix()):
        path = root / relative
        if path.suffix != ".lean" or not path.is_file():
            continue
        checked += 1
        imports, error = imports_of(path)
        if error is not None:
            errors.append(f"{relative.as_posix()}: cannot parse imports: {error}")
            continue
        for line_no, module in imports:
            if _forbidden_module(module):
                errors.append(
                    f"{relative.as_posix()}:{line_no}: forbidden import `{module}` — "
                    "QIC-bound files must not import the tensor-network side of the "
                    f"boundary ({ISSUE_CITATION})"
                )
    return errors, checked


def channel_entropy_namespace_offenders(root: Path) -> set[str]:
    """Return QIC-bound files declaring ``namespace MPSTensor``."""
    offenders: set[str] = set()
    for directory in NAMESPACE_CHECK_DIRECTORIES:
        dir_path = root / directory
        if not dir_path.is_dir():
            continue
        for path in dir_path.rglob("*.lean"):
            try:
                source = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                continue
            uncommented, error = strip_lean_comments(source)
            if error is not None:
                continue
            if NAMESPACE_MPSTENSOR_RE.search(uncommented):
                offenders.add(path.relative_to(root).as_posix())
    return offenders


def check_namespace_ratchet(
    root: Path,
    allowlist: frozenset[str] = NAMESPACE_ALLOWLIST,
    base_allowlist: frozenset[str] | None = None,
) -> list[str]:
    """Check the `namespace MPSTensor` ratchet; return violation messages."""
    errors: list[str] = []
    offenders = channel_entropy_namespace_offenders(root)

    if base_allowlist is not None:
        for entry in sorted(allowlist - base_allowlist):
            errors.append(
                f"{entry}: added to NAMESPACE_ALLOWLIST; this set may only shrink"
            )

    for entry in sorted(allowlist):
        if entry not in offenders:
            errors.append(
                f"{entry}: stale NAMESPACE_ALLOWLIST entry; remove it now that the "
                "declaration is gone"
            )

    unexplained = offenders - allowlist
    for entry in sorted(unexplained):
        errors.append(
            f"{entry}: new `namespace MPSTensor` declaration inside the QIC-bound "
            f"layer; move it to the MPS side or extend NAMESPACE_ALLOWLIST with "
            f"justification ({ISSUE_CITATION})"
        )
    return errors


def _allowlist_from_source(source: str, variable_name: str) -> frozenset[str]:
    """Read a literal ``frozenset`` module-level assignment from checker source."""
    tree = ast.parse(source)
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(
            isinstance(target, ast.Name) and target.id == variable_name for target in targets
        ):
            continue
        value = statement.value
        if (
            not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != "frozenset"
            or len(value.args) != 1
            or value.keywords
        ):
            raise ValueError(f"{variable_name} must be a literal frozenset")
        parsed = ast.literal_eval(value.args[0])
        if not isinstance(parsed, set) or not all(isinstance(entry, str) for entry in parsed):
            raise ValueError(f"{variable_name} must contain only literal paths")
        return frozenset(parsed)
    raise ValueError(f"{variable_name} assignment not found")


def _namespace_allowlist_at_merge_base(root: Path, base_ref: str) -> frozenset[str] | None:
    """Return NAMESPACE_ALLOWLIST at the merge base with *base_ref*.

    ``None`` is returned only while this checker is first introduced and is
    therefore absent from the base revision.
    """
    merge_base = subprocess.run(
        ["git", "-C", str(root), "merge-base", "HEAD", base_ref],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if merge_base.returncode != 0:
        raise ValueError(f"cannot find merge base with {base_ref}: {merge_base.stderr.strip()}")
    base_commit = merge_base.stdout.strip()
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"{base_commit}:scripts/check_import_direction.py"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        missing_path = (
            "does not exist in" in result.stderr or "exists on disk, but not in" in result.stderr
        )
        if missing_path:
            return None
        raise ValueError(
            f"cannot read checker at merge base {base_commit}: {result.stderr.strip()}"
        )
    return _allowlist_from_source(result.stdout, "NAMESPACE_ALLOWLIST")


def check_all(root: Path, base_allowlist: frozenset[str] | None = None) -> int:
    """Run both checks against *root* and return a process exit status."""
    import_errors, checked = check_import_direction(root)
    namespace_errors = check_namespace_ratchet(
        root, allowlist=NAMESPACE_ALLOWLIST, base_allowlist=base_allowlist
    )
    errors = import_errors + namespace_errors

    for message in errors:
        path = message.split(":", 1)[0]
        print(f"::error file={path},title=Import-direction guard::{message}")

    print(
        f"Checked {checked} QIC-bound Lean file(s) against the tensor-network "
        f"import boundary: {len(import_errors)} import-direction violation(s), "
        f"{len(namespace_errors)} namespace-ratchet violation(s)."
    )
    if errors:
        print(f"::error::Import-direction guard failed ({ISSUE_CITATION}).")
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Guard the import direction across the channel/tensor-network boundary."
    )
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root")
    parser.add_argument(
        "--base-ref",
        help=(
            "Pull-request merge-base ref used to enforce that the "
            "namespace-ratchet allowlist only shrinks"
        ),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    base_allowlist: frozenset[str] | None = None
    if args.base_ref is not None:
        try:
            base_allowlist = _namespace_allowlist_at_merge_base(root, args.base_ref)
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Import-direction guard failed::{error}")
            return 1
        if base_allowlist is None:
            print(
                "Initializing the namespace-ratchet baseline: the checker is absent "
                f"from {args.base_ref}."
            )
    return check_all(root, base_allowlist=base_allowlist)


if __name__ == "__main__":
    raise SystemExit(main())
