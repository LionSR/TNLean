#!/usr/bin/env python3
"""Guard the import direction across the channel/tensor-network boundary.

``TNLean/Channel``, ``TNLean/Entropy``, and ``TNLean/Kraus``, including
their root aggregators, hold the quantum-channel and entropy theory being
prepared for extraction into a standalone library, QICLean (issue
LionSR/TNLean#6560). Until that extraction lands, these modules together with
the foundation modules listed in ``scripts/qic_layer0_modules.txt`` form the
QIC mover set. Every local import reachable from this set must remain in the
set, and the set must not import the tensor-network side of the monorepo.

Pass ``--report`` to emit a stable JSON inventory of mover paths, import
rewrites required on each side of the future package boundary, and declarations
under the ``TNLean`` or ``MPSTensor`` namespaces. Report mode is read-only.

A secondary, shrinking-only ratchet (the pattern used by
``check_numbered_lean_files.py``) forbids new ``namespace MPSTensor``
declarations inside ``TNLean/Channel`` and ``TNLean/Entropy`` files outside
a hardcoded allowlist of known offenders.
"""

from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path
import re
import subprocess

from lean_import_syntax import IMPORT_COMMAND_RE, strip_lean_comments

ISSUE_CITATION = "issue LionSR/TNLean#6560"

# Directories whose entire tree is QIC-bound, together with their generated
# root aggregators. Scanning tolerates an absent directory or aggregator.
QIC_BOUND_DIRECTORIES: tuple[str, ...] = ("TNLean/Channel", "TNLean/Entropy", "TNLean/Kraus")
QIC_BOUND_ROOTS: tuple[Path, ...] = (
    Path("TNLean/Channel.lean"),
    Path("TNLean/Entropy.lean"),
    Path("TNLean/Kraus.lean"),
)

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
NAMESPACE_COMMAND_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
SECTION_COMMAND_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_COMMAND_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$")
DECLARATION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|local|scoped)\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|coinductive|opaque|axiom|instance)"
    r"\s+(?:\([^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
REPORT_NAMESPACE_PREFIXES: tuple[str, ...] = ("TNLean", "MPSTensor")

# Shrinking-only ratchet (see scripts/check_numbered_lean_files.py). The
# boundary directories carry no `namespace MPSTensor` declarations today, so
# the allowlist is empty; the ratchet rejects any new entry, keeping the
# QIC-bound set free of tensor-network namespaces.
NAMESPACE_ALLOWLIST: frozenset[str] = frozenset()


def _forbidden_module(module: str) -> bool:
    return module == "TNLean" or any(
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
    files.update(relative for relative in QIC_BOUND_ROOTS if (root / relative).is_file())
    return files


def module_path(module: str) -> Path | None:
    """Return the repository-relative path for a local ``TNLean`` module name."""
    if module != "TNLean" and not module.startswith("TNLean."):
        return None
    return Path(*module.split(".")).with_suffix(".lean")


def module_name(path: Path) -> str:
    """Return the Lean module name corresponding to a repository-relative path."""
    return ".".join(path.with_suffix("").parts)


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


def mover_files(root: Path, entries: list[tuple[int, Path]]) -> set[Path]:
    """Return the complete mover set computed from roots, directories, and manifest."""
    manifest_files = {relative for _, relative in entries if (root / relative).is_file()}
    return qic_bound_directory_files(root) | manifest_files


def check_import_direction(root: Path) -> tuple[list[str], int]:
    """Check mover closure and forbidden imports; return (errors, files checked)."""
    manifest_entries_list, manifest_errors = manifest_entries(root)
    errors = list(manifest_errors)
    errors.extend(check_manifest_hygiene(root, manifest_entries_list))
    targets = mover_files(root, manifest_entries_list)
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
            imported_path = module_path(module)
            is_unlisted_local = (
                imported_path is not None
                and (root / imported_path).is_file()
                and imported_path not in targets
            )
            if _forbidden_module(module):
                errors.append(
                    f"{relative.as_posix()}:{line_no}: forbidden import `{module}` — "
                    "QIC-bound files must not import the tensor-network side of the "
                    f"boundary ({ISSUE_CITATION})"
                )
            elif is_unlisted_local:
                errors.append(
                    f"{relative.as_posix()}:{line_no}: unlisted local dependency "
                    f"`{module}` ({imported_path.as_posix()}) — every local TNLean "
                    "import reachable from the QIC mover seed must belong to the mover "
                    f"set; add the foundation path to {MANIFEST_PATH} ({ISSUE_CITATION})"
                )
    return errors, checked


def _rewrite_record(source: Path, line_no: int, imported: str) -> dict[str, str | int]:
    return {
        "source": source.as_posix(),
        "line": line_no,
        "from": imported,
        "to": f"QICLean{imported.removeprefix('TNLean')}",
    }


def namespaced_declarations(path: Path, relative: Path) -> list[dict[str, str | int]]:
    """Inventory declarations under ``TNLean`` or ``MPSTensor`` namespaces."""
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValueError(f"{relative.as_posix()}: cannot read declarations: {error}") from error
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        raise ValueError(f"{relative.as_posix()}: cannot parse declarations: {error}")

    scopes: list[tuple[str, tuple[str, ...]]] = []
    declarations: list[dict[str, str | int]] = []
    for line_no, line in enumerate(uncommented.splitlines(), start=1):
        namespace_match = NAMESPACE_COMMAND_RE.fullmatch(line)
        if namespace_match is not None:
            scopes.append(("namespace", tuple(namespace_match.group(1).split("."))))
            continue
        if SECTION_COMMAND_RE.fullmatch(line) is not None:
            scopes.append(("section", ()))
            continue
        if END_COMMAND_RE.fullmatch(line) is not None:
            if scopes:
                scopes.pop()
            continue

        declaration_match = DECLARATION_RE.match(line)
        if declaration_match is None:
            continue
        declared_name = declaration_match.group(1)
        if declared_name.startswith("_root_."):
            qualified_name = declared_name.removeprefix("_root_.")
        else:
            namespace_parts: list[str] = []
            for kind, parts in scopes:
                if kind != "namespace":
                    continue
                if parts and parts[0] == "_root_":
                    namespace_parts.clear()
                    namespace_parts.extend(parts[1:])
                else:
                    namespace_parts.extend(parts)
            qualified_name = ".".join((*namespace_parts, *declared_name.split(".")))
        if any(
            qualified_name.startswith(f"{prefix}.") for prefix in REPORT_NAMESPACE_PREFIXES
        ):
            declarations.append(
                {"source": relative.as_posix(), "line": line_no, "name": qualified_name}
            )
    return declarations


def source_sha(root: Path) -> str:
    """Return the exact source commit for a clean extraction inventory."""
    try:
        status = subprocess.run(
            ["git", "-C", str(root), "status", "--porcelain", "--untracked-files=all"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if status.stdout:
            raise ValueError("cannot report a dirty source tree")
        result = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except subprocess.CalledProcessError as error:
        detail = error.stderr.strip() if error.stderr else str(error)
        raise ValueError(f"cannot identify the source commit: {detail}") from error
    return result.stdout.strip()


def report_inventory(root: Path) -> dict[str, object]:
    """Return a deterministic, read-only extraction inventory for the mover set."""
    closure_errors, _ = check_import_direction(root)
    if closure_errors:
        raise ValueError("cannot report an invalid mover set: " + "; ".join(closure_errors))
    entries, _ = manifest_entries(root)
    movers = mover_files(root, entries)
    mover_modules = {module_name(path) for path in movers}

    qic_internal: list[dict[str, str | int]] = []
    declarations: list[dict[str, str | int]] = []
    for relative in sorted(movers, key=lambda path: path.as_posix()):
        imports, error = imports_of(root / relative)
        if error is not None:
            raise ValueError(f"{relative.as_posix()}: cannot parse imports: {error}")
        for line_no, imported in imports:
            if imported in mover_modules:
                qic_internal.append(_rewrite_record(relative, line_no, imported))
        declarations.extend(namespaced_declarations(root / relative, relative))

    tn_to_qic: list[dict[str, str | int]] = []
    tnlean_files = set((root / "TNLean").rglob("*.lean")) if (root / "TNLean").is_dir() else set()
    if (root / "TNLean.lean").is_file():
        tnlean_files.add(root / "TNLean.lean")
    for path in sorted(tnlean_files, key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root)
        if relative in movers:
            continue
        imports, error = imports_of(path)
        if error is not None:
            raise ValueError(f"{relative.as_posix()}: cannot parse imports: {error}")
        for line_no, imported in imports:
            if imported in mover_modules:
                tn_to_qic.append(_rewrite_record(relative, line_no, imported))

    return {
        "schema_version": 1,
        "source_sha": source_sha(root),
        "mover_paths": [
            path.as_posix() for path in sorted(movers, key=lambda item: item.as_posix())
        ],
        "qic_internal_import_rewrites": qic_internal,
        "tn_to_qic_import_rewrites": tn_to_qic,
        "namespaced_declarations": declarations,
    }


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
            or len(value.args) > 1
            or value.keywords
        ):
            raise ValueError(f"{variable_name} must be a literal frozenset")
        # Python has no empty-set literal, so an emptied allowlist is written
        # as the zero-argument call `frozenset()`.
        if not value.args:
            return frozenset()
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
        "--report",
        action="store_true",
        help="Emit the deterministic extraction inventory as JSON without writing files",
    )
    parser.add_argument(
        "--base-ref",
        help=(
            "Pull-request merge-base ref used to enforce that the "
            "namespace-ratchet allowlist only shrinks"
        ),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    if args.report:
        try:
            print(json.dumps(report_inventory(root), indent=2, sort_keys=True))
        except ValueError as error:
            print(f"::error title=Import-direction report failed::{error}")
            return 1
        return 0
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
