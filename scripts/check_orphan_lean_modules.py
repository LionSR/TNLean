#!/usr/bin/env python3
"""Reject new declaration-bearing Lean modules without a mathematical consumer.

An orphan module is a handwritten production module which

* is not imported by another handwritten production module;
* contains at least one named declaration; and
* contains no declaration named by a Blueprint ``\\lean{...}`` tag.

Generated import aggregators deliberately do not count as consumers: their
purpose is to make every production module compile, so counting them would
hide precisely the dead-end modules this check is intended to expose.

``ORPHAN_MODULE_ALLOWLIST`` is a ratchet.  Existing reviewed orphans may remain,
but the set may only shrink relative to the pull-request merge base.  A path
must also be removed from the allowlist as soon as it is deleted, gains a real
consumer, or gains a Blueprint citation.
"""

from __future__ import annotations

import argparse
import ast
import re
import subprocess
from collections.abc import Iterable
from pathlib import Path

from generate_import_aggregators import (
    is_generated,
    module_name,
    source_imported_modules,
)
from lean_import_syntax import strip_lean_comments


PRODUCTION_ROOT = "TNLean/"
ARCHIVE_ROOT = "TNLean/Archive/"
CHECKER_PATH = "scripts/check_orphan_lean_modules.py"

# Seeded from current main when this ratchet was introduced.  Never add a new
# path: either connect the module to a genuine consumer/Blueprint statement or
# remove it.  Existing entries are mechanically checked and must be deleted
# from this set when they cease to be orphans.
ORPHAN_MODULE_ALLOWLIST: frozenset[str] = frozenset(
    {
        "TNLean/MPS/FundamentalTheorem/SectorBNT/CanonicalFormEqualAmbient.lean",
        "TNLean/MPS/MPDO/BNTPhysicalSectorGSNNCH.lean",
        "TNLean/MPS/MPDO/FixedBondPositivePhysicalSectorRepresentative.lean",
        "TNLean/MPS/MPDO/LengthDependentRFPExample.lean",
        "TNLean/MPS/MPDO/NormalizedMPOProportionality.lean",
        "TNLean/MPS/MPDO/RescalingStableLengthDependentRFPCapstone.lean",
        "TNLean/PEPS/GaugeConsistencyConnectivityCounterexample.lean",
        "TNLean/PEPS/PhysicalToVirtualCounterexample.lean",
        "TNLean/PEPS/PositivityCounterexamples.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSiteMul.lean",
        "TNLean/PEPS/TorusReferenceBlockingData.lean",
        "TNLean/PEPS/TorusWindowFamilyVertical.lean",
        "TNLean/PEPS/TorusWindowSingleCrossingObstruction.lean",
    }
)

DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|inductive|opaque|alias|instance)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)
BLUEPRINT_LEAN_RE = re.compile(r"\\lean(?:\[[^\]]*\])?\{([^{}]+)\}")


def _tracked_production_sources(root: Path) -> list[Path]:
    """Return version-controlled production sources, including unignored additions."""
    result = subprocess.run(
        [
            "git",
            "-C",
            str(root),
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            "TNLean",
            "TNLean.lean",
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    paths = result.stdout.decode("utf-8").split("\0")
    return sorted(
        resolved
        for path in paths
        if path.endswith(".lean")
        and (path == "TNLean.lean" or path.startswith(PRODUCTION_ROOT))
        and not path.startswith(ARCHIVE_ROOT)
        and (resolved := root / path).is_file()
    )


def _declared_names(path: Path) -> set[str]:
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return set()
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return set()
    return {
        qualified.rsplit(".", 1)[-1]
        for qualified in DECLARATION_RE.findall(uncommented)
    }


def _blueprint_names(root: Path) -> set[str]:
    """Return final identifier components occurring in Blueprint Lean tags."""
    names: set[str] = set()
    blueprint = root / "blueprint"
    if not blueprint.is_dir():
        return names
    for path in blueprint.rglob("*.tex"):
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        for tagged in BLUEPRINT_LEAN_RE.findall(source):
            for declaration in tagged.split(","):
                final = declaration.strip().rsplit(".", 1)[-1]
                if final:
                    names.add(final)
    return names


def find_orphan_modules(root: Path) -> set[str]:
    """Return current declaration-bearing, Blueprint-uncited orphan paths."""
    source_root = root / "TNLean"
    sources = _tracked_production_sources(root)
    handwritten = [path for path in sources if not is_generated(path, source_root)]
    handwritten_modules = {module_name(path, root): path for path in handwritten}

    imported_by_handwritten: set[str] = set()
    for path in handwritten:
        imported_by_handwritten.update(source_imported_modules(path))

    blueprint_names = _blueprint_names(root)
    orphans: set[str] = set()
    for module, path in handwritten_modules.items():
        declarations = _declared_names(path)
        if (
            declarations
            and module not in imported_by_handwritten
            and declarations.isdisjoint(blueprint_names)
        ):
            orphans.add(path.relative_to(root).as_posix())
    return orphans


def _allowlist_from_source(source: str) -> frozenset[str]:
    """Read ``ORPHAN_MODULE_ALLOWLIST`` from one checker source revision."""
    tree = ast.parse(source)
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(
            isinstance(target, ast.Name) and target.id == "ORPHAN_MODULE_ALLOWLIST"
            for target in targets
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
            raise ValueError("ORPHAN_MODULE_ALLOWLIST must be a literal frozenset")
        if not value.args:
            return frozenset()
        parsed = ast.literal_eval(value.args[0])
        if not isinstance(parsed, set) or not all(isinstance(path, str) for path in parsed):
            raise ValueError("ORPHAN_MODULE_ALLOWLIST must contain only literal paths")
        return frozenset(parsed)
    raise ValueError("ORPHAN_MODULE_ALLOWLIST assignment not found")


def _allowlist_at_merge_base(root: Path, base_ref: str) -> frozenset[str] | None:
    """Return the orphan baseline at the merge base with ``base_ref``."""
    merge_base = subprocess.run(
        ["git", "-C", str(root), "merge-base", "HEAD", base_ref],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if merge_base.returncode != 0:
        raise ValueError(
            f"cannot find merge base with {base_ref}: {merge_base.stderr.strip()}"
        )
    base_commit = merge_base.stdout.strip()
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"{base_commit}:{CHECKER_PATH}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        missing_path = (
            "does not exist in" in result.stderr
            or "exists on disk, but not in" in result.stderr
        )
        if missing_path:
            return None
        raise ValueError(
            f"cannot read checker at merge base {base_commit}: {result.stderr.strip()}"
        )
    return _allowlist_from_source(result.stdout)


def check_orphan_modules(
    root: Path,
    allowlist: frozenset[str] = ORPHAN_MODULE_ALLOWLIST,
    base_allowlist: frozenset[str] | None = None,
) -> int:
    """Check the orphan-module ratchet and return a process exit status."""
    try:
        current = find_orphan_modules(root)
    except (subprocess.CalledProcessError, UnicodeDecodeError) as error:
        print(f"::error title=Orphan Lean module check failed::{error}")
        return 1

    errors: list[str] = []
    if base_allowlist is not None:
        for path in sorted(allowlist - base_allowlist):
            errors.append(
                f"{path}: added to the orphan-module allowlist; this set may only shrink"
            )

    for path in sorted(allowlist - current):
        errors.append(
            f"{path}: stale orphan-module allowlist entry; remove it now that the "
            "module is deleted, cited, or consumed"
        )
    for path in sorted(current - allowlist):
        errors.append(
            f"{path}: new declaration-bearing module has no handwritten importer "
            "and no Blueprint citation"
        )

    for message in errors:
        path = message.split(":", 1)[0]
        print(f"::error file={path},title=Orphan Lean module ratchet::{message}")

    print(
        f"Checked production modules: {len(current)} current orphan(s), "
        f"{len(allowlist)} allowlisted, {len(current - allowlist)} new."
    )
    return 1 if errors else 0


def _print_literal(paths: Iterable[str]) -> None:
    for path in sorted(paths):
        print(f'        "{path}",')


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject new declaration-bearing Lean modules without consumers."
    )
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root")
    parser.add_argument("--base-ref", help="Ref whose merge base supplies the ratchet baseline")
    parser.add_argument(
        "--print-current",
        action="store_true",
        help="Print current candidates as allowlist literal entries and exit",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    if args.print_current:
        _print_literal(find_orphan_modules(root))
        return 0

    base_allowlist: frozenset[str] | None = None
    if args.base_ref is not None:
        try:
            base_allowlist = _allowlist_at_merge_base(root, args.base_ref)
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Orphan Lean module check failed::{error}")
            return 1
        if base_allowlist is None:
            print(
                "Initializing the orphan-module debt baseline: the checker is absent "
                f"from {args.base_ref}."
            )
    return check_orphan_modules(root, base_allowlist=base_allowlist)


if __name__ == "__main__":
    raise SystemExit(main())
