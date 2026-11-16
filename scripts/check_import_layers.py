#!/usr/bin/env python3
"""Reject imports that point upward between the lower layers of TNLean.

The layers below the tensor-network directories are listed in ``LAYERS``, from
the bottom up; ``ALLOWED`` says which layers each may import.  A module of
``TNLean`` outside these layers is not constrained here.  The architecture
they implement is described in ``docs/many_body_circuit_architecture.md``.

Imports are read after Lean comments are removed, so a commented-out import
is not a dependency and a trailing comment does not hide one.  An import-only
module (an aggregator) is not checked itself, but a module that imports it is
checked against everything the aggregator re-exports.

``DEBT`` is a ratchet.  It lists the imports that violated the rules when the
check was introduced.  A new violation fails, and so does an entry that no
longer violates a rule: remove it in the change that repairs the import.  With
``--base-ref`` the set is also compared with its value at the merge base, and
an added entry fails, so a new violation cannot be admitted by recording it.
"""

from __future__ import annotations

import argparse
import ast
import re
import subprocess
from collections.abc import Mapping
from pathlib import Path

from lean_import_syntax import MODULE_NAME, strip_lean_comments

PRODUCTION_ROOT = "TNLean/"
ARCHIVE_ROOT = "TNLean/Archive/"
CHECKER_PATH = "scripts/check_import_layers.py"
# An import command with the modifiers Lean accepts: ``import M``,
# ``public import M``, ``meta import M``, ``public meta import M``, ``import all M``.
IMPORT_COMMAND_RE = re.compile(
    rf"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?({MODULE_NAME})"
)

# Modules of ``TNLean/Circuit`` about operators supported on sets of sites, with
# no layer, gate or depth.  They belong to the many-body layer.
SITE_MODULES_IN_CIRCUIT: frozenset[str] = frozenset(
    f"TNLean.Circuit.{name}"
    for name in (
        "DisjointRelativeEvolution",
        "EmbeddedProduct",
        "EntropySupport",
        "ExpectationBounds",
        "ProductVector",
        "ProjectedRelativeEvolution",
        "RegionSplit",
        "RegionalSwap",
        "SiteEmbedding",
        "SiteEmbeddingNorm",
        "SiteEmbeddingOrder",
        "SiteExpectation",
        "SiteExpectationOrder",
        "SiteOperators",
        "SiteOscillation",
        "SitePermutation",
        "SitePermutationSupport",
        "SitewiseTensorSupport",
        "SpectatorOscillationSupport",
        "SpectatorSiteExpectation",
        "SupportProjection",
        "SupportedComplementProduct",
        "SupportedFunctionalCalculus",
        "SupportedGaussianIntegral",
        "SupportedGroundSpace",
        "SupportedMatrixElements",
        "SupportedNormalizedGroundSpace",
        "SupportedOperators",
    )
)

# Layer name and the module-name prefixes it owns, from the bottom up.  A module
# belongs to the first layer that claims it.
LAYERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("algebra", ("TNLean.Algebra", "TNLean.Tactic")),
    ("sites", (*sorted(SITE_MODULES_IN_CIRCUIT),)),
    ("dynamics", ("TNLean.Circuit.LiebRobinson",)),
    ("circuit", ("TNLean.Circuit",)),
    (
        "party",
        ("TNLean.Lattice.PartyCircuit", "TNLean.Lattice.Compression", "TNLean.Lattice.Sheet"),
    ),
    ("hamiltonian", ("TNLean.Lattice",)),
)

# The layers each layer may import, besides itself.  Circuits and Hamiltonians
# are siblings above the site layer: neither imports the other.
ALLOWED: dict[str, frozenset[str]] = {
    "algebra": frozenset(),
    "sites": frozenset({"algebra"}),
    "dynamics": frozenset({"algebra", "sites"}),
    "circuit": frozenset({"algebra", "sites"}),
    "hamiltonian": frozenset({"algebra", "sites", "dynamics"}),
    "party": frozenset({"algebra", "sites", "circuit"}),
}

# Existing violations only, as "importing module -> imported module".  Never add
# an entry: move the shared declaration down to the layer both sides may import.
DEBT: frozenset[str] = frozenset(
    {
        "TNLean.Circuit.SiteExpectationOrder -> TNLean.Circuit.LiebRobinson.CommutatorRecursion",
    }
)


def layer_of(module: str) -> str | None:
    """Return the layer that owns ``module``, or ``None`` if it is unconstrained."""
    for name, prefixes in LAYERS:
        for prefix in prefixes:
            if module == prefix or module.startswith(prefix + "."):
                return name
    return None


def parse_module(source: str) -> tuple[list[str], bool]:
    """Return the imported modules of a source and whether it is import-only.

    Comments are removed first.  A source whose comments cannot be removed is
    treated as having no imports and as not import-only; Lean rejects it anyway.
    """
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return [], False
    imports: list[str] = []
    import_only = True
    for line in uncommented.splitlines():
        command = line.strip()
        if not command:
            continue
        match = IMPORT_COMMAND_RE.fullmatch(command)
        if match is None:
            import_only = False
        else:
            imports.append(match.group(1))
    return imports, import_only and bool(imports)


def violations(sources: Mapping[str, str]) -> set[str]:
    """Return every ``"A -> B"`` whose import points outside the allowed layers.

    ``B`` is a module with declarations: an imported aggregator is replaced by
    the modules it re-exports, through nested aggregators.
    """
    parsed = {module: parse_module(source) for module, source in sources.items()}

    def reexports(module: str, seen: frozenset[str]) -> set[str]:
        imports, import_only = parsed.get(module, ([], False))
        if not import_only or module in seen:
            return {module}
        result: set[str] = set()
        for imported in imports:
            result |= reexports(imported, seen | {module})
        return result

    found: set[str] = set()
    for module, (imports, import_only) in parsed.items():
        layer = layer_of(module)
        if layer is None or import_only:
            continue
        for imported in imports:
            if not imported.startswith("TNLean."):
                continue
            for target_module in reexports(imported, frozenset()):
                if not target_module.startswith("TNLean."):
                    continue
                target = layer_of(target_module)
                if target is None or (target != layer and target not in ALLOWED[layer]):
                    found.add(f"{module} -> {target_module}")
    return found


def tracked_sources(root: Path) -> dict[str, str]:
    """Read the Git-tracked, non-archive Lean modules below ``TNLean/``."""
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", "TNLean"],
        check=True,
        stdout=subprocess.PIPE,
    )
    sources: dict[str, str] = {}
    for path in result.stdout.decode("utf-8").split("\0"):
        if not path.startswith(PRODUCTION_ROOT) or path.startswith(ARCHIVE_ROOT):
            continue
        if not path.endswith(".lean"):
            continue
        module = path[: -len(".lean")].replace("/", ".")
        sources[module] = (root / path).read_text(encoding="utf-8")
    return sources


def debt_from_source(source: str) -> frozenset[str]:
    """Read ``DEBT`` from one revision of this checker."""
    tree = ast.parse(source)
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(isinstance(target, ast.Name) and target.id == "DEBT" for target in targets):
            continue
        value = statement.value
        if (
            not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != "frozenset"
            or len(value.args) != 1
            or value.keywords
        ):
            raise ValueError("DEBT must be a literal frozenset")
        parsed = ast.literal_eval(value.args[0])
        if not isinstance(parsed, (set, dict)) or not all(isinstance(e, str) for e in parsed):
            raise ValueError("DEBT must contain only literal strings")
        return frozenset(parsed)
    raise ValueError("DEBT assignment not found")


def debt_at_merge_base(root: Path, base_ref: str) -> frozenset[str] | None:
    """Return ``DEBT`` at the merge base with ``base_ref``.

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
        ["git", "-C", str(root), "show", f"{base_commit}:{CHECKER_PATH}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        if "does not exist in" in result.stderr or "exists on disk, but not in" in result.stderr:
            return None
        raise ValueError(
            f"cannot read checker at merge base {base_commit}: {result.stderr.strip()}"
        )
    return debt_from_source(result.stdout)


def check_layers(
    sources: Mapping[str, str],
    debt: frozenset[str] = DEBT,
    base_debt: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the layer check; an empty list means it passes."""
    current = violations(sources)
    errors = [
        f"Import points outside the allowed layers: {entry}" for entry in sorted(current - debt)
    ]
    errors += [
        f"Repaired import still listed in DEBT; remove it: {entry}"
        for entry in sorted(debt - current)
    ]
    if base_debt is not None:
        errors += [
            f"Entry added to DEBT; this set may only shrink: {entry}"
            for entry in sorted(debt - base_debt)
        ]
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--base-ref",
        help="ref whose merge base with HEAD fixes the DEBT entries that may remain",
    )
    parser.add_argument(
        "--print-debt", action="store_true", help="print the current violations and exit"
    )
    args = parser.parse_args()
    root = args.root.resolve()

    sources = tracked_sources(root)
    if args.print_debt:
        for entry in sorted(violations(sources)):
            print(f'        "{entry}",')
        return 0

    base_debt: frozenset[str] | None = None
    if args.base_ref is not None:
        try:
            base_debt = debt_at_merge_base(root, args.base_ref)
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Import layer check failed::{error}")
            return 1

    errors = check_layers(sources, DEBT, base_debt)
    for message in errors:
        print(f"::error title=Import layer policy::{message}")
    if errors:
        print(
            "A lower layer must not import a higher one, and DEBT may only shrink. Move "
            "the shared declaration down to a layer both modules may import; see "
            "docs/many_body_circuit_architecture.md."
        )
        return 1
    print(f"Import layers respected ({len(DEBT)} recorded violations remain).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
