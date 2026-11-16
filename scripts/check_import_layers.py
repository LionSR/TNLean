#!/usr/bin/env python3
"""Reject imports that point upward between the lower layers of TNLean.

The layers below the tensor-network directories are listed in ``LAYERS``, from
the bottom up; ``ALLOWED`` says which layers each may import.  A module of
``TNLean`` outside these layers is not constrained here.  The architecture
they implement is described in ``docs/many_body_circuit_architecture.md``.

``DEBT`` is a ratchet.  It lists the imports that violated the rules when the
check was introduced.  A new violation fails, and so does an entry that no
longer violates a rule: remove it in the change that repairs the import.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

PRODUCTION_ROOT = "TNLean/"
ARCHIVE_ROOT = "TNLean/Archive/"
IMPORT_RE = re.compile(r"^import\s+(TNLean(?:\.[A-Za-z_][A-Za-z0-9_']*)+)\s*$", re.MULTILINE)

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
        "SiteEmbedding",
        "SiteEmbeddingNorm",
        "SiteEmbeddingOrder",
        "SiteExpectation",
        "SiteExpectationOrder",
        "SiteOscillation",
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
    "party": frozenset({"algebra", "sites"}),
}

# Existing violations only, as "importing module -> imported module".  Never add
# an entry: move the shared declaration down to the layer both sides may import.
DEBT: frozenset[str] = frozenset(
    {
        "TNLean.Circuit.ExpectationBounds -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.LiebRobinson.CommutatorRecursion -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SiteEmbedding -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SiteEmbeddingOrder -> TNLean.Circuit.Gates.Controlled",
        "TNLean.Circuit.SiteExpectationOrder -> TNLean.Circuit.LiebRobinson.CommutatorRecursion",
        "TNLean.Circuit.SiteOscillation -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SitePermutationSupport -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SitewiseTensorSupport -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SupportedFunctionalCalculus -> TNLean.Circuit.LocalCircuit",
        "TNLean.Circuit.SupportedGroundSpace -> TNLean.Circuit.Channel.Layer",
        "TNLean.Circuit.SupportedMatrixElements -> TNLean.Circuit.LocalCircuit",
        "TNLean.Lattice.GaussianZeroRange -> TNLean.Circuit.LocalCircuit",
        "TNLean.Lattice.LowEnergyCommutatorExample -> TNLean.Circuit.Gates.Controlled",
        "TNLean.Lattice.RegionalSwapSupport -> TNLean.Circuit.Gates.Permutation",
        "TNLean.Lattice.Sheet.Splitting -> TNLean.Lattice.RegionSplit",
        "TNLean.Lattice.Sheet.SwapCorrection -> TNLean.Lattice.RegionalSwap",
        "TNLean.Lattice.TreeBasisCounterexample.HardCoreNumber -> TNLean.Circuit.Gates.Controlled",
    }
)


def layer_of(module: str) -> str | None:
    """Return the layer that owns ``module``, or ``None`` if it is unconstrained."""
    for name, prefixes in LAYERS:
        for prefix in prefixes:
            if module == prefix or module.startswith(prefix + "."):
                return name
    return None


def is_import_only(source: str) -> bool:
    """Whether a file holds nothing but comments and import lines (an aggregator)."""
    body = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    lines = [line.strip() for line in body.splitlines()]
    return all(not line or line.startswith("--") or line.startswith("import ") for line in lines)


def violations(sources: dict[str, str]) -> set[str]:
    """Return every ``"A -> B"`` whose import points outside the allowed layers."""
    found: set[str] = set()
    for module, source in sources.items():
        layer = layer_of(module)
        if layer is None or is_import_only(source):
            continue
        for imported in IMPORT_RE.findall(source):
            target = layer_of(imported)
            if target is None:
                found.add(f"{module} -> {imported}")
            elif target != layer and target not in ALLOWED[layer]:
                found.add(f"{module} -> {imported}")
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--print-debt", action="store_true", help="print the current violations and exit"
    )
    args = parser.parse_args()

    current = violations(tracked_sources(args.root))
    if args.print_debt:
        for entry in sorted(current):
            print(f'        "{entry}",')
        return 0

    new = sorted(current - DEBT)
    stale = sorted(DEBT - current)
    for entry in new:
        print(f"::error::Import points outside the allowed layers: {entry}")
    for entry in stale:
        print(f"::error::Repaired import still listed in DEBT; remove it: {entry}")
    if new:
        print(
            "A lower layer must not import a higher one. Move the shared declaration "
            "down to a layer both modules may import; see "
            "docs/many_body_circuit_architecture.md."
        )
    if new or stale:
        return 1
    print(f"Import layers respected ({len(DEBT)} recorded violations remain).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
