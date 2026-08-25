#!/usr/bin/env python3
"""Reject new unattributed Lean declarations with no textual consumer or citation.

The check is intentionally conservative.  It extracts ordinary named
declarations from handwritten production modules and counts exact identifier
tokens across production Lean, Blueprint, and repository documentation.  A
declaration is a candidate only when its name occurs exactly once: on its own
declaration line.  Attributed declarations are excluded because simplification,
automation, deprecation, and other attributes can consume a declaration without
naming it.  Name collisions, generated declarations, instances, and
declarations mentioned in prose are likewise left alone.

``DEAD_DECLARATION_ALLOWLIST`` is a ratchet.  The existing reviewed candidates
may remain while they are triaged, but the set may only shrink relative to the
pull-request merge base.  An entry must be removed when the declaration is
deleted or acquires a real occurrence elsewhere.
"""

from __future__ import annotations

import argparse
import ast
import re
import subprocess
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

from generate_import_aggregators import is_generated
from lean_import_syntax import strip_lean_comments


PRODUCTION_ROOT = "TNLean/"
ARCHIVE_ROOT = "TNLean/Archive/"
CHECKER_PATH = "scripts/check_dead_lean_declarations.py"

# Entries have the stable form ``repository/path.lean::declaration``.  Never
# add a new entry: cite or consume the declaration, or remove it.  Existing
# entries are mechanically checked and must disappear from this set as they
# are retired.
DEAD_DECLARATION_ALLOWLIST: frozenset[str] = frozenset(
    {
        "TNLean/Algebra/MatrixStabilization.lean::projector_idempotent",
        "TNLean/Algebra/ScalarPowerSumIdentity.lean::sum_pow_eq_implies_charpoly_diagonal_eq",
        "TNLean/MPS/CanonicalForm/Definitions.lean::isCPSVCanonicalFormII",
        "TNLean/MPS/Chain/CyclicBlockAverage.lean::cyclicRotation_eq_iterate_cyclicShift",
        "TNLean/MPS/FundamentalTheorem/SectorBNT/Examples.lean::halvedDecomp_weight_unit_per_block",
        "TNLean/MPS/FundamentalTheorem/SectorBNT/Examples.lean::signFlipDecomp_weight_unit_per_block",
        "TNLean/MPS/MPDO/BNTPhysicalSectorGSNNCH.lean::hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization_of_commonWeight",
        "TNLean/MPS/MPDO/BiCFDerivation/BNTDirectSum.lean::exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors",
        "TNLean/MPS/MPDO/BiCFDerivation/BNTDirectSum.lean::exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1",
        "TNLean/MPS/MPDO/BiCFDerivation/BNTDirectSum.lean::propBlockInjective_of_blocksNotGaugePhaseEquiv_directSum_c1",
        "TNLean/MPS/MPDO/CommutingBondEtaCyclicCore.lean::reindex_product_embedLocalOperator_two_of_etaPair_decomposition",
        "TNLean/MPS/MPDO/CyclicActiveCutCoordinates.lean::cyclicActiveSeparatedBoundary_eq_right_kronecker_left",
        "TNLean/MPS/MPDO/CyclicActiveCutCoordinates.lean::leftSectorOpenEdgeEquiv_symm_fiber_heq",
        "TNLean/MPS/MPDO/CyclicActiveCutCoordinates.lean::rightSectorOpenEdgeEquiv_symm_fiber_heq",
        "TNLean/MPS/MPDO/GSNNCHFourCycleMarkov/OverlappingLiftAlgebra.lean::rightOverlappingLift_smul",
        "TNLean/MPS/MPDO/InvariantProjection.lean::blockwise_braRight_eq_ketLeftBraRight_of_invariant",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::left_factor_injective",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::right_factor_injective",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::traceMatrix_not_idempotent",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::traceMatrix_rank_ge_two_minor",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::traceMatrix_row_sum",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean::traceMatrix_sq_eq_cube",
        "TNLean/MPS/MPDO/NonCartesianActiveSectorObstruction.lean::sectorCount_eq_four",
        "TNLean/MPS/MPDO/PhysicalSectorActiveNeighboring.lean::neighboringOperator_eq_congruence",
        "TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean::oneLabelChiScaled_posEntries",
        "TNLean/MPS/MPDO/TopologicalGibbsHamiltonian.lean::singleKrausMap_gibbsDecomposition_eq_mpo",
        "TNLean/MPS/MPU/MPUCanonicalForm.lean::toIsMPUCanonicalForm",
        "TNLean/MPS/MPU/PhysicalAncilla.lean::physicalSlice_tensorPhysicalId",
        "TNLean/MPS/Overlap/Basic.lean::mpvInner_eq_sum_of_decomp_right",
        "TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean::ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1",
        "TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean::ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07",
        "TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalChain.lean::chainGroundSpace_toTensorFromBlocks_two_inclusions_and_iSupIndep_of_bnt_unital",
        "TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean::pgvwc07_directSum_restriction_intersection_of_ge_of_bnt_directSum_unital",
        "TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean::pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_unital",
        "TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean::pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors",
        "TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean::spectralGap_of_martingale_anticommutator_rowCol",
        "TNLean/MPS/ParentHamiltonian/RestrictTransport.lean::reindexSites_trans",
        "TNLean/MPS/Periodic/CornerTransition.lean::cornerProd_single",
        "TNLean/MPS/Periodic/Defs.lean::BasisOfPeriodicTensors",
        "TNLean/MPS/Periodic/Defs.lean::toChain",
        "TNLean/MPS/Periodic/NormalCanonicalPeriodOne.lean::toIsIrreducibleFormOfWeightPos_period_eq_one",
        "TNLean/MPS/Periodic/Overlap/GaugePhase.lean::gaugePhaseEquiv_to_repeatedBlocks_of_leftCanonical_irreducible",
        "TNLean/MPS/Periodic/Overlap/SectorMatch/CyclicTrace.lean::piTensorProduct_eq_smul_of_cyclic_products",
        "TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean::sectorFixedPointAlgebraRigidity_of_irreducible_tp",
        "TNLean/PEPS/CycleArcRegion.lean::not_add_one_eq_and_add_one_eq",
        "TNLean/PEPS/CycleMPSFundamentalTheorem.lean::cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge",
        "TNLean/PEPS/CycleMPSFundamentalTheorem.lean::pos_d_of_isNBlkInjective",
        "TNLean/PEPS/InsertionRealization.lean::edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eqAt",
        "TNLean/PEPS/NormalEdgeBlockingInterior.lean::normalSquareEdgeBlockingHypotheses_of_interiorData_endpoint_disjoint_cover",
        "TNLean/PEPS/NormalEdgeBlockingInterior.lean::normalSquareEdgeBlockingHypotheses_of_interiorData_injective_chain",
        "TNLean/PEPS/NormalEdgeGauge.lean::isTwoBlockInjective_blueTwoBlock",
        "TNLean/PEPS/NormalEdgeGauge.lean::isTwoBlockInjective_redTwoBlock",
        "TNLean/PEPS/NormalEdgeGauge.lean::isTwoBlockInjective_regionTwoBlock_of_isVertexInjective",
        "TNLean/PEPS/NormalEdgeSingleCrossing.lean::isCrossingEdge_horizontalTranslatedEdge_blockingDatum_interior",
        "TNLean/PEPS/NormalEdgeSingleCrossing.lean::isCrossingEdge_verticalTranslatedEdge_blockingDatum_interior",
        "TNLean/PEPS/NormalSquareInjectivity.lean::normalSquareBlockingRegions_of_overlap",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite6.lean::of_tripleAgrees",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean::agreeOffEdge_overrideEdge",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean::overrideEdge_coarse_bc",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean::overrideEdge_coarse_rc",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite9.lean::sameAwayFromRBBundle_iff_redHostAgrees",
        "TNLean/PEPS/RegionBlock/GaugeBridgeExpansion.lean::regionInsertedCoeff_applyGauge_eq_innerOuterSum",
        "TNLean/PEPS/RegionBlock/GaugeInjectivity2.lean::regionBoundaryGaugeInv_mul",
        "TNLean/PEPS/RegionBlock/InsertResidual.lean::insertOuterBondProd_congr",
        "TNLean/PEPS/RegionBlock/Realization.lean::regionInsertionOp_add",
        "TNLean/PEPS/RegionBlock/Realization.lean::regionInsertionOp_smul",
        "TNLean/PEPS/RegionBlock/Recovery3.lean::regionInsertedCoeff_eq_of_realizes",
        "TNLean/PEPS/RegionBlock/ThreeBlockReconcile.lean::threeBlock_blue_readoff",
        "TNLean/PEPS/RegionBlock/ThreeBlockReconcile.lean::threeBlock_reconcile",
        "TNLean/PEPS/RegionBlock/ThreeBlockResonate2.lean::regionBlockedWeight_threeBlockBluePhysical_mem_range",
        "TNLean/PEPS/RegionBlock/UnionClosure.lean::regionBlockedTensorInjective_union_of_isVertexInjective",
        "TNLean/PEPS/RegionTransport.lean::Region_map_mono",
        "TNLean/PEPS/TorusCovariantAbsorbedFamily.lean::glReindex_transportedAbsorbedGauge_eq",
        "TNLean/PEPS/TorusDeformedWindow.lean::verticalUnion_insert_eq_of_deformedState_eq",
        "TNLean/PEPS/TorusReferenceBlockingData.lean::isCrossingEdge_torusHorizontalReferenceBlockingDatum",
        "TNLean/PEPS/TorusReferenceBlockingData.lean::isCrossingEdge_torusVerticalReferenceBlockingDatum",
        "TNLean/PEPS/TorusWindowChain2.lean::deformedRegionStateAssembled_eq_of_curried_eq",
        "TNLean/PEPS/TorusWindowChain2.lean::nestedThreeBlockGeometry_sdiff_red",
        "TNLean/PEPS/TorusWindowChain5.lean::extendInsert_zero",
        "TNLean/PEPS/TorusWindowChain6.lean::horizontalStaircaseEndPair_subset_patch",
        "TNLean/PEPS/TorusWindowComplement.lean::toWindowHypotheses",
        "TNLean/PEPS/TorusWindowFamily.lean::staircaseWindow_injective",
        "TNLean/PEPS/TorusWindowSingleCrossingObstruction.lean::horizontalStaircasePair_complement_band_lt_window",
        "TNLean/PEPS/TorusWindowSingleCrossingObstruction.lean::horizontalStaircasePair_window_meets_row",
        "TNLean/PEPS/TorusWitnessTransport.lean::bondDim_boundaryEdgeMap_translate_eq",
        "TNLean/PEPS/VertexComplement/Basic.lean::complementVertex_ne",
    }
)

DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|inductive|opaque|alias)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)
IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
TEXT_ROOTS: tuple[str, ...] = ("TNLean", "blueprint", "docs")
TEXT_SUFFIXES: frozenset[str] = frozenset({".lean", ".tex", ".md", ".txt"})


def _git_paths(root: Path, pathspecs: Iterable[str]) -> list[Path]:
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
            *pathspecs,
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    return sorted(
        resolved
        for path in result.stdout.decode("utf-8").split("\0")
        if path and (resolved := root / path).is_file()
    )


def _production_sources(root: Path) -> list[Path]:
    source_root = root / "TNLean"
    return [
        path
        for path in _git_paths(root, ("TNLean",))
        if path.suffix == ".lean"
        and path.relative_to(root).as_posix().startswith(PRODUCTION_ROOT)
        and not path.relative_to(root).as_posix().startswith(ARCHIVE_ROOT)
        and not is_generated(path, source_root)
    ]


def _unattributed_declared_names(source: str) -> list[str]:
    """Extract declarations not governed by a preceding or inline attribute.

    Lean attributes may occur on their own line, span several lines, or share
    a line with the declaration.  The scanner deliberately excludes the whole
    attributed declaration instead of guessing whether its name is needed by
    the registered behavior.
    """
    names: list[str] = []
    pending_attribute = False
    inside_attribute = False
    for line in source.splitlines():
        remainder = line
        if inside_attribute:
            if "]" not in remainder:
                continue
            remainder = remainder.split("]", 1)[1]
            inside_attribute = False

        while remainder.lstrip().startswith("@["):
            pending_attribute = True
            remainder = remainder.lstrip()[2:]
            if "]" not in remainder:
                inside_attribute = True
                remainder = ""
                break
            remainder = remainder.split("]", 1)[1]

        if inside_attribute or not remainder.strip():
            continue

        match = DECLARATION_RE.match(remainder)
        if match is not None:
            if not pending_attribute:
                names.append(match.group(1).rsplit(".", 1)[-1])
            pending_attribute = False
            continue

        pending_attribute = False
    return names


def _text_corpus(root: Path) -> list[Path]:
    return [
        path
        for path in _git_paths(root, TEXT_ROOTS)
        if path.suffix in TEXT_SUFFIXES
        and not path.relative_to(root).as_posix().startswith(ARCHIVE_ROOT)
    ]


def find_dead_declarations(root: Path) -> set[str]:
    """Return current single-occurrence declaration keys."""
    declarations: list[tuple[str, str]] = []
    for path in _production_sources(root):
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        uncommented, error = strip_lean_comments(source)
        if error is not None:
            continue
        relative = path.relative_to(root).as_posix()
        declarations.extend(
            (relative, name) for name in _unattributed_declared_names(uncommented)
        )

    relevant_names = {name for _, name in declarations}
    counts: Counter[str] = Counter()
    for path in _text_corpus(root):
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        counts.update(token for token in IDENTIFIER_RE.findall(source) if token in relevant_names)

    return {
        f"{path}::{name}"
        for path, name in declarations
        if counts[name] == 1
    }


def _allowlist_from_source(source: str) -> frozenset[str]:
    """Read ``DEAD_DECLARATION_ALLOWLIST`` from one source revision."""
    tree = ast.parse(source)
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(
            isinstance(target, ast.Name) and target.id == "DEAD_DECLARATION_ALLOWLIST"
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
            raise ValueError("DEAD_DECLARATION_ALLOWLIST must be a literal frozenset")
        if not value.args:
            return frozenset()
        parsed = ast.literal_eval(value.args[0])
        if not isinstance(parsed, set) or not all(isinstance(item, str) for item in parsed):
            raise ValueError("DEAD_DECLARATION_ALLOWLIST must contain only literal strings")
        return frozenset(parsed)
    raise ValueError("DEAD_DECLARATION_ALLOWLIST assignment not found")


def _allowlist_at_merge_base(root: Path, base_ref: str) -> frozenset[str] | None:
    """Return the single-occurrence baseline at the merge base with ``base_ref``."""
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


def check_dead_declarations(
    root: Path,
    allowlist: frozenset[str] = DEAD_DECLARATION_ALLOWLIST,
    base_allowlist: frozenset[str] | None = None,
) -> int:
    """Check the dead-declaration ratchet and return a process exit status."""
    try:
        current = find_dead_declarations(root)
    except (subprocess.CalledProcessError, UnicodeDecodeError) as error:
        print(f"::error title=Dead Lean declaration check failed::{error}")
        return 1

    errors: list[str] = []
    if base_allowlist is not None:
        for item in sorted(allowlist - base_allowlist):
            errors.append(
                f"{item}: added to the dead-declaration allowlist; this set may only shrink"
            )
    for item in sorted(allowlist - current):
        errors.append(
            f"{item}: stale dead-declaration allowlist entry; remove it now that the "
            "declaration is deleted or referenced"
        )
    for item in sorted(current - allowlist):
        errors.append(
            f"{item}: new named declaration has no second textual occurrence"
        )

    for message in errors:
        key = message.split(": ", 1)[0]
        path, _, declaration = key.partition("::")
        title = f"Dead Lean declaration ratchet ({declaration})"
        print(f"::error file={path},title={title}::{message}")

    print(
        f"Checked named production declarations: {len(current)} current "
        f"single-occurrence candidate(s), {len(allowlist)} allowlisted, "
        f"{len(current - allowlist)} new."
    )
    return 1 if errors else 0


def _print_literal(items: Iterable[str]) -> None:
    for item in sorted(items):
        print(f'        "{item}",')


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject new unattributed Lean declarations without a textual consumer."
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
        _print_literal(find_dead_declarations(root))
        return 0

    base_allowlist: frozenset[str] | None = None
    if args.base_ref is not None:
        try:
            base_allowlist = _allowlist_at_merge_base(root, args.base_ref)
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Dead Lean declaration check failed::{error}")
            return 1
        if base_allowlist is None:
            print(
                "Initializing the dead-declaration debt baseline: the checker is absent "
                f"from {args.base_ref}."
            )
    return check_dead_declarations(root, base_allowlist=base_allowlist)


if __name__ == "__main__":
    raise SystemExit(main())
