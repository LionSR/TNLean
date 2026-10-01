# Cocycle group universes — 2026-09-30

Tracker: [#8315](https://github.com/LionSR/TNLean/issues/8315), step
[#8316](https://github.com/LionSR/TNLean/issues/8316).
Base commit: `fafa75e42af48847a029f222014ddf7d4ef360fe`.
Mathlib: v4.35.0-rc3.

## Scope

Mathlib's low-degree group cohomology requires the group and coefficient ring
in the same universe. Integer coefficients therefore require groups in `Type`.
Restrict the group arguments of scalar two- and three-cochains, L-symbols,
cohomology classes, projective representations, and their consumers to `Type`.
Restriction and pullback maps also require both groups in `Type`.

The original issue's estimate of 13 files predates later consumers. This change
covers the following 44 files, located by following cocycle/cochain uses and
reverse imports. Block-label types `X` retain their independent universes.
Tensor-only group families, permutation actions, on-site twists, and
G-injectivity definitions keep their existing universe polymorphism in the
modules that define them, and so do the tensor-level declarations built on
them: fusion and action data, reduction families, domain-wall actions and
strings, and the shift helpers of the cocycle MPO. Only declarations that take
a scalar cochain, an L-symbol, or a cohomology class (and their direct
consumers) sit in narrower sections with `G : Type`. The generic
`groupCohomology_π_eq_zero_iff` also retains the shared ring/group universe.
No definitions, theorem names, proofs, or blueprint declaration tags are removed.

- `TNLean/Algebra/CircleCohomology.lean`
- `TNLean/Algebra/CocycleCohomology.lean`
- `TNLean/Algebra/CocycleRestriction.lean`
- `TNLean/Algebra/GeneralizedCocycle.lean`
- `TNLean/Algebra/GeneralizedCocycleInversion.lean`
- `TNLean/Algebra/LSymbol.lean`
- `TNLean/Algebra/LSymbolBlockIndependence.lean`
- `TNLean/Algebra/LSymbolDomainWall.lean`
- `TNLean/Algebra/PositiveGeneralizedCocycle.lean`
- `TNLean/Algebra/ProjectiveCommutantEigenspace.lean`
- `TNLean/Algebra/ProjectiveRepresentation.lean`
- `TNLean/Algebra/RestrictedScalarGauge.lean`
- `TNLean/Algebra/ScalarThreeCocycle.lean`
- `TNLean/Algebra/ScalarThreeCocycleCyclicDomainWall.lean`
- `TNLean/Algebra/ScalarThreeCocycleCyclicInvariant.lean`
- `TNLean/Algebra/ScalarThreeCocycleCyclicTwo.lean`
- `TNLean/Algebra/ScalarThreeCocycleInversion.lean`
- `TNLean/Algebra/ScalarThreeCocycleTimeReversal.lean`
- `TNLean/Algebra/StabilizerCocycleExtension.lean`
- `TNLean/Algebra/StabilizerCocycleLSymbol.lean`
- `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- `TNLean/Algebra/TwistedRegularRepresentation.lean`
- `TNLean/MPS/Examples/GHZGInjective.lean`
- `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- `TNLean/MPS/MPU/GroupCocycleMPO/FusionAlgebra.lean`
- `TNLean/MPS/MPU/GroupCocycleMPO/FusionTensors.lean`
- `TNLean/MPS/MPU/ReductionCommonBlocking.lean`
- `TNLean/MPS/Periodic/ProjectiveRep.lean`
- `TNLean/MPS/Symmetry/CocycleCoboundary.lean`
- `TNLean/MPS/Symmetry/EntanglementSpectrum.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/AnomalyObstruction.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/AssociatorComap.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/AssociatorToolkit.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/DomainWall.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallExchange.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallFamily.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallString.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/GroupFusion.lean`
- `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- `TNLean/MPS/Symmetry/SPTFixedPoint.lean`
- `TNLean/MPS/Symmetry/StringOrder.lean`
- `TNLean/MPS/Symmetry/VirtualRepresentation.lean`

## Verification

The pinned prebuilt Mathlib cache was fetched before any library build.
The reverse import closure contains 87 non-aggregator modules, covered by 31
leaf targets. All 31 targets built successfully with the package's Lean options
and linters (9,662 jobs, including cached Mathlib artifacts and prerequisites).
Generated aggregators are omitted from that closure because they import
unrelated modules as well. `git diff --check` passed. Existing dependency
deprecation warnings do not affect the result.

## Remaining tracker work

This change implements only step 0. Steps 1–8 remain separate migrations;
step 9's recurring audit convention is already in `docs/project_conventions.md`.
The tracker's 17 listed overlapping PRs are no longer open as of this audit.
Existing on-site permutation actions, unitary averaging through
`Representation.averageMap`, induced unitary operator representations, and
`StarSubalgebra.isSemisimpleModule` already cover parts of step 8.

Step 7's requested `comul : A →ₐ[R] A ⊗[R] A` is inconsistent with its stated
non-unital coproduct: `AlgHom.map_one` requires `comul 1 = 1`, whereas
`CompleteZipperFusionFamily.coproduct_one` gives a support projector. A
multiplicative linear map permits the stated mathematics and admits ordinary
Mathlib bialgebras as instances. The tensor-product transport can use
`Algebra.TensorProduct.piRight`, tensor-product commutation, and
`Matrix.kroneckerAlgEquiv` (which combines `kroneckerTMulAlgEquiv` with the
coefficient tensor-product equivalence).
