# Mathlib 4.35 replacement audit

Date: 2026-09-25.

This audit records Mathlib material that became available between Mathlib
`v4.34.0-rc1` and `v4.35.0-rc3`. It identifies local TNLean infrastructure that
the new material replaces or shortens, records the API changes that the upgrade
had to absorb, and lists new APIs that do not replace project-specific
mathematics.

## Reason for the upgrade

The Lake executable shipped with Lean `v4.34.0-rc1` traps on exit under
macOS 27 (`malloc: pointer being freed was not allocated`, raised from thread
cleanup), so every `lake` command on that platform failed, including
`lake --version`. The upstream report is leanprover/lean4#15087; the allocator
fix first appears in the `v4.34.0` release line. Lake from `v4.35.0-rc1` and
later exits cleanly on macOS 27.

## Dependency pins and comparison range

- Lean: `leanprover/lean4:v4.35.0-rc3`;
- Mathlib: `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`;
- QICLean: `af43b1c6f147a4a717583c9e6f4049a1306ea34e`, its own upgrade to
  `v4.35.0-rc3` with a matching replacement audit (LionSR/QICLean#546);
- Gametheory: unchanged at `ec93e4daed4ad8b4784a9d760e492832e7711433`. That
  commit is three commits ahead of the Brouwer default branch, so no newer
  revision exists to adopt.

The comparison baseline is Mathlib `v4.34.0-rc1`, commit
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. The range contains 1,207 non-merge
commits and includes the `v4.34.0` release.

The audit split the Mathlib tree into three slices: linear algebra, abstract
algebra, and matrices; analysis, topology, and dynamics; and data, order,
logic, combinatorics, and tactics. For each slice it listed the added
declarations, separated genuinely new names from moved ones by checking the
baseline tree, and matched the new names against TNLean and QICLean by name and
by statement shape. A candidate was accepted only when the Mathlib statement
implies the local one under the same or weaker hypotheses.

## Summary

The range contains no module-level or declaration-level replacement for
TNLean. It contains two proof-level simplifications. The one
declaration-level replacement in the range, `Matrix.col_mul`, belongs to
QICLean and is recorded in QICLean's audit.

1. `Fin.isEmpty_iff` replaces local constructions of `IsEmpty (Fin k)` from
   `k = 0`.
2. `tendsto_nhds_unique_of_forall` removes intermediate `congr'` limits.

## Empty finite index types

Mathlib commit `17019dcaaa`, `feat(Basic/IsEmpty/Defs): add Fin.isEmpty_iff
(#43763)`, adds

```lean
@[simp, grind =] lemma Fin.isEmpty_iff {k : ℕ} : IsEmpty (Fin k) ↔ k = 0
```

in `Mathlib.Basic.IsEmpty.Defs`. Five local constructions of an empty-type
instance from a vanishing dimension now apply this equivalence directly, in
`MPS/MPU/TransferMultiplicity`, `MPS/CanonicalForm/NormalReduction/WeightNormalization`,
`MPS/MPDO/BNTAlgebraTensorClauseSpectrum`, and `MPS/MPU/CanonicalForm`.

## Uniqueness of limits of pointwise equal sequences

Mathlib commit `f86d48590e`, `feat(Topology/Separation/Hausdorff): add
tendsto_nhds_unique_of_forall`, adds

```lean
theorem tendsto_nhds_unique_of_forall {f g : α → X} {a b : X}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : ∀ y, f y = g y) : a = b
```

It replaces the two `congr'` intermediates in `MPS/RFP/PhaseOscillation`. The
remaining `tendsto_nhds_unique` sites in `MPS/SharedInfra/GaugePhase` and
`MPS/BNT/PermutationRigidityPrimitive` compare limits after a norm or `simpa`
step rather than pointwise equality and are unchanged.

## API changes absorbed by the upgrade

The first build under `v4.35.0-rc3` failed in twelve TNLean modules. The
failures were API and elaboration changes, not mathematical regressions. Each
repair keeps the theorem statement.

- `TFAE.out` is now 1-indexed. Eleven calls `.out i j` in six `MPS/MPU`
  modules became `.out (i + 1) (j + 1)`.
- The tensor-product induction principle `TensorProduct.inductionOn` no longer
  has a zero case (the old `induction_on` is deprecated), so three `zero`
  branches were deleted in `Algebra/CommutingStarSubalgebraProduct`. The same
  module now names the ring-hom source and target when it applies
  `RingHom.injective` from a simple ring, because the tensor-product semiring
  path no longer unifies with `NonAssocRing.toNonAssocSemiring` by itself.
- `spectralRadius` is now defined as a supremum over the quasispectrum.
  `MPS/Symmetry/StringOrder` rewrites with `spectralRadius_eq_of_unital` to
  recover the supremum over the spectrum.
- `LinearMap.nonneg_iff_isPositive` and `LinearMap.le_def` take their operators
  implicitly (`MPS/ParentHamiltonian/Martingale/OpenHamiltonian`,
  `MPS/ParentHamiltonian/Martingale/OpenParentGap`).
- Instance search for `HasSummableGeomSeries` on operators of a Euclidean space
  now times out. `MPS/ParentHamiltonian/GramInverseConvergence` supplies the
  instance locally from completeness of the finite-dimensional operator space.
- Several `simp` and `rw` steps no longer see through the instances of
  `Multiplicative (ZMod n)` and its products. In `MPS/MPU/GroupCocycleMPO/Instances`,
  `MPS/MPDO/CZXGaussInvariantSubspace`, and `MPS/Examples/GHZClusterAction` the
  lemmas are now applied with `exact` or `Finset.prod_congr`, which unify at
  default transparency.
- `norm_num` now closes one goal in `MPS/MPDO/PositiveMinimalRealizationCounterexample`
  that previously needed a trailing `simp`.

## Renamed APIs and warning cleanup

Mathlib moved `Mathlib.Data.Complex.Basic`, `Mathlib.Data.Complex.BigOperators`,
and `Mathlib.Data.Real.Basic` under `Mathlib.Basic`; TNLean imports the new
paths directly. It also uses the current names

```lean
MonoidHom.coe_coe → MonoidHom.coe_ofClass
SetLike.le_def    → IsConcreteLE.le_iff
```

`isCoatomic_of_orderTop_gt_wellFounded` is deprecated. `MPS/FundamentalTheorem/Reduction/Flag`
no longer builds the coatomic structure by hand: Mathlib derives `IsCoatomic` for the
submodules of a Noetherian module, so the proof applies `eq_top_or_exists_le_coatom`
directly.

The module-docstring linter now requires the module docstring to be the first
command after the imports; thirteen modules that opened namespaces or scopes
before their docstring were reordered, and two modules without a docstring
received one. Tactics that now close goals earlier were removed where the
unused-tactic linter reported them. The long-line warnings that remain predate
the upgrade.

## New APIs that do not replace TNLean mathematics

- The `norm_matmul` simproc (`Mathlib.Tactic.NormMatMul`) multiplies explicit
  matrix literals. About 170 TNLean proofs expand products entrywise with
  `Matrix.mul_apply` and `Fin.sum_univ_two`, mostly in `MPS/Examples`, but they
  multiply named matrices rather than literals, and the simproc's interaction
  with `vecCons` simp lemmas is untested here. It is a candidate for a separate
  trial on one example module, not an upgrade replacement.
- `Finset.equivOfEq` would replace one term in `PEPS/RegionBlock/Basic` without
  saving lines.
- `isOpen_setOfPred_isInvertible` and `IsInvertible.eventually_nhds` are
  qualitative and do not give the quantitative inverse bound of
  `MPS/ParentHamiltonian/GramInverseConvergence`.
- The new positive-definite `mulVec` injectivity lemmas, the positivity API for
  continuous functionals on a C*-algebra, `Matrix.spectrum_transpose`,
  `Matrix.IsIndecomposable`, and `Representation.stabilizer` have no TNLean
  counterpart; TNLean's irreducibility notions and stabilizers concern family
  actions and group actions on sets.

## Validation

`scripts/lake_build_locked.sh` completes the full build on `v4.35.0-rc3`
(10,969 jobs). The only TNLean warnings are 17 long-line warnings in the
Kramers--Wannier, parity-graded, and PEPS region-block modules, all present
before the upgrade.
