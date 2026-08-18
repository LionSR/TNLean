# Mathlib 4.34 replacement audit

Date: 2026-08-17.

This audit records Mathlib material that became available between Mathlib 4.32
and the 4.34 release line. It identifies local TNLean infrastructure that can
be removed, smaller proofs that can use new standard declarations, and related
new APIs that do not replace project-specific mathematics.

## Dependency pins and comparison range

The public repositories exposed the following 4.34 tag when the upgrade was
performed:

- Lean: `leanprover/lean4:v4.34.0-rc1`;
- Mathlib: `v4.34.0-rc1`;
- Mathlib commit: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`;
- Gametheory compatibility commit:
  `ec93e4daed4ad8b4784a9d760e492832e7711433`.

There was no final `v4.34.0` tag. The comparison baseline is Mathlib
`v4.32.0`, commit `81a5d257c8e410db227a6665ed08f64fea08e997`.
The range `v4.32.0..v4.34.0-rc1` contains 505 non-merge commits and 4,480
changed paths. It includes the 4.33 release.

The audit inspected feature commits and changed declarations, searched the
Mathlib source by name and type, and compared the resulting APIs with TNLean
declarations and use sites. Mechanical module-system changes and unrelated
subject areas were excluded after the initial inventory.

## Summary

The range contains one module-level replacement, several declaration-level
replacements, and multiple proof-level simplifications.

1. Mathlib now proves that the positive-semidefinite cone of square `RCLike`
   matrices is closed and supplies the corresponding scoped
   `OrderClosedTopology` instance. This replaces TNLean's local Loewner-order
   topology development.
2. Mathlib now supplies the `CStarAlgebra` instance for finite complex matrices
   in the L2 operator norm. This replaces TNLean's local bundled instance and
   all local instance aliases at its use sites.
3. Mathlib now proves rank invariance under multiplication by a non-zero-divisor.
   This replaces TNLean's field-specialized `Matrix.rank_smul_of_ne_zero`.
4. Mathlib's existing nondegenerate-matrix API replaces the local
   `linearIndependent_sum_smul` pass-through lemma and its 46-line proof.
5. Mathlib's Gram-matrix characterization replaces three local coordinate
   proofs for orthonormal matrix columns.
6. Continuous-linear-map rank openness replaces the determinant-minor support
   stack for matrix rank closedness.
7. `Finset.equivMap` replaces local site-translation and graph-region image
   equivalence constructors.

New determinant and limit lemmas also remove local proof plumbing:

- determinant nonvanishing now gives `mulVec` injectivity directly;
- determinant nonvanishing now preserves matrix rank under multiplication;
- scalar limits to zero or one act on constants directly;
- a quotient tending to one can be characterized from the limits of its
  numerator and denominator.

No other sound deletion-scale replacement was found. In particular, the new
convex-hull, rank-closedness, resolvent, direct-sum, echelon-form, and
tensor-product APIs do not subsume the corresponding TNLean mathematics
described below.

## Closedness of the positive-semidefinite cone

Mathlib commit:

- `c92631ba4b8bf02ff7be7ed128d9dbdebc232d64`,
  `feat(Matrix/Order): OrderClosedTopology instance for square RCLike matrices`.

Import:

```lean
import Mathlib.Analysis.Matrix.Order
```

Declarations:

```lean
Matrix.posSemidef_is_closed
Matrix.instOrderClosedTopology
```

The first theorem proves

```lean
IsClosed {A : Matrix n n 𝕜 | A.PosSemidef}
```

for any `RCLike 𝕜`. The second declaration is registered as an instance in the
`MatrixOrder` scope. Together with the general theorem `isClosed_le_prod`, they
replace all mathematical declarations in
`TNLean/Analysis/MatrixOrderTopology.lean`:

- the private continuity lemma for quadratic forms;
- `matrix_isClosed_posSemidef`;
- `matrix_isClosed_le`;
- `matrixOrderClosedTopology`.

The upstream result is more general because it works over every `RCLike` scalar
field and does not expose TNLean's conversion from `Finite` to `Fintype`.

Direct TNLean consumers of the local PSD-closedness theorem were:

- `TNLean/Channel/Semigroup/CPClosure.lean`;
- `TNLean/Channel/Semigroup/LindbladForm/EulerStep.lean`;
- `TNLean/Channel/Schwarz/TwoPositive.lean`.

They can use `Matrix.posSemidef_is_closed` directly.

`TNLean/Channel/Basic.lean` also defined the finite-index wrapper
`isClosed_posSemidef`. Its direct consumers were:

- the compactness proof for density matrices in `Channel/Basic.lean`;
- `Channel/FixedPoint/MeanErgodicProjection.lean`;
- `Channel/Irreducible/Growth/Exponential.lean`;
- `Channel/Peripheral/CesaroRecurrence.lean`.

The wrapper adds no project vocabulary and is removed. These consumers also use
`Matrix.posSemidef_is_closed` directly.

Status: exact upstream replacement.

## Matrix C-star algebra in the L2 operator norm

Mathlib commit:

- `bcaf924143a7c24b55a6ce214d4c327670de8f4c`,
  `feat(Analysis/CStarAlgebra/Matrix): add CStarAlgebra instance for matrices`.

Import:

```lean
import Mathlib.Analysis.CStarAlgebra.Matrix
```

Declaration:

```lean
Matrix.instCStarAlgebra
```

The instance is registered in the `Matrix.Norms.L2Operator` scope. It is built
from the same structures used by TNLean's `Matrix.matrixCStarAlgebra`:

```lean
Matrix.instL2OpNormedRing
Matrix.instL2OpNormedAlgebra
Matrix.instCStarRing
```

It therefore exactly replaces that local definition. A second-pass audit found
that local aliases and nested `let` bindings for the upstream instance were
still acting as pass-through layers. All such bindings are removed. Each file
now opens `Matrix.Norms.L2Operator` only in the section that needs the canonical
matrix norm and C-star structures.

The replacement applies to the explicit users in:

- `TNLean/Analysis/LiebOperatorIntegral.lean`;
- `TNLean/Channel/OperatorSystemExtension.lean`;
- `TNLean/Channel/Peripheral/UnitalKraus.lean`;
- `TNLean/Channel/Schwarz/PositiveMapProperties.lean`.

It also replaces hand-built finite-matrix `CStarAlgebra` instances in:

- `TNLean/Axioms/OperatorConvexity.lean`;
- `TNLean/Axioms/LiebSubBoundary.lean`;
- `TNLean/Analysis/CfcConjugation.lean`;
- `TNLean/Analysis/MatrixSqrt.lean`;
- `TNLean/Analysis/SandwichedRenyi.lean`;
- `TNLean/Analysis/SandwichedRenyiTwo.lean`;
- `TNLean/Channel/Schwarz/AndoLieb.lean`;
- `TNLean/Channel/Schwarz/RelativeEntropyConvexity.lean`;
- `TNLean/Channel/Schwarz/SchwarzSubnormal.lean`.

The similarly named instance in `TNLean/Analysis/CStarCompletion.lean` is not a
replacement target. It is an instance on `Completion A`, not on ordinary
matrices.

Status: exact upstream replacement.

## Determinant nonvanishing and `mulVec` injectivity

Import:

```lean
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
```

Declaration:

```lean
Matrix.mulVec_injective_of_det_ne_zero
```

`TNLean/MPS/CanonicalForm/NormalCommutant.lean` previously converted
`X.det ≠ 0` and `Y.det ≠ 0` to unit determinants, then converted those witnesses
to injectivity of `X.mulVec` and `Y.mulVec`. The new theorem gives the required
injectivity directly. The surrounding Gram-rigidity theorem remains local.

Status: exact proof-plumbing simplification.

## Determinant nonvanishing and rank preservation

Import:

```lean
import Mathlib.LinearAlgebra.Matrix.Rank
```

Relevant declarations:

```lean
Matrix.rank_of_det_ne_zero
Matrix.rank_mul_eq_left_of_det_ne_zero
Matrix.rank_mul_eq_right_of_det_ne_zero
```

`TNLean/Channel/FixedPoint/MaximalRank.lean` previously proved that a scalar
diagonal determinant was a unit solely to invoke
`Matrix.rank_mul_eq_right_of_isUnit_det`. It can instead prove determinant
nonvanishing and apply `Matrix.rank_mul_eq_right_of_det_ne_zero`.

The corresponding `IsUnit` APIs remain preferable where unitarity already
provides an `IsUnit` witness, such as `SingleKrausPositivity.lean` and
`VirtualSandwich.lean`.

Status: local proof simplification, not a theorem replacement.

## Rank under scalar multiplication

Mathlib commit:

- `3b3cdbb692`, `feat(LinearAlgebra/Matrix/Rank): rank under scalar
  multiplication by a non-zero-divisor`.

Import and declaration:

```lean
import Mathlib.LinearAlgebra.Matrix.Rank

Matrix.rank_smul_of_mem_nonZeroDivisors
```

This theorem works over a commutative ring and strictly generalizes TNLean's
field-specialized `Matrix.rank_smul_of_ne_zero`. The local theorem is deleted.
Its six consumers now invoke the Mathlib theorem directly with
`mem_nonZeroDivisors_of_ne_zero`. Five consumers also drop their import of
`TNLean.Algebra.MatrixRankBaseChange`; `DiagonalCutRank.lean` retains that import
for the still-local scalar-extension theorem `Matrix.rank_map_algebraMap`.

Status: exact declaration replacement and pass-through deletion.

## Linear independence under a nondegenerate coefficient matrix

Import and declaration:

```lean
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

LinearIndependent.sum_smul_of_nondegenerate
```

This API already existed at the 4.32 baseline, but the expanded pass-through
audit found a redundant 46-line specialization named
`linearIndependent_sum_smul` in `PEPS/RegionBlock/GaugeInjectivity2.lean`.
The sole consumer now proves the coefficient matrix nondegenerate from its
supplied right inverse and applies the Mathlib theorem directly. The local
lemma is deleted.

Status: exact replacement found while auditing the upgrade; not new in 4.34.

## Scalar and quotient limits

Mathlib commit:

- `73fbc3ec50`, adding specialized scalar-limit lemmas.

Relevant declarations include:

```lean
Filter.Tendsto.zero_smul_const
Filter.Tendsto.one_smul_const
tendsto_div_nhds_one_iff_eq₀
```

`zero_smul_const` and `one_smul_const` replace manual combinations of
`Tendsto.smul`, `tendsto_const_nhds`, and final `zero_smul` or `one_smul`
normalization in:

- `Channel/Peripheral/CesaroRecurrence.lean`;
- `Channel/Peripheral/WeightedCesaro.lean`;
- `Channel/Schwarz/SchwarzSubnormal.lean`.

`tendsto_div_nhds_one_iff_eq₀` replaces a manually assembled quotient limit in
`MPS/SharedInfra/GaugePhase.lean`.

Status: direct proof simplifications.

## Matrix rank closedness through continuous-linear-map rank openness

Import and upstream declaration:

```lean
import Mathlib.Analysis.Normed.Module.FiniteDimension

isOpen_setOfPred_nat_le_rank
```

The mathematical theorem predates 4.32; the current `Set.ofPred` name was
introduced in the 4.33 rename campaign. It proves openness of the set of
continuous linear maps whose rank is at least a fixed natural number.
Transporting this set through the matrix-to-continuous-linear-map equivalence
shows that `{A | A.rank ≤ k}` is closed.

`Matrix.isClosed_setOf_rank_le` remains as a useful matrix specialization, and
the blueprint-tagged lower-semicontinuity declarations remain project API. The
upstream transport replaces their former determinant-minor support proof, so
the following internal-only declarations are deleted:

```lean
Matrix.exists_injective_linearIndependent_cols_of_lt_rank
Matrix.lt_rank_iff_exists_isUnit_submatrix
```

Status: approximately one hundred lines of local support machinery removed;
the matrix adaptation itself remains local.

## Orthonormal families and Gram matrices

Mathlib 4.33 added:

```lean
Matrix.gram_eq_one_iff_orthonormal
```

Together with `Matrix.gram_eq_conjTranspose_mul`, this replaces three local
coordinate proofs that an orthonormal column family gives a unit Gram matrix.
The two public wrappers in `Channel/SchmidtDecomposition.lean` and the private
copy in `Algebra/CompactSVD.lean` are deleted, and their consumers use the
Mathlib Gram identities directly.

Status: three pass-through proofs deleted.

## Finset image equivalences

Mathlib 4.33 added:

```lean
Finset.equivMap
Finset.equivMap_apply_coe
Finset.equivMap_symm_apply
```

`Finset.equivMap` is the canonical equivalence between a finite set and its
image under an embedding. It replaces two local equivalence constructors:

- `SpinChain.siteTranslation` in `QCA/Translation.lean`;
- `TNLean.PEPS.regionVertexMapEquiv` in `PEPS/RegionTransport.lean`.

The project-specific translation and graph-transport APIs remain, but their
consumers now use the upstream finite-image equivalence directly. Inverse
computations in the PEPS transport use the upstream `apply_symm_apply` law
rather than reduction of a local constructor.

Status: two pass-through declarations deleted.

## Renamed APIs and Lean 4.34 warning cleanup

The 4.33 and 4.34 source ranges also introduced deprecations and stricter style
linters. TNLean now uses the current names directly, including:

```lean
if_pos       → ite_eq_left
if_neg       → ite_eq_right
dif_pos      → dite_eq_left
dif_neg      → dite_eq_right
if_true      → ite_true
if_false     → ite_false
Set.restrict → Set.domRestrict
LinearEquiv.ofLinear → LinearEquiv.ofLinearMap
```

The new proposition-instance linter also observes that tactic-mode `have` and
`let` already register proposition-valued local instances. Its reported
`haveI` and `letI` sites were converted without changing proofs. Remaining
unused-tactic, unused-simp-argument, flexible-tactic, finite-typeclass, and
source-layout warnings were repaired individually rather than suppressed.
The pinned Gametheory dependency was updated in the same way; its complete
package build now emits no warnings from Gametheory sources.

The first complete warning inventory contained 2,403 warning headers across
492 files. After the cleanup, the post-rebase 10,201-job build reports only 13
pre-existing long-line warnings in two parent-Hamiltonian modules. Each of
those lines contains an exported identifier whose name alone prevents ordinary
wrapping. They are retained because the audit excludes public renaming solely
to satisfy the line-length linter and excludes local or global suppression.
No deprecation, proposition-instance, tactic, simp-argument, option-scope, or
Gametheory warning remains.

## New APIs that do not replace TNLean mathematics

### Compact convex hulls

Mathlib added `TotallyBounded.convexHull` and
`totallyBounded_convexHull` in `Mathlib.Analysis.Convex.TotallyBounded`.
These prove total boundedness, not compactness or closedness of the convex hull.
Mathlib still has no theorem matching the finite-dimensional result

```lean
IsCompact s → IsCompact (convexHull ℝ s)
```

proved in `TNLean/Analysis/ConvexHullCompact.lean`. The new theorem is a useful
ingredient but does not justify deleting the local Caratheodory argument.

### Second resolvent identity

Mathlib added `spectrum.resolvent_sub_resolvent` in
`Mathlib.Algebra.Algebra.Spectrum.Basic`. The local theorem
`inverseGram_sub_limitingInverse_eq_resolvent` in
`MPS/ParentHamiltonian/C3CorrectionBounds.lean` concerns direct inverses of
continuous linear maps and already uses `Ring.inverse_sub_inverse`. Recasting it
through algebraic spectra would add resolvent-set hypotheses and conversions.

### Fibre direct sums

Mathlib added `DirectSum.sigmaFiberAddEquiv` and its evaluation lemmas. These are
equivalences of algebraic direct sums. They do not replace the dependent
function equivalence in `TNLean/Algebra/PiSigmaEquiv.lean` or the matrix block
reindexing in `TNLean/Algebra/DependentBlockDiagonal.lean`.

### Other additions

The new matrix echelon certificates, Bird determinant correctness theorem,
continuous Hilbert tensor-product map, and finite-image stabilization theorem do
not match a local TNLean implementation. They require no code change in this
upgrade.

## Upgrade compilation failures

The first isolated build under Lean and Mathlib `v4.34.0-rc1` reached
10,177 of 10,194 jobs and exposed 27 TNLean modules plus the Brouwer dependency.
The failures were elaboration and transparency changes rather than mathematical
regressions. The recurring forms were:

- rewrites through dependent function equivalences no longer matching at
  implicit transparency;
- function literals not being recognized definitionally as `Matrix` values;
- simplification across newly less-reducible equivalence constructors;
- missing local decidability witnesses for dependent finite sums;
- coercion mismatches around `Equiv.ofBijective` and subtype equality.

The complete initial log is `/tmp/tnlean_mathlib434_initial_build.log` in the
upgrade environment. Repair work preserves theorem statements and replaces
brittle rewrites with typed intermediates, explicit `change` steps, or direct
term proofs.
