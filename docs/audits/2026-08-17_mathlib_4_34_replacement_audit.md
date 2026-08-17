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
- Mathlib commit: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

There was no final `v4.34.0` tag. The comparison baseline is Mathlib
`v4.32.0`, commit `81a5d257c8e410db227a6665ed08f64fea08e997`.
The range `v4.32.0..v4.34.0-rc1` contains 505 non-merge commits and 4,480
changed paths. It includes the 4.33 release.

The audit inspected feature commits and changed declarations, searched the
Mathlib source by name and type, and compared the resulting APIs with TNLean
declarations and use sites. Mechanical module-system changes and unrelated
subject areas were excluded after the initial inventory.

## Summary

The range contains two deletion-scale replacements in the same low-level
matrix module.

1. Mathlib now proves that the positive-semidefinite cone of square `RCLike`
   matrices is closed and supplies the corresponding scoped
   `OrderClosedTopology` instance. This replaces TNLean's local Loewner-order
   topology development.
2. Mathlib now supplies the `CStarAlgebra` instance for finite complex matrices
   in the L2 operator norm. This replaces TNLean's local bundled instance and
   the duplicate hand-built instances at its use sites.

Two new determinant lemmas also remove local proof plumbing without replacing
project declarations:

- determinant nonvanishing now gives `mulVec` injectivity directly;
- determinant nonvanishing now preserves matrix rank under multiplication
  directly.

No other sound deletion-scale replacement was found. In particular, the new
convex-hull, rank, resolvent, direct-sum, echelon-form, and tensor-product APIs
do not subsume the corresponding TNLean mathematics described below.

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

It therefore exactly replaces that local definition. At sites where TNLean
intentionally avoids opening the operator-norm scope globally, the conservative
replacement is

```lean
letI : CStarAlgebra (Matrix n n ℂ) := Matrix.instCStarAlgebra
```

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

### Rank-minor closedness

The enlarged nonsingularity API relates determinant nonvanishing, regularity,
row and column independence, products, and powers. It does not provide the
rank-minor characterization or semicontinuity results in
`TNLean/Algebra/MatrixRankClosed.lean`. No replacement was found for
`Matrix.lt_rank_iff_exists_isUnit_submatrix`,
`Matrix.isClosed_setOf_rank_le`, or `Matrix.lowerSemicontinuous_rank`.

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
