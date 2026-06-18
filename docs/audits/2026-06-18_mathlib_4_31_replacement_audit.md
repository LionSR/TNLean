# Mathlib 4.31 replacement audit

Date: 2026-06-18.

This audit records Mathlib material newly available, or newly more useful, in
the upgrade from the TNLean baseline Mathlib 4.29 to Mathlib 4.31.  Its purpose
is to identify places where TNLean can replace local auxiliary development by
standard Mathlib declarations, and to distinguish those replacements from
project-specific results that should remain local.

The audit was carried out in the PR 3006 worktree
`codex/audit-mathlib-4.31-pr3006`, based on the PR branch
`claude/mathlib-4-31-update-vw6t4i`.

The dependency pins in the worktree are:

- Lean: `leanprover/lean4:v4.31.0`.
- Mathlib: `v4.31.0`.
- Mathlib commit: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## Executive summary

There are several genuine replacement opportunities.

The clearest replacements are:

- Gram matrix linear independence lemmas in `TNLean/Algebra/GramMatrixLI.lean`
  can now use the two-sided determinant criterion
  `Matrix.det_gram_ne_zero_iff_linearIndependent`, while retaining the local
  convergence packaging.
- Several finite-dimensional matrix-dimension wrappers in
  `TNLean/Algebra/MatrixAux.lean` can be reduced to `Module.finrank_matrix` and
  elementary simplification.
- Trace-from-characteristic-polynomial wrappers can be shortened using the
  expanded Mathlib trace/charpoly API, especially
  `Matrix.trace_eq_neg_charpoly_coeff`,
  `Matrix.trace_eq_neg_charpoly_nextCoeff`, and the eigenvalue-sum trace
  theorems.
- Reindexing code should be updated to the new equivalence API, using
  `Matrix.reindexAddEquiv`, `Matrix.reindexRingEquiv`,
  `Matrix.reindexLinearEquiv`, `Matrix.reindexAlgEquiv`, and their coercion
  lemmas.  The old application lemmas are deprecated in Mathlib 4.31.
- Homogeneous block-triangular power and exponential arguments can use
  `BlockTriangular.pow` and `BlockTriangular.exp`.
- Parts of the local Frobenius-norm development should be replaced by
  `Matrix.Norms.Frobenius`.
- Positive-map and completely-positive-map arguments should gradually acquire
  bridge lemmas to Mathlib's `PositiveLinearMap` and `CompletelyPositiveMap`.

There are also important non-replacements.

- TNLean's `nilpIndex` in the Fitting-decomposition files is not replaced by
  Mathlib's `LinearMap.index`; the latter is the Fredholm index.
- The local Choi, Kraus, partial-trace, tensor-map, and quantum-channel
  definitions remain mathematically necessary.  Mathlib 4.31 has abstract
  completely positive maps for C-star algebras, but it does not provide the
  concrete Wolf-style channel interface used in TNLean.
- The trace Jensen and matrix functional-calculus trace statements in the
  Schwarz files are not direct Mathlib theorems.  Mathlib's new operator
  concavity and monotonicity results can shorten hypotheses and intermediate
  order arguments, but not replace the trace inequalities wholesale.
- Word-products of varying matrices are not directly covered by
  `BlockTriangular.pow`; the local `evalWord` inductions remain necessary
  unless the word-product arguments are reorganized through a submonoid or
  subsemiring construction.

## Mathlib 4.31 material found

The following Mathlib changes in the interval from `v4.29.0` to `v4.31.0` are
most relevant for TNLean.

### Gram matrices

Relevant Mathlib commit:

- `25560be0051`: Gram determinant nonvanishing iff linear independence.
- `95c9f65b4a4`: additional positive-semidefinite Gram API.

Relevant declarations include:

- `Matrix.linearIndependent_of_det_gram_ne_zero`
- `Matrix.posDef_gram_iff_linearIndependent`
- `Matrix.det_gram_ne_zero_iff_linearIndependent`
- `Matrix.PosSemidef.gram`
- `Matrix.posSemidef_of_mapL`

TNLean currently has local convergence-to-Gram lemmas in
`TNLean/Algebra/GramMatrixLI.lean`:

- `eventually_linearIndependent_of_gram_tendsto_nondegenerate`
- `eventually_linearIndependent_of_gram_tendsto_id`

These results are not themselves in Mathlib, because they combine matrix-entry
convergence with eventual nonvanishing of a determinant.  However, the final
linear-independence step should use
`Matrix.det_gram_ne_zero_iff_linearIndependent`.  The local file should keep
only the topological packaging.

Recommended action:

- Keep the two TNLean convergence lemmas.
- Replace the final one-direction Gram step by the two-sided Mathlib theorem.
- Consider adding a short local wrapper only if it materially improves the
  statement shape used downstream.

### Fitting decomposition and generalized eigenspaces

Relevant Mathlib declarations include:

- `Module.End.exists_ker_pow_eq_ker_pow_succ`
- `Module.End.ker_pow_eq_ker_pow_finrank_of_le`
- `Module.End.ker_pow_le_ker_pow_finrank`
- `Module.End.ker_pow_constant`

TNLean already uses much of this API in
`TNLean/Wielandt/FittingDecomposition.lean`.  The remaining local development
there concerns the project's nilpotent index and the decomposition lemmas
needed for Wielandt theory.

Important distinction:

- Mathlib 4.31 also contains `LinearMap.index` in
  `Mathlib/Algebra/Module/LinearMap/Index.lean`.
- This is the Fredholm index, namely a difference of kernel and cokernel
  dimensions.
- It is not TNLean's local nilpotency or generalized-eigenspace stabilization
  index.

Recommended action:

- Do not rename or replace `nilpIndex` by `LinearMap.index`.
- Continue to use Mathlib's `ker_pow_*` stabilization lemmas.
- Keep the project-specific nilpotent-index lemmas local unless Mathlib later
  gains a dedicated generalized-eigenspace-index API.

### Reindexing matrices

Relevant Mathlib commit:

- `5b9fcab5dee`: reindexing as additive, ring, linear, and algebra
  equivalences.

Relevant declarations include:

- `Matrix.reindexAddEquiv`
- `Matrix.reindexRingEquiv`
- `Matrix.reindexLinearEquiv`
- `Matrix.reindexAlgEquiv`
- `Matrix.coe_reindexLinearEquiv`
- `Matrix.coe_reindexAlgEquiv`
- `Matrix.reindexLinearEquiv_mul`
- `Matrix.reindexLinearEquiv_comp_apply`
- `Matrix.det_reindexAlgEquiv`

Mathlib 4.31 deprecates some older direct application lemmas, such as
`Matrix.reindexLinearEquiv_apply` and `Matrix.reindexAlgEquiv_apply`, in favor
of coercion lemmas.

TNLean files containing deprecated or fragile reindexing code include:

- `TNLean/PEPS/TorusGaugedWeightCovariance.lean`
- `TNLean/PEPS/TorusGaugeUniqueness.lean`
- `TNLean/Channel/Schwarz/SchwarzSubnormal.lean`
- `TNLean/PEPS/RegionBlock/CoarseThreeSite11.lean`
- `TNLean/PEPS/RegionBlock/Insertion.lean`
- `TNLean/PEPS/RegionTransportInsertion.lean`
- `TNLean/PEPS/EdgeGaugeFamily.lean`
- `TNLean/Channel/Peripheral/CyclicDecomposition/Basic.lean`
- `TNLean/PEPS/FundamentalTheorem/OneVertexComparison.lean`
- `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`
- `TNLean/MPS/SharedInfra/BlockAssembly.lean`

Recommended action:

- First replace deprecated application lemmas by coercion lemmas.
- Where possible, state goals directly using raw `Matrix.reindex`.
- Use the equivalence API only when invertibility, determinant preservation, or
  algebra compatibility is needed.
- Avoid adding local reindexing wrappers unless a file uses the same cast
  pattern repeatedly.

### Rank and finite-dimensional matrix dimensions

Relevant Mathlib commits:

- `dd7fc3b379c`: generalization of `Matrix.rank` and `LinearMap.rank` to
  semirings.

Relevant declarations include:

- `Matrix.rank`
- `LinearMap.rank`
- `Matrix.rank_le_width`
- `Matrix.rank_le_height`
- `Matrix.rank_mul_le_left`
- `Matrix.rank_mul_le_right`
- `Matrix.rank_eq_finrank_range_toLin`
- `Matrix.rank_eq_finrank_span_cols`
- `Matrix.rank_eq_finrank_span_row`
- `Matrix.rank_conjTranspose_mul_self`
- `Matrix.rank_conjTranspose`
- `Matrix.rank_self_mul_conjTranspose`
- `Matrix.rank_transpose`
- `Matrix.rank_add_rank_le_card_of_mul_eq_zero`

TNLean has local finite-dimensional wrappers such as:

- `Matrix.finrank_matrix_fin_eq_sq`
- `Matrix.finrank_top_matrix_fin_eq_sq`
- `Matrix.dim_le_of_mulVec_injective`

Known downstream uses include:

- `TNLean/Wielandt/SpanGrowth/InvertibleWordSpan.lean`
- `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`

Recommended action:

- Replace square-dimension wrappers by `Module.finrank_matrix` plus
  simplification.
- Replace injectivity-to-dimension arguments by
  `LinearMap.finrank_le_finrank_of_injective` when the map has already been
  expressed as a linear map.
- Keep local lemmas only when they encode a recurring theorem statement in the
  vocabulary of MPS or Wielandt theory.

### Positive definite and positive semidefinite matrices

Relevant Mathlib commits:

- `6db85f34e46`: positive definiteness of submatrices and Hadamard submatrices.
- `fa7db6bce04`: Schur product theorem for the Hadamard product.

Relevant declarations include:

- `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`
- `Matrix.PosSemidef.kronecker`
- `Matrix.PosDef.submatrix`
- `Matrix.PosSemidef.posDef_iff_isUnit`
- `Matrix.isStrictlyPositive_iff_posDef`
- `Matrix.PosSemidef.hadamard`
- `Matrix.PosDef.hadamard`

TNLean currently has positive-semidefinite auxiliary lemmas in
`TNLean/Algebra/MatrixAux.lean`, including kernel consequences for sums of
positive semidefinite matrices.  The Mathlib theorem
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff` can shorten some proofs, but no
direct replacement was found for every local kernel-of-sum lemma.

Recommended action:

- Replace Hadamard, submatrix, and strict-positivity arguments by Mathlib
  theorems when they occur.
- Keep local lemmas of the form "from `(A+B)v = 0` infer `Av = 0`" unless a
  direct Mathlib theorem is later found.
- Consider upstreaming the positive-semidefinite kernel-sum lemmas if they are
  stated without TNLean-specific hypotheses.

### Determinants, kernels, and characteristic polynomials

Relevant Mathlib commits:

- `edf920b3415`: characteristic-polynomial coefficient formula via principal
  minors.
- `9eb40b41e4c`: eigenvalue and characteristic-polynomial API generalized to
  commutative rings.
- `c0ee2a93750`: trace/eigenvalue transfer lemmas from matrices to linear maps.
- `d2962c4edce`: strengthened Cayley-Hamilton theorem.
- `3ba74fa0b75`: determinant vanishing from a nonzero kernel vector with
  non-zero-divisor coordinate.

Relevant declarations include:

- `Matrix.exists_mulVec_eq_zero_iff`
- `Matrix.nondegenerate_iff_det_ne_zero`
- `Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors`
- `Matrix.trace_eq_neg_charpoly_coeff`
- `Matrix.trace_eq_neg_charpoly_nextCoeff`
- `Matrix.trace_eq_sum_roots_charpoly_of_splits`
- `Matrix.trace_eq_sum_roots_charpoly`
- `Matrix.IsHermitian.trace_eq_sum_eigenvalues`

TNLean has local statements such as:

- `Matrix.trace_eq_of_charpoly_eq`
- Newton-Girard and unit-modulus power-sum auxiliaries.
- Hermitian spectral-decomposition trace formulas in
  `TNLean/Algebra/MatrixSpectralDecomp.lean` and the Schwarz trace-CFC files.

Recommended action:

- Replace elementary trace-from-charpoly wrappers by Mathlib declarations.
- Keep Newton-Girard and unit-modulus power-sum arguments local if they are
  tuned to finite peripheral-spectrum arguments.
- Revisit Hermitian trace-CFC lemmas after checking whether they can be proved
  from `Matrix.IsHermitian.trace_eq_sum_eigenvalues` and existing CFC
  eigenvalue evaluation lemmas.

### Block triangular matrices and exponentials

Relevant Mathlib commit:

- `421fab31a9d`: `BlockTriangular.pow` and `BlockTriangular.exp`.

Relevant declarations include:

- `BlockTriangular.pow`
- `BlockTriangular.exp`

TNLean has block-triangular trace and projection-triangular trace files:

- `TNLean/Algebra/BlockTriangularTrace.lean`
- `TNLean/Algebra/ProjectionTriangularTrace.lean`

The Mathlib theorem `BlockTriangular.pow` is a direct replacement for
homogeneous powers of one block-triangular matrix.  The theorem
`BlockTriangular.exp` should replace local proofs about exponentials of
block-triangular matrices, if such proofs appear in semigroup arguments.

The local MPS word-product setting is subtler: `evalWord A w` multiplies a
sequence of matrices selected by a word.  This is not a power of one matrix.
The local inductive closure argument remains necessary unless the triangular
matrices are bundled as a submonoid or subsemiring and word evaluation is
recast as a product in that substructure.

Recommended action:

- Use `BlockTriangular.pow` and `BlockTriangular.exp` for one-matrix power and
  exponential arguments.
- Keep local `evalWord` induction lemmas for products of varying letters.
- Consider a future small abstraction for "all letters preserve a fixed flag",
  but only if it removes repeated induction proofs.

### Frobenius norm

Relevant Mathlib declarations are in the Frobenius-norm namespace and scoped
notation:

- `open scoped Matrix.Norms.Frobenius`
- `Matrix.frobenius_norm_def`
- `Matrix.frobenius_nnnorm_def`
- `Matrix.frobenius_norm_mul`
- `Matrix.frobenius_norm_conjTranspose`
- `Matrix.frobeniusNormedRing`
- `Matrix.frobeniusNormedAlgebra`

TNLean has local Frobenius-norm infrastructure in:

- `TNLean/Spectral/FrobeniusNorm.lean`
- `TNLean/Spectral/TransferOperatorGap.lean`

The local development defines square-norm and Euclidean-space embeddings such
as `frobSq`, `matToES`, and associated norm identities.  Mathlib's Frobenius
norm should replace much of this general matrix-norm infrastructure.

Recommended action:

- Prefer Mathlib's Frobenius norm for new proofs.
- Replace local square-norm lemmas when downstream arguments do not genuinely
  require the squared form.
- Keep MPS-specific transfer-operator estimates and sum identities local.
- If squared Frobenius norms are still convenient, define only a thin local
  wrapper around the Mathlib norm rather than maintaining an independent
  Euclidean embedding.

### Positive and completely positive maps

Relevant Mathlib commit:

- `f1ceb733fa4`: positive linear-map cleanup and API expansion.

Relevant declarations and structures include:

- `PositiveLinearMap`
- `PositiveLinearMap.exists_norm_apply_le`
- `PositiveLinearMap.map_isSelfAdjoint`
- `PositiveLinearMap.apply_le_of_isSelfAdjoint`
- `PositiveLinearMap.norm_apply_le_of_nonneg`
- `CompletelyPositiveMap`
- `CompletelyPositiveMap.map_cstarMatrix_nonneg`
- `CompletelyPositiveMapClass`

TNLean has concrete quantum-channel structures in:

- `TNLean/Channel/Basic.lean`
- `TNLean/Channel/ChoiJamiolkowski.lean`
- `TNLean/Channel/TwoPositive.lean`
- `TNLean/Channel/CPClosure.lean`
- `TNLean/Channel/PartialTrace.lean`
- `TNLean/Channel/TensorMap.lean`

Mathlib's abstract C-star-algebra notion of complete positivity is
mathematically relevant but not a direct replacement for the concrete
finite-dimensional channel interface.  TNLean's channel statements use Kraus
witnesses, Choi matrices, trace preservation, and partial traces in the form
used by Wolf's notes.

Recommended action:

- Do not replace the local channel definitions wholesale.
- Add bridge lemmas in a separate layer:
  local Kraus positivity implies a Mathlib `CompletelyPositiveMap`, and
  Mathlib complete positivity implies the local finite-dimensional positivity
  statements when transported to matrices.
- Use `PositiveLinearMap` to replace local proofs of self-adjointness,
  monotonicity, and boundedness only after the bridge exists.
- Keep Choi, Kraus, Stinespring, partial trace, and tensor-map statements local.

### Operator convexity, monotonicity, and CFC

Relevant Mathlib commits:

- `2113b17760b`: operator concavity for powers in C-star algebras.
- `a9dd44d920b`: inverse is convex and antitone on strictly positive
  operators.
- `77760d482b5`: additional joint continuity for CFC.

Relevant declarations include:

- `CFC.concaveOn_rpow`
- `CFC.concaveOn_nnrpow`
- `CFC.concaveOn_sqrt`
- `CFC.monotone_rpow`
- `CFC.rpow_le_rpow`
- `CFC.monotone_log`
- `CFC.log_le_log`
- `CFC.concaveOn_log`

TNLean has trace and Jensen-style results in:

- `TNLean/Analysis/OperatorConvexity.lean`
- `TNLean/Channel/Schwarz/OperatorConvexity.lean`
- `TNLean/Channel/Schwarz/TraceCFC.lean`

Mathlib 4.31 can strengthen the order-theoretic part of these arguments, but
the trace Jensen inequalities and matrix-trace CFC formulas remain
TNLean-specific.

Recommended action:

- Use the new CFC monotonicity and concavity theorems to remove scalar
  side-proofs and ad hoc operator-order lemmas.
- Remove exact matrix-specialized aliases of these order lemmas when the
  Mathlib theorem has the same content.  This has been done in
  `TNLean/Channel/Schwarz/OperatorMonotone.lean` for the former aliases of
  `CFC.rpow_le_rpow` and `CFC.log_le_log`.
- Keep local trace Jensen statements until Mathlib has corresponding trace
  inequalities for positive or completely positive maps.
- Consider upstreaming source-independent trace-CFC lemmas once their
  assumptions are clean.

### Projection and continuous-linear-map API

Relevant Mathlib commits:

- `20ba84f192c`: `ContinuousLinearMap.restrict`.
- `dd27355ce09`: quotient equivalences for complements.
- `84637434b5b`: `Submodule.IsTopCompl`.
- `50fb945baba`: rename to `Submodule.projectionOnto`.

Relevant declarations include:

- `Submodule.projectionOnto`
- `Submodule.IsTopCompl`
- `ContinuousLinearMap.restrict`
- `LinearMap.IsSymmetricProjection.isPositive`
- `LinearMap.IsSymmetricProjection.le_iff_range_le_range`
- `Submodule.starProjection_*`
- `IsStarProjection`

TNLean files where this may be useful include:

- `TNLean/Analysis/ProjectionGeometry.lean`
- `TNLean/Algebra/ProjectionTriangularTrace.lean`
- fixed-point and peripheral-spectrum files using invariant subspaces.

Recommended action:

- Replace elementary symmetric-projection positivity arguments by Mathlib
  projection API where possible.
- Keep the Friedrichs-angle and martingale-type estimates local.
- Prefer `Submodule.projectionOnto` for new complement projections.

## File-by-file replacement map

### `TNLean/Algebra/GramMatrixLI.lean`

Status: mostly local, with a stronger Mathlib final step.

The file already builds under Mathlib 4.31.  Its local content concerns
eventual linear independence under convergence of Gram matrices.  Mathlib now
contains the exact algebraic determinant criterion.  The local proof should be
shortened around that criterion, but the convergence result should remain in
TNLean.

### `TNLean/Wielandt/FittingDecomposition.lean`

Status: keep local nilpotent-index theory.

The file already uses Mathlib's kernel-power stabilization lemmas.  The local
`nilpIndex` is not the same as Mathlib's `LinearMap.index`.  Replacement should
be limited to any remaining elementary kernel-stabilization arguments.

### `TNLean/Algebra/MatrixAux.lean`

Status: several wrappers are candidates for deletion or shrinking.

Likely replacements:

- `finrank_matrix_fin_eq_sq` by `Module.finrank_matrix`.
- `finrank_top_matrix_fin_eq_sq` by `Module.finrank_matrix` and top-submodule
  simplification.
- `dim_le_of_mulVec_injective` by
  `LinearMap.finrank_le_finrank_of_injective`.
- `trace_eq_of_charpoly_eq` by Mathlib trace/charpoly coefficient lemmas.
- Elementary sum-distribution lemmas by `Matrix.sum_mul`, `Matrix.mul_sum`,
  and simplification.

Keep for now:

- Positive-semidefinite kernel lemmas for sums, unless a direct Mathlib theorem
  is found.
- Trace-pairing wrappers if they are used pervasively, though they should be
  reproved using `Matrix.ext_iff_trace_mul_left` and
  `Matrix.ext_iff_trace_mul_right`.

### `TNLean/Algebra/BlockTriangularTrace.lean`

Status: partial replacement.

Use Mathlib's `BlockTriangular.pow` for powers of one matrix.  Keep local word
products and trace identities involving `evalWord`.

### `TNLean/Algebra/ProjectionTriangularTrace.lean`

Status: project-specific.

Mathlib projection and block-triangular APIs may shorten supporting lemmas, but
the main projection-triangular trace statement is adapted to TNLean's MPS word
products and should remain local.

### `TNLean/Spectral/FrobeniusNorm.lean`

Status: strong refactor candidate.

This is one of the most promising local developments to shrink.  Mathlib's
Frobenius norm should become the default norm for matrix Hilbert-Schmidt
arguments.  The local squared norm may remain as a convenience wrapper, but
should no longer carry an independent foundation.

The old `TNLean/Algebra/MatrixFrobenius.lean` pass-through file exposed only
positive-definiteness of the identity matrix for the Frobenius inner product.
It has been removed: call sites now use Mathlib's `Matrix.PosDef.one`
directly.

### `TNLean/Spectral/TransferOperatorGap.lean`

Status: partial replacement.

The matrix-norm parts should move toward Mathlib's Frobenius norm.  The
transfer-operator gap estimates are project-specific and remain local.

### `TNLean/Channel/Semigroup/ProductFormula.lean`

Status: keep most local estimates.

Mathlib has complex exponential norm facts and commutation lemmas, but no
direct replacement was found for the general Banach-algebra estimate
`norm_exp_le_real_exp_norm` in the form used by TNLean, nor for the Trotter
error estimates.  These statements are good candidates for eventual upstreaming
if they can be stated abstractly.

### `TNLean/Analysis/OperatorConvexity.lean`

Status: partial replacement.

Use Mathlib's new CFC monotonicity and concavity facts to shorten order
arguments.  Keep trace Jensen statements local.

### `TNLean/Channel/Schwarz/OperatorConvexity.lean`

Status: partial replacement.

Same conclusion as above.  The Mathlib CFC theorems should help with the
operator-order part, but the trace inequalities for positive maps remain
TNLean-specific.

### `TNLean/Channel/Basic.lean` and CP-related channel files

Status: bridge, not replacement.

Do not discard the local channel API.  Instead, add bridge theorems to
Mathlib's `PositiveLinearMap` and `CompletelyPositiveMap`.  The local finite
matrix channel definitions remain the correct interface for Wolf-style
theorems.

### `TNLean/Channel/PartialTrace.lean` and `TNLean/Channel/TensorMap.lean`

Status: keep local.

No direct Mathlib partial-trace or Choi/Jamiolkowski API was found.  Mathlib's
C-star matrix and Kronecker APIs may support future refactoring, but not
replacement.

### `TNLean/Algebra/MatrixSpectralDecomp.lean`

Status: partial replacement.

The local Hermitian spectral-decomposition trace formulas should be revisited
using `Matrix.IsHermitian.trace_eq_sum_eigenvalues`.  Concrete decompositions
of positive semidefinite matrices into eigenvector outer products remain local
unless Mathlib later adds exactly that statement.

### `TNLean/Analysis/ProjectionGeometry.lean`

Status: partial replacement.

Use Mathlib projection positivity and range-order facts where they fit.  Keep
Friedrichs-angle and aggregate projection estimates local.

## Recommended order of work

The following order minimizes mathematical risk.

1. Reindexing deprecations.
   These are syntactic and local.  They reduce future warning noise and should
   not change mathematical statements.

2. Finrank and trace-charpoly wrappers in `MatrixAux`.
   These replacements are elementary and can be checked file by file.

3. Gram matrix cleanup.
   Replace one-direction arguments by
   `Matrix.det_gram_ne_zero_iff_linearIndependent`, keeping the convergence
   lemmas.

4. Frobenius-norm migration.
   This has larger downstream impact, so it should be done after the basic
   upgrade compiles.  Start with new lemmas and only then remove old wrappers.

5. Block-triangular power and exponential cleanup.
   Use Mathlib's `BlockTriangular.pow` and `BlockTriangular.exp` where the
   expression is truly a power or exponential of one matrix.

6. Positive-map and completely-positive-map bridges.
   This should be a separate mathematical PR.  It changes the interface
   between the local channel theory and Mathlib's C-star-algebra API.

7. Operator-convexity and trace-CFC cleanup.
   This should follow the bridge work, since many statements involve positive
   maps and order preservation.

## Immediate Mathlib 4.31 build issue observed and local repair

After fetching Mathlib 4.31 caches, the following command was run:

```text
lake build TNLean.Algebra.MatrixFunctionalCalculus \
  TNLean.Algebra.ProjectionTriangularTrace \
  TNLean.Algebra.MatrixOperatorSpace
```

In the initial check, the first two targets built, but
`TNLean.Algebra.MatrixOperatorSpace` failed.  The failures were typeclass
failures around continuous-linear-map normed instances for

```text
MatrixCLM n := Matrix n n C ->L[C] Matrix n n C
```

The failing instances included:

- `NormedSpace C (TNLean.MatrixCLM n)`
- `NormedAlgebra C (TNLean.MatrixCLM n)`
- `NormedAlgebra R (TNLean.MatrixCLM n)`
- `IsUniformAddGroup (TNLean.MatrixCLM n)`

Local Lean checks indicate that Mathlib 4.31 provides the relevant continuous
linear map instances:

- `ContinuousLinearMap.toNormedSpace`
- `ContinuousLinearMap.toNormedAlgebra`

Adding explicit complex normed-space and normed-algebra instances for
`MatrixCLM n` makes the immediate complex instance search succeed in small
checks.  The current worktree contains exactly this repair: it exposes the
complex `NormedSpace` and `NormedAlgebra` instances through
`ContinuousLinearMap.toNormedSpace` and
`ContinuousLinearMap.toNormedAlgebra`, restricts scalars for the real normed
algebra instance, and removes the local `CompleteSpace` instance whose proof
passed through `FiniteDimensional.complete`.

Current status:

- `lake env lean TNLean/Algebra/MatrixOperatorSpace.lean` succeeds.
- `lake build TNLean.Algebra.MatrixOperatorSpace` succeeds.

This was a genuine upgrade compatibility issue, separate from the replacement
audit.  Its local repair is already present in the worktree.

## Verification performed

The Mathlib cache was fetched for the 4.31 worktree.  An initial cache fetch
encountered a corrupted local archive; rerunning the forced cache command
succeeded.

The following focused checks succeeded under Mathlib 4.31 during the audit and
adaptation work:

```text
lake env lean TNLean/Algebra/GramMatrixLI.lean
lake build TNLean.Algebra.MatrixOperatorSpace
lake env lean TNLean/MPS/Symmetry/StringOrder.lean --json
lake env lean TNLean/Wielandt/Primitivity/PrimitiveBridge.lean --json
lake env lean TNLean/Channel/Semigroup/Primitivity/Basic.lean --json
lake env lean TNLean/Channel/Semigroup/Primitivity/Helpers.lean --json
lake env lean TNLean/MPS/CanonicalForm/Existence.lean --json
lake env lean TNLean/MPS/CanonicalForm/SectorComparison/PrimitiveBlocks.lean --json
lake env lean TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean --json
lake env lean TNLean/MPS/CanonicalForm/SectorComparison/CommonBlockedCyclicSectorFamily.lean --json
lake env lean TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorData.lean --json
lake build TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData -q --log-level=info
lake env lean TNLean/MPS/Periodic/Overlap/SelfOverlapSetup.lean --json
lake env lean TNLean/MPS/Periodic/Overlap/Dichotomy.lean --json
lake env lean TNLean/MPS/Periodic/FundamentalTheorem.lean --json
lake env lean TNLean/MPS/Periodic/Symmetry/Theorem41Forward.lean --json
```

The final root build also succeeds:

```text
lake build -q --log-level=info
```

The build still reports pre-existing warnings: style-header warnings, module
docstring placement warnings, deprecated theorem names such as
`tendsto_finset_sum`, and the existing `sorry` warning in
`TNLean/MPS/Periodic/Overlap/Case3.lean`.

The compatibility repairs made while reaching this state are proof-level
adaptations: explicit coercion/unfolding steps for continuous linear maps,
trace-preserving Kraus normalization, finite type bijections, semigroup scalar
exponentials, and related definitional equalities whose elaboration changed
between Mathlib 4.29 and 4.31.  No theorem statement was intentionally
strengthened or weakened by these repairs.

## Conclusions

Mathlib 4.31 materially improves the background library for TNLean, especially
around Gram matrices, reindexing, rank, trace and characteristic polynomials,
block-triangular powers and exponentials, Frobenius norms, C-star-algebra CFC,
positive maps, completely positive maps, and projection API.

The upgrade should not be treated as a wholesale replacement of TNLean's
quantum-channel layer.  The local finite-dimensional Choi, Kraus, partial
trace, tensor-map, and MPS word-product developments remain mathematically
load-bearing.  The best course is to remove elementary duplicated linear
algebra first, then build bridges to the abstract C-star-algebra API in
separate, reviewable steps.
