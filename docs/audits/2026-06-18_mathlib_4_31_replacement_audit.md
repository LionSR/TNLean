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
  `TNLean/Algebra/MatrixAux.lean` have been removed or reduced to direct
  Mathlib finite-rank arguments.
- The local finite-sum wrapper `Matrix.sum_mul_mul` was only a specialization
  of Mathlib's `Matrix.sum_mul` and `Matrix.mul_sum`, and has been removed.
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
- Hermitian eigenvector-unitary wrappers should be replaced by Mathlib's
  unitary-group API, such as `Matrix.UnitaryGroup.star_mul_self`,
  `Unitary.mul_star_self_of_mem`, and `Matrix.UnitaryGroup.det_isUnit`.
- Local shaped Hermitian spectral-decomposition wrappers should be avoided:
  call sites can use `Matrix.IsHermitian.spectral_theorem` directly and locally
  simplify Mathlib's `conjStarAlgAut` form to `U * diagonal * Uᴴ`.
- The old `TNLean.Algebra.MatrixFunctionalCalculus` scope is no longer needed:
  Mathlib 4.31 provides the required matrix `NonnegSpectrumClass` instance
  through `MatrixOrder`, and the non-unital CFC instance through
  `ContinuousFunctionalCalculus.toNonUnital`.
- The remaining local uses of deprecated-name aliases in non-Archive Lean code
  were exact pass-through layers and have been removed after confirming that the
  new names are used internally.  Some deprecated compatibility declarations are
  retained where they are public names.
- Positive-map and completely-positive-map arguments should gradually acquire
  bridge lemmas to Mathlib's `PositiveLinearMap` and `CompletelyPositiveMap`.
  The first such bridge, `IsPositiveMap.toPositiveLinearMap`, is now used to
  prove `IsPositiveMap.map_isHermitian` from Mathlib's `map_isSelfAdjoint`.
- The remaining non-Archive axioms were checked.  They are all still used, and
  Mathlib 4.31 does not yet contain direct replacements for their statements.
  The operator-concavity facts newly available in Mathlib are useful inputs for
  future proofs of the Jensen axioms, not replacements for the present
  positive-map Jensen conclusions.
- Four scalar-instance pass-through abbreviations in
  `TNLean.Algebra.MatrixOperatorSpace` were removed.  Their few explicit users
  now use the corresponding `inferInstance` arguments directly.
- The rectangular continuous-linear-map instance package formerly exported by
  `TNLean.Spectral.GaugeConstruction` has mostly been inlined in the
  spectral-radius proofs.  They now use Mathlib's
  `ContinuousLinearMap.toNormedRing`, `ContinuousLinearMap.toNormedAlgebra`,
  and local finite-dimensional completeness proofs directly; the former
  finite-dimensional witness remains only as a deprecated compatibility name.
- Two one-use Frobenius submultiplicativity wrappers in the transfer-operator
  gap files were removed.  The proofs now call Mathlib's
  `Matrix.frobenius_norm_mul` directly at the Hilbert-Schmidt estimate.

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
- Use the Mathlib 4.31 name `LinearMap.coe_restrict_apply` rather than the
  deprecated `LinearMap.restrict_coe_apply`.
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

Applied PEPS follow-up:

- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_smul` were removed.  The four
  scalar transport sites in `TNLean/PEPS/TorusGaugeUniqueness.lean` now rewrite
  by Mathlib's `map_smul` for the algebra equivalence, while the public theorem
  remains as a deprecated compatibility name.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_finCongr_symm_round` were
  removed from `TNLean/PEPS/EdgeGaugeFamily.lean`.  The only local transport
  site now uses a proof by simplifying `Matrix.reindexAlgEquiv` directly, while
  the public theorem remains as a deprecated compatibility name.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_gaugeConj` were removed.  The
  only use in `TNLean/PEPS/TorusWitnessTransport.lean` now uses `map_mul`,
  `map_inv`, and `glReindex_coe` directly, while the public theorem remains as
  a deprecated compatibility name.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_transpose` were removed.  Its
  users now call Mathlib's `Matrix.transpose_reindex` directly, with local
  `change` steps where the gauge-applied bond dimension is definitionally equal
  to the original one, while the public theorem remains as a deprecated
  compatibility name.
- The corresponding blueprint theorem was deleted, since the algebra fact is
  now an inline proof step in the blueprint route rather than a formalized
  target.
- The private MPS cyclic-sector helper
  `reindexLinearEquiv_conjTranspose` was removed from
  `TNLean/MPS/CanonicalForm/CyclicSectors/Compression.lean`; its two uses now
  cite Mathlib's `Matrix.conjTranspose_reindex` directly.

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

TNLean had local finite-dimensional wrappers such as:

- `Matrix.finrank_matrix_fin_eq_sq`
- `Matrix.finrank_top_matrix_fin_eq_sq`
- `Matrix.dim_le_of_mulVec_injective`

The square-dimension wrappers and the rectangular injectivity-to-dimension
wrapper have now been removed.  The remaining rectangular dimension arguments
in `TNLean/Spectral/GaugeConstruction.lean` and
`TNLean/Spectral/TransferOperatorGapNT.lean` use
`Matrix.toLin'` together with `LinearMap.finrank_le_finrank_of_injective`
directly.

Recommended action:

- Prefer `Module.finrank_matrix`, `Matrix.toLin'`, and
  `LinearMap.finrank_le_finrank_of_injective` directly for future
  dimension-counting proofs.
- Use `Matrix.sum_mul` and `Matrix.mul_sum` directly for fixed matrix factors
  pulled through finite sums; the former local wrapper `Matrix.sum_mul_mul` has
  been removed from `TNLean/Algebra/MatrixAux.lean`.
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

### Hermitian spectral decomposition and unitary matrices

Relevant Mathlib declarations include:

- `Matrix.IsHermitian.spectral_theorem`
- `Matrix.UnitaryGroup.star_mul_self`
- `Unitary.mul_star_self_of_mem`
- `Matrix.UnitaryGroup.det_isUnit`

TNLean's Hermitian spectral helper file should keep the genuinely local
extremal-eigenvalue and scalar-shift lemmas, such as `minEigenvalue`,
`maxEigenvalue`, `hermitian_sub_scalar_spectral`, and
`smul_one_sub_hermitian_spectral`.

The elementary eigenvector-unitary wrappers were exact aliases for Mathlib
facts and have been removed:

- `eig_conj_mul`
- `eig_mul_conj`
- `eigenvectorUnitary_isUnit`

The dependent proofs now use the Mathlib unitary facts directly.  Two private
copies of a shaped spectral-decomposition lemma were also removed from
`TNLean/Channel/PerronFrobenius/Normalization.lean` and
`TNLean/MPS/Irreducible/FixedPointProjection.lean`.

The public shaped spectral-decomposition wrappers were also removed from
`TNLean/Algebra/HermitianHelpers.lean`:

- `Matrix.IsHermitian.spectral_decomp_eq_of_generalIndex`
- `spectral_decomp_eq`

The remaining uses now invoke `Matrix.IsHermitian.spectral_theorem` directly,
with local simplification of `Unitary.conjStarAlgAut_apply`,
`Matrix.star_eq_conjTranspose`, and `Function.comp_def` when the proof needs
the concrete `U * diagonal * Uᴴ` form.

Recommended action:

- Prefer Mathlib's unitary API directly for `Uᴴ * U = 1`, `U * Uᴴ = 1`, and
  invertibility of an eigenvector unitary.
- Prefer local one-line invocations of `Matrix.IsHermitian.spectral_theorem`
  over shared pass-through lemmas for the shaped spectral decomposition.
- Do not add new local aliases for elementary unitary identities.

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
- `map_isSelfAdjoint`
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
- Add bridge lemmas:
  local Kraus positivity implies a Mathlib `CompletelyPositiveMap`, and
  Mathlib complete positivity implies the local finite-dimensional positivity
  statements when transported to matrices.
- Use `PositiveLinearMap` to replace local proofs of self-adjointness,
  monotonicity, and boundedness when this does not change the public channel
  vocabulary.
- Keep Choi, Kraus, Stinespring, partial trace, and tensor-map statements local.

Applied bridge:

- `TNLean/Channel/Basic.lean` now defines
  `IsPositiveMap.toPositiveLinearMap`.
- The proof of `IsPositiveMap.map_isHermitian` now applies Mathlib's
  `map_isSelfAdjoint` to this bridge, replacing the local CFC positive-part /
  negative-part decomposition.
- `TNLean/Channel/Schwarz/PositiveMapProperties.lean` now proves
  `IsPositiveMap.map_le_map` by the monotonicity of the bridged
  `PositiveLinearMap`, and proves `IsPositiveMap.map_conjTranspose` from
  Mathlib's star-preservation theorem for positive maps between C-star
  algebras.
- The direct imports of the CFC basic and positive-part files were removed from
  `TNLean/Channel/Basic.lean`; the needed Mathlib theorem is provided by
  `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap`.

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

The former scoped helper file `TNLean/Algebra/MatrixFunctionalCalculus.lean`
has been removed.  Its two instances are available directly from Mathlib 4.31:
`Matrix.instNonnegSpectrumClass` under `open scoped MatrixOrder`, and
`ContinuousFunctionalCalculus.toNonUnital`.

The same `MatrixOrder` scoped instance also replaces the private local matrix
`NonnegSpectrumClass` aliases that were present in:

- `TNLean/Analysis/OperatorConvexity.lean`
- `TNLean/Axioms/OperatorConvexity.lean`
- `TNLean/Channel/Schwarz/OperatorMonotone.lean`
- `TNLean/Channel/Schwarz/OperatorConvexity.lean`
- `TNLean/Channel/Schwarz/AndoLieb.lean`

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

### Sanctioned axiom audit

The non-Archive Lean sources contain eight actual axiom declarations:

- `posMap_rpow_concave_jensen`
- `posMap_rpow_convex_jensen`
- `posMap_log_concave_jensen`
- `lieb_concavity_axiom`
- `Axioms.rfp_to_nncph_commute`
- `Axioms.beigi_nncph_to_rfp`
- `strong_subadditivity`
- `hayashi_ssa_equality_characterization`

All eight have downstream uses.  None is an unused declaration that can be
deleted without changing the present chain of proved results.

Mathlib 4.31 gives useful new ingredients for the first and third operator
axioms:

- `CFC.concaveOn_rpow`
- `CFC.concaveOn_log`
- `CFC.rpow_le_rpow`
- `CFC.log_le_log`
- the `PositiveLinearMap` and `CompletelyPositiveMap` structures

These do not prove the current axioms directly.  The current statements are
Jensen inequalities after applying an arbitrary positive subunital or unital
map on a matrix algebra.  The missing formal theorem is the
Hansen--Pedersen/Choi--Davis--Jensen passage from operator concavity to
positive-map Jensen.  The local file
`TNLean/Channel/Schwarz/OperatorJensenAux.lean` already contains part of the
finite-POVM compression route toward the concave real-power case.

For `posMap_rpow_convex_jensen`, Mathlib's
`CFC.Rpow.Order` still lists operator convexity of `rpow` on `[1, 2]` as a
TODO.  For `lieb_concavity_axiom`, no Mathlib theorem was found for Lieb's
joint concavity in the matrix-trace form used by TNLean.

For the two Beigi/CPSV parent-Hamiltonian axioms, no Mathlib material was
found for matrix product states, nearest-neighbor commuting Hamiltonian
ground-space classification, or the RFP--NNCPH bridge.  These remain
project-specific mathematical assumptions.

For the two entropy axioms, Mathlib 4.31 has classical information-theoretic
entropy material, but no finite-dimensional quantum von Neumann strong
subadditivity theorem and no Hayashi/Ruskai/Hayden--Jozsa--Petz--Winter
equality characterization in the form stated here.  These axioms remain
necessary until the quantum relative-entropy and Markov-decomposition
formalization is supplied locally or upstream.

The same audit was compared against the current non-Archive `sorry` surface.
The remaining proof placeholders are the three Lorentz-normal-form statements
in `TNLean/Channel/LorentzNormalForm.lean` and the cyclic contraction step in
`TNLean/MPS/Periodic/Overlap/Case3.lean`.  None is discharged by the eight
sanctioned axioms: the Lorentz-normal-form statements require coercivity,
compactness packaging, and the SL(2, C) Lorentz-orbit classification, while
the periodic-overlap statement requires the cyclic sector-contraction theorem.
Thus the axioms remain useful assumptions for their own theorem families, but
they do not give a direct Mathlib-4.31 replacement or a local shortcut for the
present `sorry`s.

This comparison was repeated after the alias-cleanup batch.  The conclusion is
unchanged: the axioms are not unused, and none supplies the missing cyclic
sector-contraction or Lorentz-normal-form ingredients.

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
  projection API where possible.  The exact local wrapper
  `LinearMap.IsSymmetricProjection.re_inner_nonneg` has been removed; uses now
  call `LinearMap.IsSymmetricProjection.isPositive` and
  `LinearMap.IsPositive.re_inner_nonneg_left` directly.
- Keep the Friedrichs-angle and martingale-type estimates local.
- Prefer `Submodule.projectionOnto` for new complement projections.

Applied martingale follow-up:

- The private helper `isPositive_smul_of_real_re_nonneg` in
  `TNLean/MPS/ParentHamiltonian/Martingale/Transport.lean` was removed.  The
  local-term averaging proof now uses Mathlib's
  `LinearMap.IsPositive.smul_of_nonneg` directly, with the scalar nonnegativity
  discharged by `positivity` under `ComplexOrder`.

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

Status: the finite-dimensional and finite-sum wrappers have been removed.

Completed replacements:

- `finrank_matrix_fin_eq_sq` by `Module.finrank_matrix`.
- `finrank_top_matrix_fin_eq_sq` by `Module.finrank_matrix` and top-submodule
  simplification.
- `dim_le_of_mulVec_injective` by direct uses of `Matrix.toLin'` and
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

The one-use private wrappers

- `norm_matToES_mul_le`
- `norm_matToES_rect_mul_le`

have been removed from `TNLean/Spectral/TransferOperatorGap.lean` and
`TNLean/Spectral/TransferOperatorGapRect.lean`.  The two Cauchy-Schwarz chains
now unfold the local `matToES` abbreviations at the call site and apply
Mathlib's `Matrix.frobenius_norm_mul` directly.

### Remaining axiom boundary recheck, 2026-06-19

The remaining non-Archive axioms were checked again against the Mathlib 4.31
checkout:

- `posMap_rpow_concave_jensen`
- `posMap_rpow_convex_jensen`
- `posMap_log_concave_jensen`
- `lieb_concavity_axiom`
- `Axioms.rfp_to_nncph_commute`
- `Axioms.beigi_nncph_to_rfp`
- `strong_subadditivity`
- `hayashi_ssa_equality_characterization`

Mathlib 4.31 provides useful inputs for the operator-convexity boundary,
notably `CFC.concaveOn_rpow`, `CFC.concaveOn_log`,
`PositiveLinearMap`, and `CompletelyPositiveMap`.  It does not yet provide the
Hansen-Pedersen positive-map Jensen theorem, operator convexity of `rpow` on
`[1,2]`, Lieb joint concavity, finite-dimensional quantum strong
subadditivity, the Hayashi equality characterization, or the Beigi
nearest-neighbor commuting-Hamiltonian ground-space theorem.  The local axioms
therefore remain load-bearing assumptions.

The current non-Archive `sorry` sites are in
`TNLean/Channel/LorentzNormalForm.lean` and
`TNLean/MPS/Periodic/Overlap/Case3.lean`.  These do not import the Beigi or
entropy axiom boundary as a direct missing step, and the operator-convexity
axioms do not match their current goals.  No present `sorry` was closed by the
remaining axioms in this recheck.

The present usefulness check is:

- `posMap_rpow_concave_jensen`, `posMap_rpow_convex_jensen`, and
  `posMap_log_concave_jensen`: useful for the Schwarz/operator-convexity
  family, but their conclusions are order inequalities for positive maps.
  They do not address the compactness/coercivity step in Lorentz normal form or
  the cyclic sector contraction in periodic overlap.
- `lieb_concavity_axiom`: useful for Ando--Lieb trace concavity.  Its trace
  inequality has no direct target among the current proof placeholders.
- `Axioms.rfp_to_nncph_commute` and `Axioms.beigi_nncph_to_rfp`: useful for the
  parent-Hamiltonian RFP--NNCPH equivalence.  They do not supply the sector
  phase-coboundary contraction in `Case3.lean`.
- `strong_subadditivity` and `hayashi_ssa_equality_characterization`: useful
  for the entropy/MPDO Markov-chain branch.  They do not enter the Lorentz
  normal form file or the periodic-overlap contraction.

A declaration-only recheck after the PEPS pass-through removal found the same
eight axiom declarations.  The Mathlib 4.31 scout found useful positive-map,
complete-positivity, and functional-calculus infrastructure, but no theorem
whose statement matches these eight axiom boundaries.

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

After fetching Mathlib 4.31 caches, the following early upgrade check was run
while the now-deleted `TNLean.Algebra.MatrixFunctionalCalculus` target still
existed:

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

A follow-up pass removed explicit uses of four exact scalar-instance aliases
from downstream proofs and then removed the abbreviations themselves from
`TNLean.Algebra.MatrixOperatorSpace`:

- `complexPosSMulMonoDef`
- `complexContinuousSMulReal`
- `matrixContinuousSMulReal`
- `matrixScalarTowerRealComplex`

The remaining semigroup proofs use the same structures directly through
`inferInstance`, including the fully explicit derivative arguments in
`TNLean.Channel.Semigroup.Basic`, `TNLean.Channel.Semigroup.Kernel`, and
`TNLean.Channel.Semigroup.Primitivity.Helpers`.

A further pass removed the local rectangular continuous-linear-map normed
structure wrappers from `TNLean.Spectral.GaugeConstruction`; the
finite-dimensional witness remains as a deprecated compatibility name:

- `instGCNormedAddCommGroupMatrixCLM`
- `instGCNormedRingMatrixCLM`
- `instGCSeminormedRingMatrixCLM`
- `instGCNormedAlgebraMatrixCLM`
- `instGCCompleteSpaceMatrixCLM`

Retained compatibility name:

- `instGCFiniteDimensionalMatrixCLM`

These were exact local wrappers around the continuous-linear-map normed-ring
and finite-dimensional-completeness infrastructure.  The spectral and
string-order proofs now use Mathlib's
`ContinuousLinearMap.toNormedAddCommGroup`,
`ContinuousLinearMap.toSeminormedRing`, `ContinuousLinearMap.toNormedRing`,
`ContinuousLinearMap.toNormedSpace`, and
`ContinuousLinearMap.toNormedAlgebra` directly, with local
`FiniteDimensional.complete` proofs where spectrum or power-decay lemmas need
completeness.

## Verification performed

The Mathlib cache was fetched for the 4.31 worktree.  An initial cache fetch
encountered a corrupted local archive; rerunning the forced cache command
succeeded.

The following focused checks succeeded under Mathlib 4.31 during the audit and
adaptation work:

```text
lake env lean TNLean/Algebra/GramMatrixLI.lean
lake env lean TNLean/Algebra/MatrixOperatorSpace.lean
lake build TNLean.Algebra.MatrixOperatorSpace
lake env lean TNLean/Channel/Semigroup/Basic.lean
lake env lean TNLean/Channel/Semigroup/Kernel.lean
lake env lean TNLean/Channel/Semigroup/Primitivity/Helpers.lean
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
lake env lean TNLean/Axioms/OperatorConvexity.lean --json
lake env lean TNLean/Analysis/OperatorConvexity.lean --json
lake env lean TNLean/Channel/Schwarz/OperatorMonotone.lean --json
lake env lean TNLean/Channel/Schwarz/OperatorConvexity.lean --json
lake env lean TNLean/Channel/Schwarz/AndoLieb.lean --json
lake build TNLean.Analysis.OperatorConvexity TNLean.Axioms.OperatorConvexity \
  TNLean.Channel.Schwarz.OperatorMonotone TNLean.Channel.Schwarz.OperatorConvexity \
  TNLean.Channel.Schwarz.AndoLieb -q --log-level=info
lake env lean TNLean/Algebra/MatrixAux.lean --json
lake env lean TNLean/Spectral/GaugeConstruction.lean --json
lake env lean TNLean/Spectral/TransferOperatorGapNT.lean --json
lake env lean TNLean/Spectral/TransferOperatorGapRect.lean
lake env lean TNLean/Spectral/PrimitiveOverlap.lean
lake env lean TNLean/Spectral/MPVOverlapDecay.lean
lake env lean TNLean/MPS/Symmetry/StringOrderDefs.lean
lake build TNLean.Spectral.GaugeConstruction TNLean.Spectral.TransferOperatorGap \
  TNLean.Spectral.TransferOperatorGapRect TNLean.Spectral.TransferOperatorGapNT \
  TNLean.Spectral.PrimitiveOverlap TNLean.Spectral.MPVOverlapDecay \
  TNLean.MPS.Symmetry.StringOrderDefs -q --log-level=info
lake env lean TNLean/Channel/Irreducible/Growth/OneStep.lean --json
lake env lean TNLean/Channel/Irreducible/Growth/Preservation.lean --json
lake env lean TNLean/Channel/Irreducible/Growth/KernelDescent.lean --json
lake env lean TNLean/Channel/Peripheral/GroupStructure.lean --json
lake env lean TNLean/Spectral/TransferOperatorGap.lean --json
lake env lean TNLean/Spectral/TransferOperatorGap.lean
lake env lean TNLean/Spectral/TransferOperatorGapRect.lean
lake env lean TNLean/PiAlgebra/CanonicalFormSepAux.lean --json
lake build TNLean.Algebra.MatrixAux TNLean.Spectral.GaugeConstruction \
  TNLean.Spectral.TransferOperatorGapNT TNLean.Spectral.TransferOperatorGap \
  TNLean.Channel.Irreducible.Growth.KernelDescent \
  TNLean.Channel.Peripheral.GroupStructure TNLean.PiAlgebra.CanonicalFormSepAux \
  -q --log-level=info
lake env lean TNLean/Spectral/QuantitativeGap.lean --json
lake env lean TNLean/MPS/Structure/PrimitivityBridge.lean --json
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
