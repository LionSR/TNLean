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
  finite-dimensional witness was removed with the other exact local wrappers.
- Two one-use Frobenius submultiplicativity wrappers in the transfer-operator
  gap files were removed.  The proofs now call Mathlib's
  `Matrix.frobenius_norm_mul` directly at the Hilbert-Schmidt estimate.
- The dissipative-drift semigroup proof now uses Mathlib's ball-free
  `NormedSpace.map_exp` theorem for continuous algebra homomorphisms.  The
  local exponential convergence-ball lemma and the old Lean 4.29 heartbeat
  adjustment are no longer needed.
- The rectangular Kraus-freedom proof now names the Euclidean-space
  inner-product structure explicitly by `PiLp.innerProductSpace`, removing a
  large local synthesis budget that was needed only to find this standard
  instance.
- The determinant-one unitary-channel characterization now has one Lean
  statement.  The duplicate `_of_channel` theorem had the same hypotheses and
  conclusion as `channelDet_norm_eq_one_iff_exists_unitaryChannel`, so the
  blueprint points directly to the latter.
- The Lindblad-form trace-constraint proof now uses Mathlib's
  `Matrix.ext_iff_trace_mul_right` directly.  The one-use local theorem
  `Matrix.eq_zero_of_forall_trace_mul_eq_zero` was removed from
  `TNLean/Channel/Semigroup/LindbladForm/TraceBridge.lean`.
- Further Lean 4.31 elaboration checks removed local heartbeat bounds from the
  POVM unitary-comparison proof, the irreducible-channel spectral-radius scalar
  proof, the semigroup perturbation derivative proof, and the common
  cyclic-sector data theorem.
- The periodic-MPS equivalence bundles now cite the chain-level relation laws
  directly.  Six local theorem declarations that only restated reflexivity,
  symmetry, and transitivity for the periodic abbreviations were removed.
- Two PEPS pass-through declarations were removed: a coarse-frame
  bond-positivity accessor that only exposed the structure field, and a one-use
  same-state restatement in the row-cut obstruction example.
- Three more PEPS example pass-through declarations were removed by inlining
  their immediate witnesses at the only proof sites where they were used.
- The Frobenius-square nonnegativity wrapper `MPSTensor.frobSq_nonneg` was
  removed; the two transfer estimates now unfold `frobSq` and use `sq_nonneg`.
- Two RFP/ZCL wrappers were removed: an unused MPDO implication method that
  repeated `MPOTensor.isRFP_iff_isZCL`, and a one-use cluster-example RFP fact.
- The unused elementary orthogonal-projection witnesses for `0` and `1` were
  removed.  Positivity of an orthogonal projection now passes through Mathlib's
  `IsStarProjection.nonneg` and `Matrix.nonneg_iff_posSemidef`.

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
- The `SO(3)` Euler-angle factorization in
  `TNLean/MPS/Examples/AKLTRotation.lean` remains local.  Mathlib 4.31 provides
  the special-orthogonal group interface, a two-dimensional membership
  characterization, and the `Complex.arg` trigonometric identities used by the
  local proof, but it does not provide a direct `SO(3)` Euler decomposition.
  Removing the theorem-level `maxHeartbeats` bound from `so3_euler_decomp`
  still times out at the default budget.

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
  by Mathlib's `map_smul` for the algebra equivalence.  The unused
  compatibility theorem was then removed.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_finCongr_symm_round` were
  removed from `TNLean/PEPS/EdgeGaugeFamily.lean`.  The only local transport
  site now uses a proof by simplifying `Matrix.reindexAlgEquiv` directly.  The
  unused compatibility theorem was then removed.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_gaugeConj` were removed.  The
  only use in `TNLean/PEPS/TorusWitnessTransport.lean` now uses `map_mul`,
  `map_inv`, and `glReindex_coe` directly.  The unused compatibility theorem
  was then removed.
- Explicit uses of `TNLean.PEPS.reindexAlgEquiv_transpose` were removed.  Its
  users now call Mathlib's `Matrix.transpose_reindex` directly, with local
  `change` steps where the gauge-applied bond dimension is definitionally equal
  to the original one.  The unused compatibility theorem was then removed.
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

Additional channel cleanup:

- The private scalar pass-through theorem `star_I_eq_neg_I` was removed from
  `TNLean/Channel/WolfProps.lean`.  The two polarization proofs now cite
  `Complex.conj_I` directly as a local proof term inside `simp only`, leaving
  the other conjugates in the scalar identity untouched.

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

A later pass also reduced the local matrix-instance blocks in
`TNLean/Analysis/OperatorConvexity.lean`,
`TNLean/Axioms/OperatorConvexity.lean`,
`TNLean/Channel/Schwarz/OperatorConvexity.lean`, and
`TNLean/Channel/Schwarz/OperatorMonotone.lean`.  The files still keep the two
local normed instances that the CFC notation requires for the concrete matrix
norm, but the local `CStarRing`, `PartialOrder`, `StarOrderedRing`, and
`CStarAlgebra` pass-through aliases are no longer needed; Mathlib 4.31's
matrix order and C-star instances are used directly.

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

Applied wrapping-window follow-up:

- The two theorem-level `maxHeartbeats` bounds in
  `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean` were removed.  Under Lean
  4.31, both the trace-rotation extraction lemma `wrapping_window_matEq` and
  the boundary commutation theorem `boundary_matrix_commutes` elaborate under
  the default heartbeat budget.

Focused check:

```bash
lake build TNLean.MPS.ParentHamiltonian.WrappingWindow -q --log-level=info
```

Applied projection follow-up:

- `TNLean/Channel/Irreducible/Basic.lean` now bridges the local matrix
  predicate `IsOrthogonalProjection` with Mathlib's `IsStarProjection`.
  The complement theorem `IsOrthogonalProjection.one_sub` is proved through
  Mathlib's `IsStarProjection.one_sub`.
- The unused elementary witnesses that `0` and `1` are orthogonal projections
  were removed.  The proof that an orthogonal projection is positive
  semidefinite now uses
  `IsStarProjection.nonneg` followed by `Matrix.nonneg_iff_posSemidef`.
- Duplicate complement-projection proofs were removed from
  `TNLean/MPS/Irreducible/Adjoint.lean`,
  `TNLean/Channel/Irreducible/FromSpectral.lean`, and
  `TNLean/Channel/Semigroup/ReducibleQDS/Defs.lean`; downstream uses now call
  the single foundational lemma.

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
- Trace-pairing wrappers only when they are part of TNLean's public
  mathematical vocabulary.  Private equality-form wrappers should use
  `Matrix.ext_iff_trace_mul_left` and `Matrix.ext_iff_trace_mul_right`
  directly.

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

Status: partially applied.

This is one of the most promising local developments to shrink.  Mathlib's
Frobenius norm is now the foundation for matrix Hilbert-Schmidt arguments:
`frobSq` is a squared Mathlib Frobenius norm, and the entrywise sum formula is
kept as `frobSq_eq_sum` for trace and finite-sum arguments.  The local squared
norm remains only as a convenience wrapper for downstream transfer estimates.
The separate nonnegativity wrapper `MPSTensor.frobSq_nonneg` has been removed:
the needed fact is exactly `sq_nonneg ‖X‖` after unfolding `frobSq`.

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

The Mathlib 4.31 pass also removes local synthesis-budget bounds from the
square transfer-gap theorem, the rectangular transfer-gap theorem, the
rectangular non-translation-invariant gap theorem, and the non-rectangular
non-translation-invariant spectral-radius extraction.  These proofs now name the
continuous-linear-map normed structures directly enough that the former local
`synthInstance.maxHeartbeats` adjustments are no longer needed.

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

### Small scalar lemma cleanup, 2026-06-19

The peripheral-spectrum file contained one local scalar lemma:

- `ne_zero_of_norm_eq_one`

It was removed.  Its internal uses now call Mathlib's `norm_ne_zero_iff`
directly at the two root-of-unity cancellation steps and the two semigroup
primitivity cancellation steps.

The Schwarz non-completely-positive example also had two private numeral facts:

- `complex_one_half_nonneg`
- `complex_one_quarter_nonneg`

These were removed.  The four positivity uses now discharge the complex
nonnegativity side condition directly by `norm_num [Complex.nonneg_iff]`.

Focused check:

```bash
lake build TNLean.Channel.Peripheral.Spectrum \
  TNLean.Channel.Semigroup.Primitivity.Helpers \
  TNLean.Channel.Schwarz.SchwarzNotCP -q --log-level=info
```

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

A later pass also removed the private convergence-ball helper `mem_exp_ball`
from `TNLean.Channel.Semigroup.Basic`.  The semigroup law for
`expSemigroupCLM` now calls Mathlib's ball-free
`NormedSpace.exp_add_of_commute` directly.

A subsequent dissipative-drift pass removed the analogous private
convergence-ball lemma from `TNLean.Channel.Semigroup.Dissipative`.  The
left- and right-multiplication exponential identities now use Mathlib's
ball-free theorem `NormedSpace.map_exp` for continuous algebra homomorphisms.
Lean 4.31 also elaborates the commuting-exponential step in this file without
the former local `synthInstance.maxHeartbeats` adjustment.

A later semigroup perturbation pass removed the old local heartbeat bound around
`hasDerivAt_semigroup_product`.  The CLM-valued product-derivative proof now
elaborates under the default Lean 4.31 budget.  The same pass removed two inert
proof-normalization steps from `TNLean.Channel.Semigroup.LindbladForm.Basic`
that Lean 4.31 reports as unused.

A subsequent check of `TNLean.Channel.Semigroup.Basic` removed the four
remaining theorem-level heartbeat bounds in that file.  Lean 4.31 now
elaborates the exponential-semigroup derivative, the one-sided differentiability
lemma for continuous semigroups, the exponential-form theorem, and generator
uniqueness under the default heartbeat budget.

In `TNLean.Channel.POVM.Uniqueness`, the Gram-matrix comparison theorem
`exists_unitary_mul_eq_of_conjTranspose_mul_eq` no longer needs its old local
heartbeat bound.  Its proof already names the Euclidean-space inner-product and
finite-dimensional structures explicitly, so Lean 4.31 elaborates the
partial-isometry argument directly.

In `TNLean.Channel.KrausFreedom`, the Euclidean-space inner-product instance is
now given explicitly by `PiLp.innerProductSpace (fun _ : ι => ℂ)`.  This removes
the former large local synthesis budget around the cached instance and makes the
finite-dimensional Hilbert-space structure used in the rectangular isometry
argument explicit.  The remaining local `maxHeartbeats` bound around the
partial-isometry extension theorem was retested under Lean 4.31 and is still
needed for elaboration.

In `TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData`, the common
positive-blocking-length cyclic-sector theorem now elaborates under the default
Lean 4.31 heartbeat budget.  The local theorem-level `maxHeartbeats` override
and its comment were removed.

In `TNLean.Channel.Schwarz.PositiveOnAbelian.Characterization`, the two
simultaneous-diagonalization results no longer need theorem-level heartbeat
bounds.  Lean 4.31 elaborates both
`blockForm_nonneg_of_scalarPSD_of_commuting` and
`quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` under the default
budget.

Focused check:

```bash
lake build TNLean.Channel.Schwarz.PositiveOnAbelian.Characterization -q --log-level=info
```

The determinant-one unitary-channel theorem no longer has the duplicate
`channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel` restatement.  The
statement already assumes `IsChannel T`, so the removed theorem was an exact
pass-through layer.  The corresponding blueprint entry now cites only
`channelDet_norm_eq_one_iff_exists_unitaryChannel`.

A further pass removed the local rectangular continuous-linear-map normed
structure wrappers from `TNLean.Spectral.GaugeConstruction`:

- `instGCNormedAddCommGroupMatrixCLM`
- `instGCNormedRingMatrixCLM`
- `instGCSeminormedRingMatrixCLM`
- `instGCNormedAlgebraMatrixCLM`
- `instGCCompleteSpaceMatrixCLM`
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

The local spectral-radius extraction theorems in
`TNLean.Spectral.TransferOperatorGap`, `TNLean.Spectral.TransferOperatorGapRect`,
and `TNLean.Spectral.TransferOperatorGapNT` were retested under Lean 4.31.  The
square transfer-gap theorem, the rectangular transfer-gap theorem, the
Perron--Frobenius gauge extraction in the non-translation-invariant file, and
the non-rectangular non-translation-invariant spectral-radius extraction no
longer need their previous local bounds.

Focused check for the final non-translation-invariant removal:

```bash
lake build TNLean.Spectral.TransferOperatorGapNT -q --log-level=info
```

The scalar spectral-radius identity `spectralRadius_smul` in
`TNLean.Channel.Irreducible.SpectralRadius` also no longer needs a local
`synthInstance.maxHeartbeats` bound for the matrix-endomorphism continuous
linear-map completeness search.

### Fixed-point Wedderburn decomposition

Removed pass-through accessor:

- `Kraus.wedderburnBlockDims_sum_le`

This theorem merely returned the `dim_le` field from an
`IsWedderburnBlockDecomp` witness.  The Wedderburn--Artin existence theorems
and the bundled decomposition structure are unchanged; callers should use
`w.dim_le` directly when they have a decomposition witness `w`.

### Wielandt rank-one products

Removed unused local convenience wrappers:

- `MPSTensor.matrix_in_cumulativeSpan`
- `MPSTensor.one_eq_evalWord_nil`
- `MPSTensor.wordSpan_generates_full_algebra`

The first and third merely restated `cumulativeSpan_eq_top`, while the second
was just `evalWord_nil`.  No Lean or blueprint declaration referred to them.

### Complex scalar idempotents, 2026-06-19

Removed the local scalar lemma:

- `MPSTensor.mul_self_eq_self_or_eq_one`

This theorem specialized Mathlib's general idempotent-element result
`IsIdempotentElem.iff_eq_zero_or_one` to complex numbers.  The three local
uses in invariant-subspace splitting and cyclic-sector compression now call
the Mathlib theorem directly.

### Complex nonnegative cone and norm, 2026-06-19

Removed private local proofs of standard complex-order facts:

- `isClosed_complex_nonneg`
- `norm_of_complex_nonneg`
- `isClosed_complex_nonneg_generic`

Mathlib 4.31 supplies the ordered-topology instance for the complex order under
`ComplexOrder`, so the closedness proof is now
`isClosed_le continuous_const continuous_id`.  For nonnegative complex numbers,
the bounded-density-matrix argument now derives the real norm identity from
`Complex.norm_of_nonneg'`.

### Commuting idempotent products, 2026-06-19

Removed the local linear-map specialization:

- `LinearMap.comp_idem_of_comm_idem`

The theorem was exactly `IsIdempotentElem.mul_of_commute` for endomorphisms
written with composition notation.  The commuting-parent-Hamiltonian proof now
uses the Mathlib theorem directly.

### Projection-complement idempotent algebra, 2026-06-19

The projection-triangular trace file originally carried local
projection-complement lemmas whose statements were exact specializations of
Mathlib's general idempotent-complement API:

- `IsIdempotentElem.mul_one_sub_self`
- `IsIdempotentElem.one_sub_mul_self`
- `IsIdempotentElem.one_sub`

The pass-through names have now been removed:

- `MPSTensor.proj_add_projCompl`
- `MPSTensor.proj_mul_projCompl`
- `MPSTensor.projCompl_mul_proj`
- `MPSTensor.projCompl_mul_projCompl`

The internal projection-triangular trace proofs call `simp` or the Mathlib
idempotent-complement theorems directly.

### Semigroup projection-complement cleanup, 2026-06-19

The reducible-QDS generator-compression file contained two public
projection-complement theorems:

- `orthogonalProjection_complement_mul`
- `orthogonalProjection_mul_complement`

They were exact matrix-projection specializations of Mathlib's general
idempotent identities:

- `IsIdempotentElem.one_sub_mul_self`
- `IsIdempotentElem.mul_one_sub_self`

No blueprint entry or non-Archive Lean declaration outside the semigroup proof
cluster referred to the local theorem names.  They have therefore been removed,
and the generator-compression and relaxation-condition proofs now call the
Mathlib idempotent-complement theorems directly.

The same pass also replaced the private scalar calculation in
`not_isNontrivialProjection_of_eq_smul_one`: the proof now uses
`IsIdempotentElem.iff_eq_zero_or_one` instead of factoring `c * (c - 1)`.

Focused check:

```bash
lake build TNLean.Channel.Semigroup.ReducibleQDS.GeneratorCompression \
  TNLean.Channel.Semigroup.RelaxationConditions -q --log-level=info
```

### Lindblad-form heartbeat retest, 2026-06-19

`TNLean.Channel.Semigroup.LindbladForm.EulerStep` no longer needs its three
theorem-level heartbeat bounds.  Lean 4.31 now elaborates the conditional
complete-positivity direction of Wolf Proposition 7.3, the one-step Kraus-map
expansion, and the CLM exponential-remainder estimate under the default
heartbeat budget.

The same retest removed the two theorem-level heartbeat bounds from
`TNLean.Channel.Semigroup.LindbladForm.TraceBridge`: the CLM trace-constant
lemma and the right-derivative trace-annihilation theorem also elaborate under
the default budget.

Focused check:

```bash
lake build TNLean.Channel.Semigroup.LindbladForm.EulerStep \
  TNLean.Channel.Semigroup.LindbladForm.TraceBridge -q --log-level=info
```

### Reducible-QDS subsequence heartbeat retest, 2026-06-19

`TNLean.Channel.Semigroup.ReducibleQDS.SubsequenceAnalysis` no longer needs its
theorem-level heartbeat bound around the subsequence-limit argument
`generator_vanishes_at_limit`.  Lean 4.31 elaborates the Taylor-remainder
normalization step under the default heartbeat budget.

Focused check:

```bash
lake build TNLean.Channel.Semigroup.ReducibleQDS.SubsequenceAnalysis -q --log-level=info
```

### Further projection-complement proof reductions, 2026-06-19

A second pass replaced remaining handwritten complement identities of the form
`P * (1 - P) = 0`, `(1 - P) * P = 0`, and `(1 - P) * (1 - P) = 1 - P`
by Mathlib's idempotent API, without changing any theorem statements.

The affected files are:

- `TNLean/Channel/MaximallyEntangled.lean`
- `TNLean/Channel/Irreducible/FromSpectral.lean`
- `TNLean/Channel/Irreducible/Growth/Exponential.lean`
- `TNLean/Channel/Irreducible/Growth/OneStep.lean`
- `TNLean/Channel/Irreducible/Similarity.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS/FixedDensity.lean`
- `TNLean/MPS/Core/CPPrimitive.lean`
- `TNLean/MPS/Irreducible/FixedPointProjection.lean`
- `TNLean/MPS/Irreducible/FormII.lean`
- `TNLean/QPF/PosDef.lean`

The public maximally-entangled projection lemmas remain, because they name the
local Choi--Jamiolkowski object `omegaProj`.  Their proofs now reduce the
idempotence theorem `omegaProj_mul_self` through
`IsIdempotentElem.one_sub_mul_self`, `IsIdempotentElem.mul_one_sub_self`, and
`IsIdempotentElem.one_sub`.

Focused check:

```bash
lake build TNLean.QPF.PosDef TNLean.Channel.MaximallyEntangled \
  TNLean.Channel.Irreducible.Growth.OneStep \
  TNLean.Channel.Irreducible.Growth.Exponential \
  TNLean.Channel.Irreducible.FromSpectral TNLean.Channel.Irreducible.Similarity \
  TNLean.Channel.Semigroup.ReducibleQDS.FixedDensity \
  TNLean.MPS.Core.CPPrimitive TNLean.MPS.Irreducible.FormII \
  TNLean.MPS.Irreducible.FixedPointProjection -q --log-level=info
```

### Projection-triangular pass-through removal, 2026-06-19

The internal `ProjectionTriangularTrace` proof no longer introduces local
abbreviating lemmas for `P + (1 - P) = 1` or the three idempotent-complement
identities.  The proof now uses `simp`,
`IsIdempotentElem.mul_one_sub_self`,
`IsIdempotentElem.one_sub_mul_self`, and `IsIdempotentElem.one_sub` at each
use site.  This removes a small pass-through layer without changing the main
statements:

- `MPSTensor.lowerZero_evalWord`
- `MPSTensor.evalWord_diagPart_eq`
- `MPSTensor.trace_eq_trace_diag_of_proj`
- `MPSTensor.sameMPV_diagPart_of_lowerZero`

Focused check:

```bash
lake build TNLean.Algebra.ProjectionTriangularTrace -q --log-level=info
```

### Periodic relation-law pass-through removal, 2026-06-19

`PeriodicMPSTensor.SameState` and `PeriodicMPSTensor.GaugeEquiv` are
abbreviations for the corresponding `MPSChainTensor` relations.  The periodic
reflexivity, symmetry, and transitivity theorems therefore added no new
periodic-MPS content.  The equivalence bundles now cite the chain-level
relation laws directly, while retaining the blueprint-facing bundle names:

- `MPSTensor.PeriodicMPSTensor.instEquivalenceSameState`
- `MPSTensor.PeriodicMPSTensor.instEquivalenceGaugeEquiv`

Removed declarations:

- `MPSTensor.PeriodicMPSTensor.SameState.refl`
- `MPSTensor.PeriodicMPSTensor.SameState.symm`
- `MPSTensor.PeriodicMPSTensor.SameState.trans`
- `MPSTensor.PeriodicMPSTensor.GaugeEquiv.refl`
- `MPSTensor.PeriodicMPSTensor.GaugeEquiv.symm`
- `MPSTensor.PeriodicMPSTensor.GaugeEquiv.trans`

Focused check:

```bash
lake build TNLean.MPS.Periodic.Defs -q --log-level=info
```

### PEPS accessor pass-through removal, 2026-06-19

Two PEPS declarations had no independent mathematical content and no blueprint
references:

- `TNLean.PEPS.CoarseBlockingFrame.coarseTensor_pos_bondDim` only exposed the
  structure field `CoarseBlockingFrame.pos_coarseBondDim`.  The coarse
  three-site and normal-bond-dimension proofs now use the field directly.
- `TNLean.PEPS.sameMPV_Aunits_Bunits` only applied
  `gaugeEquiv_Aunits_Bunits.sameMPV` at one row-cut obstruction proof site.
  That proof now calls the gauge-invariance theorem directly.

Focused check:

```bash
lake build TNLean.PEPS.RegionBlock.CoarseThreeSite11 \
  TNLean.PEPS.NormalBondDimension TNLean.PEPS.TorusRowColumnReductionObstruction \
  -q --log-level=info
```

### PEPS example pass-through removal, 2026-06-19

The follow-up PEPS scan found three exported example declarations that named
only immediate proof steps and had no blueprint references:

- `TNLean.PEPS.middle_injective` in
  `TNLean/PEPS/PhysicalToVirtualCounterexample.lean` was exactly
  `linearIndependent_empty_type`, used once as the middle-injectivity field of
  the three-site counterexample.
- `TNLean.PEPS.Aunits_isNBlkInjective` in
  `TNLean/PEPS/TorusRowColumnReductionObstruction.lean` was the direct
  one-block injectivity consequence of `Aunits_isInjective`.
- `TNLean.PEPS.Bunits_isNBlkInjective` in the same file was the corresponding
  one-block consequence after transporting injectivity along
  `gaugeEquiv_Aunits_Bunits`.

The remaining proofs now use these witnesses locally at the structure field or
route-specialization site, so no additional public theorem names are exported.

Focused check:

```bash
lake build TNLean.PEPS.PhysicalToVirtualCounterexample \
  TNLean.PEPS.TorusRowColumnReductionObstruction -q --log-level=info
```

### PEPS two-injective heartbeat retest, 2026-06-19

In `TNLean.PEPS.TwoInjectiveComparison.Basic`, the operator-Schmidt bond-gauge
extraction theorem now elaborates under the default Lean 4.31 heartbeat budget.
The local theorem-level `maxHeartbeats` override and its comment were removed.
The diagonal-family lemma in
`TNLean.Channel.Schwarz.PositiveOnAbelian.Consequences` was retested in the same
pass and still times out at the default budget during the simultaneous
diagonalization proof, so its local heartbeat bound remains.

### Trace-pairing extensionality, 2026-06-19

Mathlib 4.31 has equality-form trace-pairing extensionality lemmas:

- `Matrix.ext_iff_trace_mul_left`
- `Matrix.ext_iff_trace_mul_right`

The blueprint-facing theorem `Matrix.trace_mul_right_eq_zero_iff` is retained,
because it is a named TNLean statement used in the MPS trace-pairing chapter.
Its proof now uses `Matrix.ext_iff_trace_mul_right` rather than expanding
matrix entries by hand.

Several equality proofs no longer pass through the artificial subtraction
step `M - N = 0`.  They now apply the Mathlib equality-form theorem directly:

- `MPSTensor.internal_products_eq`
- `MPSTensor.external_products_eq`
- `MPSTensor.eq_of_trace_mul_evalWord_eq`
- `eq_of_trace_pairing_span` in `TNLean.PEPS.CycleMPSChainArc`

The two private `eq_of_trace_mul_left_eq` helpers in the PEPS overlap
insertion files were removed; their use sites now call
`Matrix.ext_iff_trace_mul_left` directly.

The Lindblad-form trace bridge also no longer exports the one-use theorem
`Matrix.eq_zero_of_forall_trace_mul_eq_zero`: the GKSL trace-constraint proof
uses `Matrix.ext_iff_trace_mul_right` directly at the equality step.

### Deprecation-policy exceptions

The usual convention in `docs/MATHLIB_style.md` is to keep a public
declaration as `@[deprecated]` before deleting it.  This audit records the
exceptions made in this Mathlib-4.31 cleanup.  In each case below, the removed
name had no independent mathematical content: it either repeated a statement
already present under the canonical name, exposed a field projection from a
bundled structure, or named a local proof step that is now written directly at
its use site.  All non-Archive uses in TNLean were already absent or were
rewritten in this PR, and no blueprint entry cites these names.

No compatibility declaration is retained for the following exact
pass-throughs:

- `complexPosSMulMonoDef`, `complexContinuousSMulReal`,
  `matrixContinuousSMulReal`, and `matrixScalarTowerRealComplex`.  These were
  abbreviations for standard scalar structures; the remaining proofs use the
  corresponding structures by inference.
- `IsPrimitiveMPS.spectral_gap`, `spectral_gap_of_injective`, and
  `uniform_spectral_gap_of_finite_lt_one`.  These were already deprecated
  aliases whose internal call sites had moved to the canonical theorem names.
- `channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel`.  This was the
  same theorem as `channelDet_norm_eq_one_iff_exists_unitaryChannel`, with the
  same channel hypothesis and conclusion.
- `MPSTensor.isOrthogonalProjection_one_sub`.  The replacement is the general
  theorem `IsOrthogonalProjection.one_sub`.
- `Kraus.wedderburnBlockDims_sum_le`.  This only returned the field `w.dim_le`
  from an `IsWedderburnBlockDecomp` witness.
- `TNLean.PEPS.reindexAlgEquiv_smul`,
  `TNLean.PEPS.reindexAlgEquiv_finCongr_symm_round`,
  `TNLean.PEPS.reindexAlgEquiv_gaugeConj`, and
  `TNLean.PEPS.reindexAlgEquiv_transpose`.  The remaining proofs use the
  algebra-equivalence identities (`map_smul`, `map_mul`, `map_inv`), the
  `glReindex` coercion theorem, a direct simplification of
  `Matrix.reindexAlgEquiv`, or `Matrix.transpose_reindex`.
- `instGCFiniteDimensionalMatrixCLM`.  The finite-dimensional witness is now
  constructed locally from `Module.End.toContinuousLinearMap`.
- `MPSTensor.matrix_in_cumulativeSpan`, `MPSTensor.one_eq_evalWord_nil`, and
  `MPSTensor.wordSpan_generates_full_algebra`.  These were immediate
  restatements of `cumulativeSpan_eq_top` or `evalWord_nil`.
- `MPSTensor.mul_self_eq_self_or_eq_one`.  This was the complex-number
  specialization of `IsIdempotentElem.iff_eq_zero_or_one`.
- `LinearMap.comp_idem_of_comm_idem`.  This was the endomorphism-composition
  specialization of `IsIdempotentElem.mul_of_commute`.
- `orthogonalProjection_complement_mul` and
  `orthogonalProjection_mul_complement`.  These were the matrix-projection
  specializations of `IsIdempotentElem.one_sub_mul_self` and
  `IsIdempotentElem.mul_one_sub_self`.
- `MPSTensor.PeriodicMPSTensor.SameState.refl`,
  `MPSTensor.PeriodicMPSTensor.SameState.symm`,
  `MPSTensor.PeriodicMPSTensor.SameState.trans`,
  `MPSTensor.PeriodicMPSTensor.GaugeEquiv.refl`,
  `MPSTensor.PeriodicMPSTensor.GaugeEquiv.symm`, and
  `MPSTensor.PeriodicMPSTensor.GaugeEquiv.trans`.  These were exact
  restatements of the chain-level relation laws for the periodic abbreviations.
- `TNLean.PEPS.CoarseBlockingFrame.coarseTensor_pos_bondDim`.  This only
  returned the `pos_coarseBondDim` field from a `CoarseBlockingFrame`.
- `TNLean.PEPS.sameMPV_Aunits_Bunits`.  This was a one-use application of
  `gaugeEquiv_Aunits_Bunits.sameMPV`.
- `TNLean.PEPS.middle_injective`.  This was the empty-index linear-independence
  witness `linearIndependent_empty_type` for one example structure field.
- `TNLean.PEPS.Aunits_isNBlkInjective` and
  `TNLean.PEPS.Bunits_isNBlkInjective`.  These were one-use consequences of the
  standard one-block injectivity theorem.
- `MPSTensor.frobSq_nonneg`.  This was the immediate square-nonnegativity fact
  for the definition `frobSq X = ‖X‖ ^ 2`.
- `MPOTensor.IsRFP.isZCL`.  This was an unused implication method repeating the
  blueprint-facing equivalence `MPOTensor.isRFP_iff_isZCL`.
- `MPSTensor.clusterBlocked_isRFP`.  This was a one-use restatement of the
  blueprint-facing theorem `MPSTensor.clusterBlocked_transferMap_idempotent`.

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
lake build TNLean.Channel.Semigroup.Dissipative -q --log-level=info
lake build TNLean.Channel.KrausFreedom -q --log-level=info
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
lake build TNLean.Analysis.OperatorConvexity TNLean.Axioms.OperatorConvexity \
  TNLean.Channel.Schwarz.OperatorConvexity TNLean.Channel.Schwarz.OperatorMonotone \
  -q --log-level=info
lake build TNLean.Channel.WolfProps -q --log-level=info
lake build TNLean.Channel.Irreducible.Basic TNLean.MPS.Irreducible.Adjoint \
  TNLean.Channel.Irreducible.FromSpectral TNLean.Channel.Semigroup.ReducibleQDS.Defs \
  TNLean.MPS.Periodic.SectorIrreducibility.HLiftCore -q --log-level=info
lake env lean TNLean/Algebra/MatrixAux.lean --json
lake env lean TNLean/Spectral/GaugeConstruction.lean --json
lake build TNLean.Algebra.ProjectionTriangularTrace -q --log-level=info
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
lake build TNLean.Algebra.TracePairing TNLean.MPS.Chain.TensorEquality \
  TNLean.PEPS.CycleMPSWordTransport TNLean.PEPS.CycleMPSChainArc \
  TNLean.PEPS.CycleMPSOverlapInsertion TNLean.PEPS.CycleMPSChainOverlapWindow \
  TNLean.PEPS.CycleMPSChainOverlapInsertion -q --log-level=info
lake build TNLean.Channel.Semigroup.ReducibleQDS.GeneratorCompression \
  TNLean.Channel.Semigroup.RelaxationConditions -q --log-level=info
lake build TNLean.QPF.PosDef TNLean.Channel.MaximallyEntangled \
  TNLean.Channel.Irreducible.Growth.OneStep \
  TNLean.Channel.Irreducible.Growth.Exponential \
  TNLean.Channel.Irreducible.FromSpectral TNLean.Channel.Irreducible.Similarity \
  TNLean.Channel.Semigroup.ReducibleQDS.FixedDensity \
  TNLean.MPS.Core.CPPrimitive TNLean.MPS.Irreducible.FormII \
  TNLean.MPS.Irreducible.FixedPointProjection -q --log-level=info
```

### Semigroup primitivity heartbeat retest, 2026-06-19

`TNLean.Channel.Semigroup.Primitivity.Basic` no longer needs its local heartbeat
bound around the spectral-mapping theorem
`eigenvalue_exp_of_eigenvalue_generator`.  Lean 4.31 elaborates the
`spectrum.exp_mem_exp` argument for the finite-dimensional CLM algebra under
the default heartbeat budget.

Focused check:

```bash
lake build TNLean.Channel.Semigroup.Primitivity.Basic -q --log-level=info
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

## Additional trace-pairing use-site cleanup, 2026-06-19

Mathlib's equality-form trace-pairing theorem
`Matrix.ext_iff_trace_mul_right` now replaces the remaining zero-difference
trace-pairing conversions in the channel layer:

- `TNLean/Channel/KrausRepresentation.lean`
- `TNLean/Channel/KrausFreedom.lean`
- `TNLean/Channel/Determinant/UnitaryCharacterization.lean`

The affected proofs now establish matrix equality directly by comparing
`trace (A * X)` against all test matrices `X`, rather than proving
`trace ((A - B) * X) = 0` and then invoking the local zero-form trace-pairing
wrapper.

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
