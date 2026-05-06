/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.BlockDiagonalCommutant.ProjectionSpan
import TNLean.MPS.CanonicalForm.Assembly.NormalityChain
import TNLean.MPS.BNT.Construction
import TNLean.MPS.MPDO.BiCFDerivation
import TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Block-diagonal commutants from sector projections

This file isolates the algebraic part of the block-diagonal commutant argument
for the parent-Hamiltonian block decomposition. If the sector projections of a
dependent direct sum lie in the span of a family of matrices and a boundary
matrix commutes with that family, then it
commutes with the projections and hence has no off-block entries.

The file also proves a finite-span reduction: if the simultaneous block word
tuples span the full product algebra, then the sector projections lie in the
finite word span of the assembled tensor.  The remaining paper-level CF/BNT input
is to derive that product-word span from the separated canonical-form/BNT
hypotheses.  Once the projection-span input is available,
`MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan` turns long-word
commutation of the assembled boundary matrix into block diagonality.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Finite product-word span gives the projection-span input for the assembled tensor.

Assume that the simultaneous length-`m` word evaluations
`ω ↦ (k ↦ evalWord (A k) (List.ofFn ω))` span the full product algebra of the
blocks.  If all assembly weights are nonzero, then after pulling the length-`m`
word products of `toTensorFromBlocks μ A` back to the dependent direct-sum basis,
their span contains every sector projection.

The remaining paper-level CF/BNT task is to prove the displayed product-word span
hypothesis from the separated canonical-form/BNT assumptions. -/
theorem blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {m : ℕ}
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hSpan : Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ))) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) := by
  classical
  intro k
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  have hproj :
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.blockDiagonal' fun j : Fin r =>
            (μ j) ^ m • evalWord (A j) (List.ofFn ω)) := by
    exact Matrix.blockProjection_mem_span_blockDiagonal'_of_pi_span_eq_top
      (n := fun k : Fin r => Fin (dim k))
      (T := fun ω : Fin m → Fin d => fun j : Fin r => evalWord (A j) (List.ofFn ω))
      (c := fun j : Fin r => (μ j) ^ m)
      (fun j => pow_ne_zero m (hμ j)) hSpan k
  have hgen : (fun ω : Fin m → Fin d =>
        Matrix.reindex e.symm e.symm
          (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) =
      (fun ω : Fin m → Fin d =>
        Matrix.blockDiagonal' fun j : Fin r =>
          (μ j) ^ m • evalWord (A j) (List.ofFn ω)) := by
    funext ω
    rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]
    ext x y
    simp [e, Matrix.reindex_apply]
  change Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
    Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
      Matrix.reindex e.symm e.symm
        (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω)))
  rw [hgen]
  exact hproj

/-- `WordTupleSpanTop` spelling of
`blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top`. -/
theorem blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {m : ℕ}
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hSpan : WordTupleSpanTop A m) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) := by
  exact blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
    (d := d) (dim := dim) μ A hμ (by simpa [WordTupleSpanTop, wordTuple] using hSpan)

/-- Reindexed word-span version of the block-diagonal commutant criterion.

Let `B` be a tensor whose bond space is the reindexed direct sum
`Fin (∑ k, dim k)`.  Pull all length-`m` word products and the boundary matrix
back to the dependent `Σ`-indexed direct sum via `finSigmaFinEquiv.symm`.  If the
block projections lie in the span of these pulled-back word products, then any
matrix on the assembled bond space commuting with all length-`m` word products
pulls back to a block-diagonal matrix.

For `B = toTensorFromBlocks μ A`, the pulled-back word products are the matrices
`Matrix.blockDiagonal' (fun k => (μ k)^m • evalWord (A k) (List.ofFn ω))` by
`evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal`. -/
theorem isBlockDiagonal'_of_commutes_reindexed_wordSpan
    (B : MPSTensor d (∑ k : Fin r, dim k)) {m : ℕ}
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord B (List.ofFn ω))))
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord B (List.ofFn ω) = evalWord B (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  classical
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  apply Matrix.isBlockDiagonal'_of_commutes_span_blockProjection
    (n := fun k : Fin r => Fin (dim k))
    (S := fun ω : Fin m → Fin d => Matrix.reindex e.symm e.symm (evalWord B (List.ofFn ω)))
    hProj
  intro ω
  have h := congrArg (Matrix.reindex e.symm e.symm) (hComm ω)
  simpa [e, Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

/-- Assembled-tensor commutant criterion using a finite product-word span
hypothesis instead of an explicit projection-span hypothesis.

The hypothesis says that the simultaneous block word evaluations of length `m`
span the full product algebra.  The previous projection-span lemma turns this
into the sector-projection input required by
`isBlockDiagonal'_of_commutes_reindexed_wordSpan`. -/
theorem isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {m : ℕ}
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hSpan : Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)))
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  exact isBlockDiagonal'_of_commutes_reindexed_wordSpan
    (B := toTensorFromBlocks (d := d) (μ := μ) A)
    (blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
      (d := d) (dim := dim) μ A hμ hSpan)
    hComm

/-- Canonical-form/BNT data plus finite block-selector words give full product-word span.

The remaining paper-level separation step is the construction of the selector words
from the BNT non-equivalence hypothesis. Once those selectors are available,
canonical-form injectivity supplies a one-letter prefix spanning the selected
block algebra, and concatenating prefix and selector words spans the whole
product algebra. -/
theorem wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    WordTupleSpanTop A (1 + S) := by
  refine wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    (A := A) (L := 1) (S := S) ?_ hSel
  intro k
  exact isNBlkInjective_one_of_isInjective (hCF.toHasInjectiveBlocks.block_injective k)

/-- Canonical-form/BNT data plus pairwise block-separating word polynomials give
full product-word span.

The pairwise hypotheses ask only for a word polynomial separating one ordered
pair of distinct blocks at a time.  The finite selector assembly in
`hasBlockSelectorWords_of_pairBlockSeparatingWords` turns these pairwise
separators into full block selectors, and the selector-word reduction then gives
product-word span. -/
theorem wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords μ A hCF
    (hasBlockSelectorWords_of_pairBlockSeparatingWords A hPair)

/-- Canonical-form/BNT data plus a finite pair trace-separation criterion give
full product-word span.

Once every ordered distinct pair has a common homogeneous trace-separating
length, pair trace-separation duality gives pairwise separating word
polynomials, and the selector-word construction spans the full product algebra. -/
theorem wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords μ A hCF
    (hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt A hSep)

/-- Canonical-form/BNT data plus cumulative pair trace separation and exact
identity padding give full product-word span.

The cumulative finite cutoff gives homogeneous separation at length `T` when
each ordered pair has simultaneous identity padding at the complementary lengths
needed to reach `T`. -/
theorem wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S T : ℕ}
    (hST : S ≤ T)
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S)
    (hPad : ∀ k j : Fin r, j ≠ k → ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (T - l)))) :
    WordTupleSpanTop A (1 + (r - 1) * T) :=
  wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF
    (fun k j hjk =>
      pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
        (A k) (A j) hST (hSep k j hjk) (hPad k j hjk))

/-- Positive-length product-word span from canonical-form/BNT data and
pairwise block-separating word polynomials. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairBlockSeparatingWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + (r - 1) * S, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords μ A hCF hPair

/-- Positive-length product-word span obtained from canonical-form/BNT data and
the finite pair trace-separation criterion. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + (r - 1) * S, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hSep

/-- Positive-length product-word span from canonical-form/BNT separation and
the source-faithful three-block direct-sum hypotheses.

The BNT data supply non-gauge-equivalence for equal-dimensional distinct
blocks.  Unequal-dimensional pairs use the strict-size branch of the
direct-sum argument.  The fixed-length block-injectivity hypotheses are kept
explicit, matching the direct-sum input rather than inferring them from BNT
data. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_threeBlock
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    {L : ℕ}
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hL : 1 < L) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :=
  exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF
    (forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
      A hIrr hCF.toIsLeftCanonicalBlockFamily hCF.toHasNormalizedSelfOverlap
      hCF.blocks_not_equiv hBlk hBlk3 hCF.toHasInjectiveBlocks.block_injective hL)

/-- Positive-length product-word span from canonical-form/BNT separation and
one-site injectivity of the BNT blocks.

This specializes the three-block direct-sum theorem to `L = 2`.  The
canonical-form/BNT hypotheses provide one-site injectivity for each block, and
fixed-length injectivity persists at positive multiples, giving the length-`2`
and length-`6` direct-sum inputs required by the source argument.  Irreducibility
remains explicit because the BNT predicate records injectivity and normalization
but not the tensor-irreducibility hypothesis used by the direct-sum comparison. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_threeBlock
    (d := d) (dim := dim) μ A hCF hIrr (L := 2) ?_ ?_ ?_
  · intro k
    simpa using isNBlkInjective_mul_of_isNBlkInjective (A k) (N := 1) (m := 2)
      (by norm_num) (isNBlkInjective_one_of_isInjective
        (hCF.toHasInjectiveBlocks.block_injective k))
  · intro k
    simpa using isNBlkInjective_mul_of_isNBlkInjective (A k) (N := 1) (m := 6)
      (by norm_num) (isNBlkInjective_one_of_isInjective
        (hCF.toHasInjectiveBlocks.block_injective k))
  · norm_num

/-- Positive-length product-word span from normal-CF-BNT data plus explicit
one-site injectivity.

Normal-CF-BNT data provide the irreducibility, trace-preserving normalization,
self-overlap normalization, weight ordering, and BNT separation used by the
direct-sum comparison.  The additional one-site injectivity hypothesis supplies
the `IsCanonicalFormBNT` injectivity field, after which the previous lemma
specializes the fixed-length direct-sum input to \(L=2\). -/
lemma exists_pos_productWordSpan_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hInj : ∀ k : Fin r, IsInjective (A k)) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  let hCF : IsCanonicalFormBNT μ A :=
    IsCanonicalFormBNT.ofSeparatedData
      (HasInjectiveBlocks.ofForall hInj)
      hNCF.toIsLeftCanonicalBlockFamily
      hNCF.toHasStrictOrderedNonzeroWeights
      hNCF.toHasNormalizedSelfOverlap
      hNCF.blocks_not_equiv
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    μ A hCF hNCF.toHasIrreducibleBlocks

/-- `WordTupleSpanTop` version of the direct-sum span theorem for
canonical-form/BNT block families. -/
lemma exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A) :
    ∃ m : ℕ, 0 < m ∧ WordTupleSpanTop A m := by
  obtain ⟨m, hm, hSpan⟩ :=
    exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
      μ A hCF hIrr
  exact ⟨m, hm, by simpa [WordTupleSpanTop, wordTuple] using hSpan⟩

/-- `WordTupleSpanTop` version of the direct-sum span theorem for
normal-CF-BNT block families with explicit one-site injectivity. -/
lemma exists_wordTupleSpanTop_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hInj : ∀ k : Fin r, IsInjective (A k)) :
    ∃ m : ℕ, 0 < m ∧ WordTupleSpanTop A m := by
  obtain ⟨m, hm, hSpan⟩ :=
    exists_pos_productWordSpan_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
      μ A hNCF hInj
  exact ⟨m, hm, by simpa [WordTupleSpanTop, wordTuple] using hSpan⟩

/-- Conditional positive-length product-word span from all-words pair separation plus eventual
identity padding for every ordered pair of distinct BNT blocks.

The proof takes a finite maximum over the separating and padding lengths for the
ordered block pairs, obtaining a single homogeneous word length whose block-product
word evaluations span the full direct product algebra.

This theorem does not supply BNT separation by itself: the homogeneous
identity-padding input must be supplied separately, preferably by fixed-length
or period-window hypotheses. -/
theorem exists_pos_productWordSpan_of_pairTraceSeparatingAll_of_identity_padding
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j))
    (hPad : ∀ k j : Fin r, j ≠ k → ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) n))) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  obtain ⟨T, hT⟩ :=
    exists_forall_pairTraceSeparatingAt_of_pairTraceSeparatingAll_of_identity_padding
      A hSep hPad
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hT

/-- Canonical-form/BNT data give all-words pair trace separation for every
ordered pair of distinct blocks.

Equal-dimensional pairs use the BNT non-gauge-phase-equivalence hypothesis and
the pair-product algebra density theorem.  Unequal-dimensional pairs use the
dimension-mismatch pair-product density theorem. -/
theorem pairTraceSeparatingAll_of_isCanonicalFormBNT
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) :
    ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j) := by
  intro k j hjk
  by_cases hdim : dim k = dim j
  · exact pairTraceSeparatingAll_of_injective_not_gaugePhaseEquiv_cast_left hdim
      (A k) (A j)
      (hCF.toHasInjectiveBlocks.block_injective k)
      (hCF.toHasInjectiveBlocks.block_injective j)
      (hCF.toIsLeftCanonicalBlockFamily.leftCanonical k)
      (hCF.toIsLeftCanonicalBlockFamily.leftCanonical j)
      (hCF.blocks_not_equiv k j hjk.symm hdim)
  · exact pairTraceSeparatingAll_of_injective_dim_ne
      (A k) (A j)
      (hCF.toHasInjectiveBlocks.block_injective k)
      (hCF.toHasInjectiveBlocks.block_injective j)
      hdim

/-- Canonical-form/BNT data plus eventual identity padding give a common
homogeneous trace-separating length for all ordered pairs of distinct blocks.

This is the finite-maximum step after the pairwise Burnside-Jacobson
identity-padding hypotheses have been supplied. The BNT hypotheses provide
all-words trace separation for each pair; the generic homogenization lemma
chooses one length that works for the whole finite block family.

The conclusion depends explicitly on homogeneous padding data; it is not the
David/Perez-Garcia finite-length direct-sum input. -/
theorem exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_padding
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hPad : ∀ k j : Fin r, j ≠ k → ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) n))) :
    ∃ T : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) T :=
  exists_forall_pairTraceSeparatingAt_of_pairTraceSeparatingAll_of_identity_padding
    A (pairTraceSeparatingAll_of_isCanonicalFormBNT μ A hCF) hPad

/-- Conditional positive-length product-word span from canonical-form/BNT data plus eventual
identity padding for every ordered pair of distinct blocks.

Canonical-form/BNT separation gives all-words trace separation for distinct blocks.
Together with eventual homogeneous identity padding for each ordered block pair, this
gives a positive word length at which the block-product word evaluations span the full
direct product algebra.

This theorem depends explicitly on homogeneous padding data. Use a
fixed-length or period-window hypothesis rather than replacing that input by
cumulative or all-words separation. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_identity_padding
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hPad : ∀ k j : Fin r, j ≠ k → ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) n))) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  obtain ⟨T, hT⟩ :=
    exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_padding
      μ A hCF hPad
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hT

/-- Canonical-form/BNT data plus period-window identity-padding certificates give a common
homogeneous trace-separating length for all ordered pairs of distinct blocks.

The BNT data supply all-words pair trace separation.  The period-window hypotheses are the
remaining Burnside-Jacobson input needed to convert the cumulative separation data to one
homogeneous length. -/
theorem exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hWindow : ∀ k j : Fin r, j ≠ k → ∃ start period : ℕ, 0 < period ∧
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) period)) ∧
      ∀ s : ℕ, s < period →
        ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
            (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
          Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (start + s)))) :
    ∃ T : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) T :=
  exists_forall_pairTraceSeparatingAt_of_pairTraceSeparatingAll_of_identity_period_windows
    A (pairTraceSeparatingAll_of_isCanonicalFormBNT μ A hCF) hWindow

/-- Product-word span from canonical-form/BNT data plus period-window identity-padding
certificates for every ordered pair of distinct blocks.

This is the direct word-span form of
`exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows`.
It keeps the period-window hypothesis explicit and takes a finite maximum over block pairs
to obtain a common length for later commutant and projection-span lemmas. -/
theorem exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_identity_period_windows
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hWindow : ∀ k j : Fin r, j ≠ k → ∃ start period : ℕ, 0 < period ∧
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) period)) ∧
      ∀ s : ℕ, s < period →
        ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
            (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
          Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (start + s)))) :
    ∃ T : ℕ, WordTupleSpanTop A (1 + (r - 1) * T) := by
  obtain ⟨T, hT⟩ :=
    exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows
      μ A hCF hWindow
  exact ⟨T, wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hT⟩

/-- Product-word span from canonical-form/BNT data plus period windows of full
homogeneous pair spans for every ordered pair of distinct blocks.

This is the same BNT finite-family wrapper as
`exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_identity_period_windows`, but
with the period-window input stated as fixed-length full pair spans. -/
theorem exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_pairSpanTop_period_windows
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hWindow : ∀ k j : Fin r, j ≠ k → ∃ start period : ℕ, 0 < period ∧
      PairWordTupleSpanTop (A k) (A j) period ∧
      ∀ s : ℕ, s < period → PairWordTupleSpanTop (A k) (A j) (start + s)) :
    ∃ T : ℕ, WordTupleSpanTop A (1 + (r - 1) * T) := by
  obtain ⟨T, hT⟩ :=
    exists_forall_pairTraceSeparatingAt_of_pairSpanTop_period_windows
      A (pairTraceSeparatingAll_of_isCanonicalFormBNT μ A hCF) hWindow
  exact ⟨T, wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hT⟩

/-- Positive-length product-word span from canonical-form/BNT data plus a
finite period-window identity-padding certificate for every ordered pair of
distinct blocks.

For a block family in canonical BNT form, it suffices to provide the finite
period-window identity-padding certificates for the ordered pairs of distinct
blocks.  The all-words pair separation follows from the BNT hypotheses. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_identity_period_windows
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hWindow : ∀ k j : Fin r, j ≠ k → ∃ start period : ℕ, 0 < period ∧
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) period)) ∧
      ∀ s : ℕ, s < period →
        ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
            (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
          Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (start + s)))) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  obtain ⟨T, hT⟩ :=
    exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows
      μ A hCF hWindow
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt μ A hCF hT

/-- Positive-length product-word span from cumulative pair trace separation plus
exact identity padding. -/
theorem
    exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S T : ℕ}
    (hST : S ≤ T)
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S)
    (hPad : ∀ k j : Fin r, j ≠ k → ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (T - l)))) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + (r - 1) * T, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding
      μ A hCF hST hSep hPad

/-- Positive-length product-word span obtained from canonical-form/BNT data and
finite block-selector words.

This is the goal shape with the still-missing selector-word theorem
kept explicit rather than replaced by the conclusion. -/
theorem exists_pos_productWordSpan_of_isCanonicalFormBNT_of_blockSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + S, Nat.add_pos_left Nat.zero_lt_one S, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords μ A hCF hSel

/-- Canonical-form/BNT data and selector words give the projection-span input for
the assembled tensor. -/
theorem blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin (1 + S) → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) := by
  exact blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTupleSpanTop
    (d := d) (dim := dim) μ A hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero
    (wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords μ A hCF hSel)

/-- Selector-word version of the assembled-tensor commutant criterion.

Under canonical-form/BNT data, finite block selectors replace the product-word
span hypothesis in the commutant reduction. The construction of those selectors
from BNT separation is the remaining finite-dimensional separation theorem. -/
theorem isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_bntSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S)
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin (1 + S) → Fin d,
      X * evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  exact isBlockDiagonal'_of_commutes_reindexed_wordSpan
    (B := toTensorFromBlocks (d := d) (μ := μ) A)
    (blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords
      (d := d) (dim := dim) μ A hCF hSel)
    hComm

/-- Entrywise off-block-zero corollary of
`isBlockDiagonal'_of_commutes_reindexed_wordSpan`.

This is often the most convenient form when using the result inside a boundary
matrix decomposition proof: after pulling the boundary matrix back to dependent
block coordinates, every entry from block `i` to a distinct block `j` vanishes. -/
theorem offBlock_zero_of_commutes_reindexed_wordSpan
    (B : MPSTensor d (∑ k : Fin r, dim k)) {m : ℕ}
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord B (List.ofFn ω))))
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord B (List.ofFn ω) = evalWord B (List.ofFn ω) * X)
    {i j : Fin r} (hij : i ≠ j) (a : Fin (dim i)) (b : Fin (dim j)) :
    (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  have hBD := isBlockDiagonal'_of_commutes_reindexed_wordSpan (B := B) hProj hComm
  exact (Matrix.isBlockDiagonal'_iff_offBlock_zero _).mp hBD hij a b

/-- Entrywise off-block-zero form of the assembled-tensor criterion with a finite
product-word span hypothesis. -/
theorem offBlock_zero_of_commutes_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {m : ℕ}
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hSpan : Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)))
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) * X)
    {i j : Fin r} (hij : i ≠ j) (a : Fin (dim i)) (b : Fin (dim j)) :
    (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  have hBD := isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_wordTuple_span_eq_top
    (d := d) (dim := dim) μ A hμ hSpan hComm
  exact (Matrix.isBlockDiagonal'_iff_offBlock_zero _).mp hBD hij a b

end MPSTensor
