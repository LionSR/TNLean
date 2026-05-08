/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.BlockDiagonalCommutant.ProjectionSpan
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.BNT.Construction
import TNLean.MPS.MPDO.BiCFDerivation
import TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Block-diagonal commutants from sector projections

The algebraic commutant argument for a dependent direct sum is separated into
finite-dimensional hypotheses.  If the sector projections lie in the span of the
word products of the block-diagonal tensor and a boundary matrix commutes with those products, then
the boundary matrix commutes with every sector projection, hence has no off-block
entries.

A second reduction obtains the sector-projection span from a product-word span
for the blocks, provided the weights are nonzero.  For canonical-form
BNT block families, the results here use only restricted consequences of that
hypotheses: block injectivity, nonzero weights, pair separation, selector words, and
homogeneous padding hypotheses.  They are not the general CPSV repeated-sector
comparison, where multiplicities and sector weights remain explicit data.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Finite product-word span gives the projection-span input for `toTensorFromBlocks μ A`.

Assume that the simultaneous length-`m` word evaluations
`ω ↦ (k ↦ evalWord (A k) (List.ofFn ω))` span the full product algebra of the
blocks.  If all weights `μ k` are nonzero, then after pulling the length-`m`
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
matrix on the block-diagonal bond space commuting with all length-`m` word products
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

/-- Block injectivity plus finite block-selector words give full product-word span.

Once the selector words are available, only blockwise injectivity is needed:
a one-letter prefix spans the selected block algebra, and concatenating the
prefix and selector words spans the whole product algebra. -/
theorem wordTupleSpanTop_of_hasInjectiveBlocks_of_blockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    WordTupleSpanTop A (1 + S) := by
  refine wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    (A := A) (L := 1) (S := S) ?_ hSel
  intro k
  exact isNBlkInjective_one_of_isInjective (hInj.block_injective k)

/-- Canonical-form/BNT data and finite block-selector words give full product-word span. -/
lemma wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    WordTupleSpanTop A (1 + S) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_blockSelectorWords A hCF.toHasInjectiveBlocks hSel

/-- Block injectivity plus pairwise block-separating word polynomials give full
product-word span.

The pairwise hypotheses ask only for a word polynomial separating one ordered
pair of distinct blocks at a time.  The finite selector construction in
`hasBlockSelectorWords_of_pairBlockSeparatingWords` turns these pairwise
separators into full block selectors, and the selector-word reduction then gives
product-word span. -/
theorem wordTupleSpanTop_of_hasInjectiveBlocks_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_blockSelectorWords A hInj
    (hasBlockSelectorWords_of_pairBlockSeparatingWords A hPair)

/-- Canonical-form/BNT data and pairwise block-separating words give product-word span. -/
lemma wordTupleSpanTop_of_isCanonicalFormBNT_of_pairBlockSeparatingWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_pairBlockSeparatingWords A
    hCF.toHasInjectiveBlocks hPair

/-- Block injectivity plus a finite pair trace-separation criterion give full
product-word span.

Once every ordered distinct pair has a common homogeneous trace-separating
length, pair trace-separation duality gives pairwise separating word
polynomials, and the selector-word construction spans the full product algebra. -/
theorem wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingAt
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_pairBlockSeparatingWords A hInj
    (hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt A hSep)

/-- Canonical-form/BNT data and fixed-length pair trace separation give product-word span. -/
lemma wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    WordTupleSpanTop A (1 + (r - 1) * S) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingAt A
    hCF.toHasInjectiveBlocks hSep

/-- Block injectivity plus cumulative pair trace separation and exact identity
padding give full product-word span.

The cumulative finite cutoff gives homogeneous separation at length `T` when
each ordered pair has simultaneous identity padding at the complementary lengths
needed to reach `T`. -/
theorem wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingUpTo_of_identity_padding
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S T : ℕ}
    (hST : S ≤ T)
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S)
    (hPad : ∀ k j : Fin r, j ≠ k → ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (T - l)))) :
    WordTupleSpanTop A (1 + (r - 1) * T) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingAt A hInj
    (fun k j hjk =>
      pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
        (A k) (A j) hST (hSep k j hjk) (hPad k j hjk))

/-- Canonical-form/BNT data, cumulative separation, and padding give product-word span. -/
lemma wordTupleSpanTop_of_isCanonicalFormBNT_of_pairTraceSeparatingUpTo_of_identity_padding
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S T : ℕ}
    (hST : S ≤ T)
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S)
    (hPad : ∀ k j : Fin r, j ≠ k → ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) (T - l)))) :
    WordTupleSpanTop A (1 + (r - 1) * T) :=
  wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingUpTo_of_identity_padding
    A hCF.toHasInjectiveBlocks hST hSep hPad

/-- Positive-length product-word span from block injectivity and
pairwise block-separating word polynomials. -/
theorem exists_pos_productWordSpan_of_hasInjectiveBlocks_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + (r - 1) * S, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_hasInjectiveBlocks_of_pairBlockSeparatingWords A hInj hPair

/-- Canonical-form/BNT data and pairwise block-separating words give positive product span. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairBlockSeparatingWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :=
  exists_pos_productWordSpan_of_hasInjectiveBlocks_of_pairBlockSeparatingWords A
    hCF.toHasInjectiveBlocks hPair

/-- Positive-length product-word span obtained from block injectivity and
the finite pair trace-separation criterion. -/
theorem exists_pos_productWordSpan_of_hasInjectiveBlocks_of_pairTraceSeparatingAt
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + (r - 1) * S, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_hasInjectiveBlocks_of_pairTraceSeparatingAt A hInj hSep

/-- Canonical-form/BNT data and fixed-length pair trace separation give positive product span. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :=
  exists_pos_productWordSpan_of_hasInjectiveBlocks_of_pairTraceSeparatingAt A
    hCF.toHasInjectiveBlocks hSep

/-- Canonical-form/BNT hypotheses and the three-block direct-sum assumptions give
homogeneous pair separation at length `L + (L + L)`.

Equal-dimensional distinct blocks use the BNT non-gauge-equivalence hypothesis;
unequal-dimensional pairs use the strict-size direct-sum branch. -/
lemma forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    {L : ℕ}
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hL : 1 < L) :
    ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) (L + (L + L)) :=
  forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
    A hIrr hCF.toIsLeftCanonicalBlockFamily hCF.toHasNormalizedSelfOverlap
    hCF.blocks_not_equiv hBlk hBlk3 hCF.toHasInjectiveBlocks.block_injective hL

/-- Existential form of
`forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock`. -/
lemma exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    {L : ℕ}
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hL : 1 < L) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S :=
  ⟨L + (L + L),
    forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock
      μ A hCF hIrr hBlk hBlk3 hL⟩

/-- Canonical-form/BNT hypotheses and the three-block direct-sum assumptions give product span.

This is the product-algebra form of
`exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock`. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_directSum_threeBlock
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
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  obtain ⟨S, hSep⟩ :=
    exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock
      μ A hCF hIrr hBlk hBlk3 hL
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    μ A hCF hSep

/-- One-site injectivity of the BNT blocks gives one homogeneous pair-separation
length for all ordered pairs of distinct blocks.

The proof specializes the three-block direct-sum theorem to `L = 2`; one-site
injectivity gives the length-`2` and length-`6` fixed-length inputs. -/
lemma exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S := by
  refine exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_threeBlock
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
  obtain ⟨S, hSep⟩ :=
    exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
      μ A hCF hIrr
  exact exists_pos_productWordSpan_of_isCanonicalFormBNT_of_pairTraceSeparatingAt
    μ A hCF hSep

/-- Normal-CF-BNT hypotheses plus explicit one-site injectivity give one
homogeneous pair-separation length for all ordered pairs of distinct blocks. -/
lemma exists_forall_pairTraceSeparatingAt_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hInj : ∀ k : Fin r, IsInjective (A k)) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S := by
  let hCF : IsCanonicalFormBNT μ A :=
    IsCanonicalFormBNT.ofSeparatedData
      (HasInjectiveBlocks.ofForall hInj)
      hNCF.toIsLeftCanonicalBlockFamily
      hNCF.toHasStrictOrderedNonzeroWeights
      hNCF.toHasNormalizedSelfOverlap
      hNCF.blocks_not_equiv
  exact exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    μ A hCF hNCF.toHasIrreducibleBlocks

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

/-- Canonical-form/BNT direct-sum separation gives the block-injective
horizontal-canonical-form field used by the MPDO bicanonical-form structure. -/
lemma hasBiCF_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A)
    (hIrr : HasIrreducibleBlocks (d := d) A) :
    HasBiCF A := by
  obtain ⟨m, _hm, hSpan⟩ :=
    exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_directSum_injectiveBlocks
      μ A hCF hIrr
  exact hasBiCF_of_wordTupleSpanTop A hSpan

/-- Normal-CF-BNT direct-sum separation gives the block-injective
horizontal-canonical-form field used by the MPDO bicanonical-form structure,
provided one-site injectivity is supplied explicitly. -/
lemma hasBiCF_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hInj : ∀ k : Fin r, IsInjective (A k)) :
    HasBiCF A := by
  obtain ⟨m, _hm, hSpan⟩ :=
    exists_wordTupleSpanTop_of_isNormalCanonicalFormBNT_of_directSum_injectiveBlocks
      μ A hNCF hInj
  exact hasBiCF_of_wordTupleSpanTop A hSpan

/-- Conditional product-word span from all-words pair separation plus eventual identity padding.

The proof takes a finite maximum over the separating and padding lengths for the
ordered block pairs, obtaining a single homogeneous word length whose block-product
word evaluations span the full direct product algebra.

This lemma does not supply BNT separation by itself: the homogeneous
identity-padding input must be supplied separately, preferably by fixed-length
or period-window hypotheses. -/
lemma exists_pos_productWordSpan_of_pairTraceSeparatingAll_of_identity_padding
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

/-- Canonical-form/BNT data give all-words pair trace separation.

Equal-dimensional pairs use the BNT non-gauge-phase-equivalence hypothesis and
the pair-product algebra density theorem.  Unequal-dimensional pairs use the
dimension-mismatch pair-product density theorem. -/
lemma pairTraceSeparatingAll_of_isCanonicalFormBNT
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

/-- Canonical-form/BNT data and identity padding give homogeneous trace separation.

This is the finite-maximum step after the pairwise Burnside-Jacobson
identity-padding hypotheses have been supplied. The BNT hypotheses provide
all-words trace separation for each pair; the generic homogenization lemma
chooses one length that works for the whole finite block family.

The conclusion depends explicitly on homogeneous padding data; it is not the
David/Perez-Garcia finite-length direct-sum input. -/
lemma exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_padding
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

/-- Canonical-form/BNT data and eventual identity padding give positive product-word span.

Canonical-form/BNT separation gives all-words trace separation for distinct blocks.
Together with eventual homogeneous identity padding for each ordered block pair, this
gives a positive word length at which the block-product word evaluations span the full
direct product algebra.

This lemma depends explicitly on homogeneous padding data. Use a
fixed-length or period-window hypothesis rather than replacing that input by
cumulative or all-words separation. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_identity_padding
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

/-- Canonical-form/BNT data and period-window padding give homogeneous trace separation.

The BNT data supply all-words pair trace separation.  The period-window hypotheses are the
remaining Burnside-Jacobson input needed to convert the cumulative separation data to one
homogeneous length. -/
lemma exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows
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

/-- Canonical-form/BNT data and period-window identity padding give product-word span.

This is the direct word-span form of
`exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows`.
It keeps the period-window hypothesis explicit and takes a finite maximum over block pairs
to obtain a common length for later commutant and projection-span lemmas. -/
lemma exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_identity_period_windows
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

/-- Canonical-form/BNT data and period windows of full pair spans give product-word span.

This is the same finite-family conclusion as the identity-padding formulation,
but with the period-window input stated as fixed-length full pair spans. -/
lemma exists_wordTupleSpanTop_of_isCanonicalFormBNT_of_pairSpanTop_period_windows
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

/-- Canonical-form/BNT data and period-window padding give positive product-word span.

For a block family in canonical BNT form, it suffices to provide the finite
period-window identity-padding certificates for the ordered pairs of distinct
blocks.  The all-words pair separation follows from the BNT hypotheses. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_identity_period_windows
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

/-- Canonical-form/BNT data, cumulative separation, and padding give positive product span. -/
lemma
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

/-- From `IsCanonicalFormBNT`, obtain `PairTraceSeparatingAll` for every ordered
pair of distinct blocks and `PairTraceSeparatingUpTo S` for a common cutoff
`S`.

The homogeneous trace-separation conclusion still requires a period-window
identity-padding certificate
(see `exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows`
above). -/
theorem forall_pairTraceSeparatingAll_and_exists_pairTraceSeparatingUpTo_of_isCanonicalFormBNT
    [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) :
    (∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j)) ∧
    (∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S) := by
  have hSepAll : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j) :=
    pairTraceSeparatingAll_of_isCanonicalFormBNT μ A hCF
  obtain ⟨S, hSepUpTo⟩ :=
    exists_forall_pairTraceSeparatingUpTo_of_forall_pairTraceSeparatingAll A hSepAll
  exact ⟨hSepAll, ⟨S, hSepUpTo⟩⟩

/-- Positive-length product-word span obtained from block injectivity and finite
block-selector words.

This separates the selector-word hypothesis from the product-span conclusion, anticipating
the finite selector-word existence theorem. -/
theorem exists_pos_productWordSpan_of_hasInjectiveBlocks_of_blockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  refine ⟨1 + S, Nat.add_pos_left Nat.zero_lt_one S, ?_⟩
  simpa [WordTupleSpanTop, wordTuple] using
    wordTupleSpanTop_of_hasInjectiveBlocks_of_blockSelectorWords A hInj hSel

/-- Canonical-form/BNT data and finite block-selector words give positive product span.

This separates the selector-word hypothesis from the product-span conclusion, anticipating
the finite selector-word existence theorem. -/
lemma exists_pos_productWordSpan_of_isCanonicalFormBNT_of_blockSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∃ m : ℕ, 0 < m ∧
      Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
        fun k : Fin r => evalWord (A k) (List.ofFn ω)) =
      (⊤ : Submodule ℂ
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
  exact exists_pos_productWordSpan_of_hasInjectiveBlocks_of_blockSelectorWords A
    hCF.toHasInjectiveBlocks hSel

/-- Nonzero weights, block injectivity, and selector words give the projection-span
input for `toTensorFromBlocks μ A`. -/
theorem blockProjection_mem_span_reindexed_toTensorFromBlocks_of_selectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin (1 + S) → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) := by
  exact blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTupleSpanTop
    (d := d) (dim := dim) μ A hμ
    (wordTupleSpanTop_of_hasInjectiveBlocks_of_blockSelectorWords A hInj hSel)

/-- Canonical-form/BNT hypotheses and selector words give the projection-span input for
`toTensorFromBlocks μ A`. -/
lemma blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin (1 + S) → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω))) := by
  exact blockProjection_mem_span_reindexed_toTensorFromBlocks_of_selectorWords
    (d := d) (dim := dim) μ A hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero
    hCF.toHasInjectiveBlocks hSel

/-- Block injectivity, nonzero weights, and selector words give the commutant criterion.

The finite selectors and block injectivity give the projection-span input; only
nonzero weights are needed to pass through `toTensorFromBlocks`. -/
theorem isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_selectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    (hInj : HasInjectiveBlocks (d := d) A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S)
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin (1 + S) → Fin d,
      X * evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  exact isBlockDiagonal'_of_commutes_reindexed_wordSpan
    (B := toTensorFromBlocks (d := d) (μ := μ) A)
    (blockProjection_mem_span_reindexed_toTensorFromBlocks_of_selectorWords
      (d := d) (dim := dim) μ A hμ hInj hSel)
    hComm

/-- Selector-word version of the block-diagonal commutant criterion.

Under canonical-form/BNT data, finite block selectors replace the product-word
span hypothesis in the commutant reduction. The construction of those selectors
from BNT separation is the remaining finite-dimensional separation theorem. -/
lemma isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_bntSelectorWords
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) {S : ℕ}
    (hSel : HasBlockSelectorWords A S)
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin (1 + S) → Fin d,
      X * evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks (d := d) (μ := μ) A) (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  exact isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_selectorWords
    (d := d) (dim := dim) μ A hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero
    hCF.toHasInjectiveBlocks hSel hComm

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

/-- Entrywise off-block-zero form of the block-diagonal criterion with a finite
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
