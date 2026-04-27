/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Provides `Matrix.blockProjection`, `Matrix.IsBlockDiagonal'`, and the
-- projection-commutant criterion used below.
import TNLean.Algebra.ScalarCommutant
import TNLean.MPS.BNT.Construction
import TNLean.MPS.MPDO.BiCFDerivation
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Block-diagonal commutants from sector projections

This file isolates the algebraic part of the block-diagonal commutant argument
for the parent-Hamiltonian block decomposition. If the sector projections of a
dependent direct sum lie in the span of a family of matrices and a boundary
matrix commutes with that family, then it
commutes with the projections and hence has no off-block entries.

The file also records a finite-span reduction: if the simultaneous block word
tuples span the full product algebra, then the sector projections lie in the
finite word span of the assembled tensor.  The remaining paper-level CF/BNT input
is to derive that product-word span from the separated canonical-form/BNT
hypotheses.  Once the projection-span input is available,
`MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan` turns long-word
commutation of the assembled boundary matrix into block diagonality.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {ι α : Type*} {n : ι → Type*}

section CommutesSpan

variable [Fintype ι] [DecidableEq ι]
variable [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]

/-- If every block projection lies in the span of a matrix family `S`, then any
matrix commuting with all members of `S` is block diagonal.

This records the common linearity step used in commutant arguments: commutation
extends from generators to their span, giving commutation with each projection;
`Matrix.isBlockDiagonal'_of_commutes_blockProjection` then kills all off-block
entries. -/
theorem isBlockDiagonal'_of_commutes_span_blockProjection
    {S : α → Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    {X : Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    (hProj : ∀ k : ι,
      blockProjection (n := n) (R := ℂ) k ∈ Submodule.span ℂ (Set.range S))
    (hComm : ∀ a : α, X * S a = S a * X) :
    IsBlockDiagonal' X := by
  classical
  apply isBlockDiagonal'_of_commutes_blockProjection (n := n) (R := ℂ)
  intro k
  have hcomm_span : ∀ M ∈ Submodule.span ℂ (Set.range S), X * M = M * X := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
        rcases hM with ⟨a, rfl⟩
        exact hComm a
    | zero => simp
    | add M N _ _ hM hN => rw [mul_add, add_mul, hM, hN]
    | smul c M _ hM =>
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hM]
  exact hcomm_span (blockProjection (n := n) (R := ℂ) k) (hProj k)

end CommutesSpan

section ProjectionSpan

variable [DecidableEq ι]
variable [(i : ι) → DecidableEq (n i)]

/-- If a family of block tuples spans the full product algebra, then the span of
its nonzero componentwise scalar multiples, embedded as dependent block-diagonal
matrices, contains each sector projection.

This is the algebraic finite-span reduction used for assembled tensors: after a
finite word-tuple span theorem supplies the full product algebra
`(i : ι) → Matrix (n i) (n i) ℂ`, the diagonal embedding of those same word tuples
contains the projections onto the individual direct-sum sectors. -/
theorem blockProjection_mem_span_blockDiagonal'_of_pi_span_eq_top
    {T : α → (i : ι) → Matrix (n i) (n i) ℂ} {c : ι → ℂ}
    (hc : ∀ i : ι, c i ≠ 0)
    (hSpan : Submodule.span ℂ (Set.range T) =
      (⊤ : Submodule ℂ ((i : ι) → Matrix (n i) (n i) ℂ)))
    (k : ι) :
    blockProjection (n := n) (R := ℂ) k ∈
      Submodule.span ℂ (Set.range fun a : α =>
        Matrix.blockDiagonal' fun i : ι => c i • T a i) := by
  classical
  let target : (i : ι) → Matrix (n i) (n i) ℂ :=
    fun i => if i = k then (c i)⁻¹ • 1 else 0
  let L : ((i : ι) → Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ := {
    toFun := fun M => Matrix.blockDiagonal' fun i : ι => c i • M i
    map_add' := by
      intro M N
      ext x y
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      by_cases hij : i = j
      · subst j
        simp [Pi.add_apply, smul_add]
      · simp [Matrix.blockDiagonal'_apply_ne _ p q hij]
    map_smul' := by
      intro a M
      ext x y
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      by_cases hij : i = j
      · subst j
        simp [smul_smul, mul_comm, mul_left_comm]
      · simp [Matrix.blockDiagonal'_apply_ne _ p q hij] }
  have htarget : target ∈ Submodule.span ℂ (Set.range T) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hmap_span : ∀ M ∈ Submodule.span ℂ (Set.range T),
      L M ∈ Submodule.span ℂ (Set.range fun a : α =>
        Matrix.blockDiagonal' fun i : ι => c i • T a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
        rcases hM with ⟨a, rfl⟩
        exact Submodule.subset_span ⟨a, rfl⟩
    | zero =>
        have hL0 : L 0 = 0 := by
          ext x y
          rcases x with ⟨i, p⟩
          rcases y with ⟨j, q⟩
          by_cases hij : i = j
          · subst j
            simp [L]
          · simp [L, Matrix.blockDiagonal'_apply_ne _ p q hij]
        rw [hL0]
        exact Submodule.zero_mem _
    | add M N _ _ hM hN => simpa [L.map_add] using Submodule.add_mem _ hM hN
    | smul a M _ hM => simpa [L.map_smul] using Submodule.smul_mem _ a hM
  have hL_target : L target = blockProjection (n := n) (R := ℂ) k := by
    ext x y
    rcases x with ⟨i, p⟩
    rcases y with ⟨j, q⟩
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp [L, target, blockProjection, hc i]
      · simp [L, target, blockProjection, hik]
    · simp [L, blockProjection, Matrix.blockDiagonal'_apply_ne _ p q hij]
  simpa [L, hL_target] using hmap_span target htarget

end ProjectionSpan

end Matrix

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

/-- Positive-length product-word span obtained from canonical-form/BNT data and
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
finite block-selector words.

This is the issue-#934 goal shape with the still-missing selector-word theorem
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
