/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Transfer
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# The translation-invariant canonical form of PGVWC07 as a predicate

This file packages the block form of the translation-invariant canonical form
of Pérez-García, Verstraete, Wolf, and Cirac (PGVWC07, arXiv:quant-ph/0608197,
Theorem 4, MPSarchive.tex lines 742-763) as a predicate on a tensor of bond
dimension \(D\): the matrices are block diagonal,
\(A_i=\bigoplus_j\lambda_jA_i^j\) with weights \(1\ge\lambda_j>0\), and each
block satisfies the three canonical conditions of the theorem. The blocks
occupy a partition of the bond indices given by a bijection; the source lists
the blocks consecutively, which is the special case of the standard block
order.

The first assertion of the proposition on condition C1 (lines 911-919), that
condition C1 forces a single block, is proved here: a matrix supported on one
off-diagonal block is annihilated by every word, so a canonical form with two
blocks is not block injective at any length. For a block-injective canonical
form the sum \(\sum_iA_iA_i^\dagger\) is therefore the scalar \(\lambda^2\)
of its unique block.

## Main declarations

* MPSTensor.PGVWC07CanonicalFormData, MPSTensor.IsPGVWC07CanonicalForm - the
  block data of Theorem 4 and the corresponding predicate.
* MPSTensor.PGVWC07CanonicalFormData.not_isNBlkInjective_of_ne - two blocks
  exclude block injectivity, the first assertion of the proposition on
  condition C1.
* MPSTensor.PGVWC07CanonicalFormData.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective -
  a block-injective canonical form is a single weighted unital block.
* MPSTensor.isPGVWC07CanonicalForm_toTensorFromBlocks - the weighted direct
  sum produced by the existence theorem is in canonical form.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The block data of the translation-invariant canonical form of PGVWC07
(arXiv:quant-ph/0608197, Theorem 4, MPSarchive.tex lines 742-763): finitely
many blocks of positive bond dimension, weights `1 ≥ λ_j > 0`, the three
canonical conditions on each block, and the block-diagonal reconstruction of
the tensor along a bijection between the block coordinates and the bond
indices. -/
structure PGVWC07CanonicalFormData (A : MPSTensor d D) where
  /-- The number of blocks (lines 745-751). -/
  r : ℕ
  /-- The bond dimension of each block (lines 745-751). -/
  dim : Fin r → ℕ
  /-- Every block has positive bond dimension.

  **Local fix (positive block dimensions):** the source does not state the
  size of a block; an empty block contributes nothing to the direct sum and
  is not a summand the source intends, so the predicate lists only blocks of
  positive dimension. Documented in
  docs/paper-gaps/pgvwc07_ti_canonical_form_positive_blocks.tex. -/
  dim_pos : ∀ k, 0 < dim k
  /-- The weight `λ_j` of each block (line 751). -/
  weight : Fin r → ℝ
  /-- The weights are positive (line 751). -/
  weight_pos : ∀ k, 0 < weight k
  /-- The weights are at most one (line 751). -/
  weight_le_one : ∀ k, weight k ≤ 1
  /-- The matrices `A_i^j` of each block (lines 745-751). -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Condition 1: `∑_i A_i^j A_i^{j†} = 1` (line 753). -/
  unital : ∀ k, ∑ i, blocks k i * (blocks k i)ᴴ = 1
  /-- Condition 2: `∑_i A_i^{j†} Λ^j A_i^j = Λ^j` for a diagonal positive
  full-rank `Λ^j` (lines 753-755). -/
  dual_fixedPoint : ∀ k, ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
    Λ.PosDef ∧ Λ.IsDiag ∧ ∑ i, (blocks k i)ᴴ * Λ * blocks k i = Λ
  /-- Condition 3: the identity is the only fixed point of
  `X ↦ ∑_i A_i^j X A_i^{j†}` up to scalars (lines 755-757). -/
  fixedPoint_scalar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
    Kraus.transferMap (d := d) (D := dim k) (blocks k) X = X →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
  /-- The bond indices occupied by the blocks; the source lists the blocks
  consecutively (lines 745-751). -/
  index : ((k : Fin r) × Fin (dim k)) ≃ Fin D
  /-- The block-diagonal form `A_i = ⊕_j λ_j A_i^j` (lines 745-751). -/
  reconstruct : ∀ i, A i = Matrix.reindex index index
    (Matrix.blockDiagonal' fun k => (weight k : ℂ) • blocks k i)

/-- A tensor is a translation-invariant canonical representation in the sense
of PGVWC07 (arXiv:quant-ph/0608197, Theorem 4, MPSarchive.tex lines 742-763)
when it carries the block data of that theorem. -/
def IsPGVWC07CanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (PGVWC07CanonicalFormData A)

namespace PGVWC07CanonicalFormData

variable {A : MPSTensor d D} (h : PGVWC07CanonicalFormData A)

/-- Every word of a canonical form is block diagonal, with the word of the
weighted block `λ_j A^j` on block `j`. -/
theorem evalWord_eq (w : List (Fin d)) :
    Kraus.evalWord A w = Matrix.reindex h.index h.index
      (Matrix.blockDiagonal' fun k =>
        Kraus.evalWord (fun i => (h.weight k : ℂ) • h.blocks k i) w) := by
  classical
  induction w with
  | nil =>
    simp only [Kraus.evalWord_nil, Matrix.reindex_apply]
    rw [show (fun k => (1 : Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ)) =
      (1 : ∀ k, Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ) from rfl,
      Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih, h.reconstruct i, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
    rfl

/-- **Two blocks exclude block injectivity**, the first assertion of the
proposition on condition C1 in PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex
lines 911-919): the matrix unit supported on an off-diagonal block is
annihilated by every word, so the words of no length span the full matrix
algebra. -/
theorem not_isNBlkInjective_of_ne {k k' : Fin h.r} (hkk' : k ≠ k') (L : ℕ) :
    ¬ Kraus.IsNBlkInjective A L := by
  classical
  refine Kraus.not_isNBlkInjective_of_linearMap
    (Matrix.entryLinearMap ℂ ℂ (h.index ⟨k, ⟨0, h.dim_pos k⟩⟩) (h.index ⟨k', ⟨0, h.dim_pos k'⟩⟩))
    (fun σ => ?_)
    (Matrix.single (h.index ⟨k, ⟨0, h.dim_pos k⟩⟩) (h.index ⟨k', ⟨0, h.dim_pos k'⟩⟩) 1) ?_
  · simp only [Matrix.entryLinearMap_apply, h.evalWord_eq, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hkk'
  · simp

/-- The sum `∑_i A_i A_i†` of a canonical form is the block-diagonal matrix
with the scalar `λ_j²` on block `j`, by condition 1 on each block. -/
theorem sum_mul_conjTranspose_eq :
    ∑ i, A i * (A i)ᴴ = Matrix.reindex h.index h.index
      (Matrix.blockDiagonal' fun k =>
        ((h.weight k : ℂ) ^ 2) • (1 : Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ)) := by
  classical
  have hi : ∀ i, A i * (A i)ᴴ = Matrix.reindexLinearEquiv ℂ ℂ h.index h.index
      (Matrix.blockDiagonal'AddMonoidHom _ _ ℂ fun k =>
        ((h.weight k : ℂ) ^ 2) • (h.blocks k i * (h.blocks k i)ᴴ)) := by
    intro i
    rw [Matrix.coe_reindexLinearEquiv, Matrix.blockDiagonal'AddMonoidHom_apply,
      h.reconstruct i, Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.blockDiagonal'_conjTranspose,
      ← Matrix.blockDiagonal'_mul]
    refine congrArg (fun M => Matrix.submatrix M _ _)
      (congrArg Matrix.blockDiagonal' (funext fun k => ?_))
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def,
      Complex.conj_ofReal, sq]
  rw [Finset.sum_congr rfl fun i _ => hi i, ← map_sum, ← map_sum, Matrix.coe_reindexLinearEquiv,
    Matrix.blockDiagonal'AddMonoidHom_apply]
  refine congrArg (Matrix.reindex h.index h.index)
    (congrArg Matrix.blockDiagonal' (funext fun k => ?_))
  simp only [Finset.sum_apply, ← Finset.smul_sum, h.unital k]

include h in
/-- **A block-injective canonical form has a single block**, the first
assertion of the proposition on condition C1 in PGVWC07
(arXiv:quant-ph/0608197, MPSarchive.tex lines 911-919), in the form used by
the uniqueness theorem: the sum `∑_i A_i A_i†` is the scalar `λ²` of the
unique block, with `0 < λ ≤ 1`. -/
theorem exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective [NeZero D] {L : ℕ}
    (hinj : Kraus.IsNBlkInjective A L) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ ∑ i, A i * (A i)ᴴ = ((lam : ℂ) ^ 2) • 1 := by
  classical
  obtain ⟨k₀, -⟩ := h.index.symm ⟨0, NeZero.pos D⟩
  have hk : ∀ k : Fin h.r, k = k₀ := fun k => by
    by_contra hne
    exact h.not_isNBlkInjective_of_ne hne L hinj
  refine ⟨h.weight k₀, h.weight_pos k₀, h.weight_le_one k₀, ?_⟩
  rw [h.sum_mul_conjTranspose_eq]
  have hconst : (fun k => ((h.weight k : ℂ) ^ 2) •
      (1 : Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ)) =
      ((h.weight k₀ : ℂ) ^ 2) • (1 : ∀ k, Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ) := by
    funext k
    have hkk := hk k
    subst hkk
    rfl
  rw [hconst, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one, Matrix.reindex_apply]
  ext a b
  simp [Matrix.one_apply]

end PGVWC07CanonicalFormData

/-- The weighted direct sum of blocks produced by the existence theorem for
the canonical form (PGVWC07, arXiv:quant-ph/0608197, Theorem 4, MPSarchive.tex
lines 742-763) is in canonical form, with the blocks in their standard
consecutive order. -/
theorem isPGVWC07CanonicalForm_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (ν : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hdim : ∀ k, 0 < dim k)
    (hν : ∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ))
    (hν_le : ∀ k, ‖ν k‖ ≤ 1)
    (hunital : ∀ k, ∑ i, blocks k i * (blocks k i)ᴴ = 1)
    (hdual : ∀ k, ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      Λ.PosDef ∧ Λ.IsDiag ∧ ∑ i, (blocks k i)ᴴ * Λ * blocks k i = Λ)
    (hfixed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      Kraus.transferMap (d := d) (D := dim k) (blocks k) X = X →
        ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :
    IsPGVWC07CanonicalForm (toTensorFromBlocks (d := d) (μ := ν) blocks) := by
  choose a ha using hν
  refine ⟨⟨r, dim, hdim, a, fun k => (ha k).1, fun k => ?_, blocks, hunital, hdual, hfixed,
    finSigmaFinEquiv, fun i => ?_⟩⟩
  · have := hν_le k
    rw [(ha k).2, Complex.norm_real, Real.norm_of_nonneg (ha k).1.le] at this
    exact this
  · simp only [toTensorFromBlocks]
    congr 2
    funext k
    rw [(ha k).2]

end MPSTensor
