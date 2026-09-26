/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import QICLean.Algebra.MatrixAux
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Kraus.Injectivity
import QICLean.Kraus.InvariantProjection
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
* MPSTensor.PGVWC07CanonicalFormData.trace_evalWord_eq_sum,
  MPSTensor.PGVWC07CanonicalFormData.mpv_eq_sum - the amplitudes of a
  canonical form are the weighted sums of the block amplitudes.
* MPSTensor.isIrreducibleFamily_of_unital_of_dualFixedPoint,
  MPSTensor.PGVWC07CanonicalFormData.isIrreducibleFamily_blocks - the three
  canonical conditions make a block irreducible.
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

/-- In a star ring, if `P` is a self-adjoint idempotent with `K P = P K P`, then
`K P K^* = P K K^* P - B B^*` with `B = P K (1 - P)`. -/
private theorem mul_proj_mul_star_eq {R : Type*} [Ring R] [StarRing R] {P K : R}
    (hP : star P = P) (hPP : P * P = P) (hKP : K * P = P * K * P) :
    K * P * star K = P * (K * star K) * P - P * K * (1 - P) * star (P * K * (1 - P)) := by
  have hPP' : ∀ x, P * (P * x) = P * x := fun x => by rw [← mul_assoc, hPP]
  calc K * P * star K = K * P * star (K * P) := by
        rw [star_mul, hP, ← mul_assoc, mul_assoc K P P, hPP]
    _ = P * K * P * star (P * K * P) := by rw [hKP]
    _ = _ := by
        simp only [star_mul, star_sub, hP, mul_sub, sub_mul, mul_one, mul_assoc, hPP']
        abel

/-- Bridge: a block satisfying conditions 1–3 of arXiv:quant-ph/0608197, Theorem 4
(lines 753–757) is irreducible. Let `∑_i A_i A_i^† = 1`, let `Λ` be a positive definite
fixed point of the dual map `X ↦ ∑_i A_i^† X A_i`, and let every fixed point of
`X ↦ ∑_i A_i X A_i^†` be a scalar. If `(1 - P) A_i P = 0` for an orthogonal projection `P`,
then `P - ∑_i A_i P A_i^†` is the positive matrix `∑_i B_i B_i^†`, `B_i = P A_i (1 - P)`,
whose pairing with `Λ` vanishes; so `P` is a fixed point of `X ↦ ∑_i A_i X A_i^†`, hence a
scalar projection, `0` or `1`. -/
theorem isIrreducibleFamily_of_unital_of_dualFixedPoint (A : MPSTensor d D)
    (hunital : ∑ i, A i * (A i)ᴴ = 1) {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛ : Λ.PosDef)
    (hΛfix : Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) Λ = Λ)
    (hscalar : ∀ X : Matrix (Fin D) (Fin D) ℂ, Kraus.transferMap (d := d) (D := D) A X = X →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    Kraus.IsIrreducibleFamily A := by
  classical
  rintro ⟨P, ⟨hPh, hPP⟩, hP0, hP1, hinv⟩
  have hΛfix' : ∑ i, (A i)ᴴ * Λ * A i = Λ := by
    rw [Kraus.transferMap_apply] at hΛfix
    simpa only [Matrix.conjTranspose_conjTranspose] using hΛfix
  have hPh' : star P = P := hPh
  have hterm : ∀ i, A i * P * (A i)ᴴ =
      P * (A i * (A i)ᴴ) * P - P * A i * (1 - P) * (P * A i * (1 - P))ᴴ := fun i => by
    have hKP : A i * P = P * A i * P := by
      have := hinv i
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul] at this
      exact sub_eq_zero.mp this
    simpa only [Matrix.star_eq_conjTranspose] using mul_proj_mul_star_eq hPh' hPP hKP
  have hsum : P - Kraus.transferMap (d := d) (D := D) A P =
      ∑ i, P * A i * (1 - P) * (P * A i * (1 - P))ᴴ := by
    rw [Kraus.transferMap_apply, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hunital, Matrix.mul_one, hPP, sub_sub_cancel]
  have hpsd : (P - Kraus.transferMap (d := d) (D := D) A P).PosSemidef := by
    rw [hsum]
    exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_self_mul_conjTranspose _
  have htr : Matrix.trace (Λ * (P - Kraus.transferMap (d := d) (D := D) A P)) = 0 := by
    rw [Kraus.transferMap_apply, Matrix.mul_sub, Matrix.trace_sub, Finset.mul_sum,
      Matrix.trace_sum, sub_eq_zero]
    conv_lhs => rw [← hΛfix', Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hfix : Kraus.transferMap (d := d) (D := D) A P = P :=
    (sub_eq_zero.mp (Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hpsd hΛ htr)).symm
  obtain ⟨c, hc⟩ := hscalar P hfix
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    exact hP0 (Subsingleton.elim _ _)
  have : NeZero D := ⟨hD.ne'⟩
  have hcc : c * c = c := by
    have := congrFun (congrFun hPP 0) 0
    rw [hc] at this
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with h0 | h1
  · exact hP0 (by rw [hc, h0, zero_smul])
  · exact hP1 (by rw [hc, h1, one_smul])

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

/-- Condition 2 of arXiv:quant-ph/0608197, Theorem 4 (lines 753–755) in the form of a
positive definite fixed point of the transfer map of the conjugate-transposed block. -/
theorem dualFixedPoint_transferMap (k : Fin h.r) :
    ∃ Λ : Matrix (Fin (h.dim k)) (Fin (h.dim k)) ℂ, Λ.PosDef ∧
      Kraus.transferMap (d := d) (D := h.dim k) (fun i => (h.blocks k i)ᴴ) Λ = Λ := by
  obtain ⟨Λ, hΛ, -, hΛfix⟩ := h.dual_fixedPoint k
  refine ⟨Λ, hΛ, ?_⟩
  rw [Kraus.transferMap_apply]
  simpa only [Matrix.conjTranspose_conjTranspose] using hΛfix

/-- Source: arXiv:quant-ph/0608197, lines 1320–1326 (`|φ⟩ = ∑_j |φ_{A^j}⟩` with
`|φ_{A^j}⟩ = λ_j^N ∑ tr(A^j_{i_1} ⋯ A^j_{i_N}) |i_1 ⋯ i_N⟩`), at the level of words: the
trace of a word of a canonical form is the weighted sum of the traces of the block words. -/
theorem trace_evalWord_eq_sum (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord A w) =
      ∑ k, (h.weight k : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (h.blocks k) w) := by
  rw [h.evalWord_eq, Matrix.reindex_apply, Matrix.trace_submatrix_equiv,
    Matrix.trace_blockDiagonal']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]

/-- Source: arXiv:quant-ph/0608197, lines 1320–1326: the periodic vector of a canonical form
is the sum of the weighted block vectors, `|φ⟩ = ∑_j λ_j^N |φ_{A^j}⟩`. -/
theorem mpv_eq_sum {N : ℕ} (σ : Fin N → Fin d) :
    mpv A σ = ∑ k, (h.weight k : ℂ) ^ N * mpv (h.blocks k) σ := by
  simp only [mpv_eq, coeff_eq, h.trace_evalWord_eq_sum, List.length_ofFn]

/-- Bridge: every block of a canonical form is irreducible, by conditions 1–3 of
arXiv:quant-ph/0608197, Theorem 4 (lines 753–757); see
`isIrreducibleFamily_of_unital_of_dualFixedPoint`. -/
theorem isIrreducibleFamily_blocks (k : Fin h.r) : Kraus.IsIrreducibleFamily (h.blocks k) :=
  isIrreducibleFamily_of_unital_of_dualFixedPoint _ (h.unital k)
    (h.dualFixedPoint_transferMap k).choose_spec.1 (h.dualFixedPoint_transferMap k).choose_spec.2
    (h.fixedPoint_scalar k)

/-- Bridge: the dual map `X ↦ ∑_i A_i^† X A_i` of every block of a canonical form is
irreducible, from `isIrreducibleFamily_blocks` and the passage to the trace adjoint. -/
theorem isIrreducibleMap_mapLM_blocks_conjTranspose (k : Fin h.r) :
    IsIrreducibleMap (Kraus.mapLM fun i => (h.blocks k i)ᴴ) :=
  Kraus.isIrreducibleMap_mapLM_conjTranspose _
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily _ (h.isIrreducibleFamily_blocks k))

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
