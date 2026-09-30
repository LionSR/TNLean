/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal
import TNLean.MPS.SharedInfra.BlockGauge

/-!
# Global unitary assembly of matched periodic blocks

Permuting multiplicity copies and applying their unitary basis gauges gives
a global unitary between the two flattened bond spaces. This is the unitary
form of the global similarity in arXiv:1708.00029, Theorem 3.8, line 690,
used in the channel-root construction of Theorem 4.1, lines 752--810.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private theorem inv_eq_conjTranspose_of_unitary {n : ℕ} (G : GL (Fin n) ℂ)
    (hG : (G : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ((G⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (G : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  have heq : unitaryGL ⟨(G : Matrix (Fin n) (Fin n) ℂ), hG⟩ = G := Units.ext rfl
  exact congrArg (fun Z : GL (Fin n) ℂ =>
    ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) heq.symm

/-- Matched weighted blocks with unitary conjugations assemble into a
unitary conjugation of the complete tensors. Source: arXiv:1708.00029,
Theorem 3.8, line 690, and Theorem 4.1, lines 752--810. -/
theorem toTensorFromBlocks_unitary_conj_of_matched_blocks
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (ν : Fin s → ℂ) (B : (k : Fin s) → MPSTensor d (dim' k))
    (e : Fin r ≃ Fin s) (hd : ∀ k, dim k = dim' (e k))
    (U : (k : Fin s) → Matrix.unitaryGroup (Fin (dim' k)) ℂ)
    (hrel : ∀ k i,
      Matrix.reindex (finCongr (hd k)) (finCongr (hd k)) (μ k • A k i) =
        ν (e k) • ((U (e k) : Matrix (Fin (dim' (e k))) (Fin (dim' (e k))) ℂ) *
          B (e k) i * (U (e k) : Matrix (Fin (dim' (e k))) (Fin (dim' (e k))) ℂ)ᴴ)) :
    ∃ Y : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim' k)) ℂ,
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      ∀ i, toTensorFromBlocks μ A i = Y * toTensorFromBlocks ν B i * Yᴴ := by
  classical
  let X := fun k => unitaryGL (U k)
  let B' : (k : Fin s) → MPSTensor d (dim' k) := fun k i =>
    (U k : Matrix (Fin (dim' k)) (Fin (dim' k)) ℂ) * B k i *
      (U k : Matrix (Fin (dim' k)) (Fin (dim' k)) ℂ)ᴴ
  have hconj := toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
    (μ := ν) (A := B) (B := B') X (fun _ _ => rfl)
  have hblocks : ∀ k i, μ k • A k i =
      Matrix.reindex (finCongr (hd k)).symm (finCongr (hd k)).symm
        (ν (e k) • B' (e k) i) := by
    intro k i
    rw [show ν (e k) • B' (e k) i =
      Matrix.reindex (finCongr (hd k)) (finCongr (hd k)) (μ k • A k i) from
        (hrel k i).symm]
    ext a b
    simp
  have hreindex := toTensorFromBlocks_eq_reindex_of_equiv μ A ν B' e hd hblocks
  let E := blockDimEquiv e hd
  let G := globalGaugeOfBlocks X
  have hG : (G : Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ) ∈
      Matrix.unitaryGroup (Fin (∑ k, dim' k)) ℂ := globalGaugeOfBlocks_unitaryGL_mem U
  have hGinv : ((G⁻¹ : GL (Fin (∑ k, dim' k)) ℂ) :
      Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ) =
      (G : Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ)ᴴ :=
    inv_eq_conjTranspose_of_unitary G hG
  have hE : (permMatrixOfEquiv E)ᴴ = (permMatrixOfEquiv E)ᵀ := by
    ext i j
    simp [permMatrixOfEquiv, Matrix.conjTranspose_apply]
  refine ⟨permMatrixOfEquiv E * (G : Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hE, ← hGinv]
    rw [← Matrix.mul_assoc,
      Matrix.mul_assoc (permMatrixOfEquiv E)
        (G : Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ),
      show (G : Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ) *
        ((G⁻¹ : GL (Fin (∑ k, dim' k)) ℂ) :
          Matrix (Fin (∑ k, dim' k)) (Fin (∑ k, dim' k)) ℂ) = 1 from Units.mul_inv G,
      Matrix.mul_one, permMatrixOfEquiv_mul_transpose]
  · rw [Matrix.conjTranspose_mul, hE, ← hGinv]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMatrixOfEquiv E)ᵀ,
      permMatrixOfEquiv_transpose_mul, Matrix.one_mul]
    exact Units.inv_mul G
  · intro i
    rw [hreindex i, hconj i, reindex_eq_permMatrixOfEquiv_conj]
    rw [Matrix.conjTranspose_mul, hE]
    simp only [E, G, hGinv, Matrix.mul_assoc]

/-- The multiplicity phase gauge and matched unitary basis gauges assemble
into a global unitary conjugation, retaining the finite order, commutation,
and periodic-vector identities of the phase gauge. Source:
arXiv:1708.00029, Theorem 3.8, lines 643--690, and Theorem 4.1, lines 752--765. -/
theorem equalCase_global_unitary_zgauge_of_blockwise
    {d : ℕ} {P Q : SectorDecomposition d}
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hDim : ∀ j, P.basisDim j = Q.basisDim (perm j))
    (τ : (j : Fin P.basisCount) → Fin (P.copies j) ≃ Fin (Q.copies (perm j)))
    (ξ : Fin P.basisCount → ℂ)
    (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ)
    (hConj : ∀ (j : Fin P.basisCount) (i : Fin d),
      (cast (congr_arg (MPSTensor d) (hDim j)) (P.basis j)) i =
        ξ j • ((U (perm j) :
            Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ) *
          Q.basis (perm j) i *
          (U (perm j) :
            Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ)ᴴ))
    (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ)
    (hz : ∀ j q, z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ j q))
    (period : Fin P.basisCount → ℕ)
    (hPer : ∀ j, IsPeriodic (period j) (P.basis j))
    (hzm : ∀ j q, z j q ^ period j = 1)
    (L : ℕ) (hLdvd : ∀ j, period j ∣ L) :
    ∃ Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ,
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      blockScalarMatrix P.flatDim (P.flatCopyScalar z) ^ L = 1 ∧
      (∀ i : Fin d,
        blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
          P.toTensor i * blockScalarMatrix P.flatDim (P.flatCopyScalar z)) ∧
      (∀ i : Fin d,
        blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
          Y * Q.toTensor i * Yᴴ) ∧
      SameMPV₂Pos P.toTensor
        (fun i => blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i) := by
  classical
  let X := fun k => unitaryGL (U k)
  let e := SectorDecomposition.sectorFlatEquiv (P := Q) (Q := P) perm τ
  let hd : ∀ s, P.flatDim s = Q.flatDim (e s) := fun s =>
    (SectorDecomposition.flatDim_sectorFlatEquiv (P := Q) (Q := P) perm
      (fun j => (hDim j).symm) τ s).symm
  let Uflat : (s : Fin Q.totalCopies) → Matrix.unitaryGroup (Fin (Q.flatDim s)) ℂ :=
    fun s => U (Q.flatIndexEquiv.symm s).1
  have hrel := equalCase_flat_conj_of_blockwise perm hDim τ ξ X hConj z hz
  obtain ⟨Y, hY, hY', hconj⟩ := toTensorFromBlocks_unitary_conj_of_matched_blocks
    (fun s => P.flatCopyScalar z s * P.flatWeight s) P.flatBasis
    Q.flatWeight Q.flatBasis e hd Uflat hrel
  refine ⟨Y, hY, hY', ?_, ?_, ?_, ?_⟩
  · rw [blockScalarMatrix_pow]
    have hone : (fun s : Fin P.totalCopies => P.flatCopyScalar z s ^ L) =
        fun _ => (1 : ℂ) := by
      funext s
      obtain ⟨c, hc⟩ := hLdvd (P.flatIndexEquiv.symm s).1
      rw [SectorDecomposition.flatCopyScalar, hc, pow_mul, hzm, one_pow]
    rw [hone, blockScalarMatrix_one]
  · intro i
    exact (blockScalarMatrix_mul_toTensorFromBlocks _ P.flatWeight P.flatBasis i).trans
      (toTensorFromBlocks_mul_blockScalarMatrix _ P.flatWeight P.flatBasis i).symm
  · intro i
    exact (blockScalarMatrix_mul_toTensorFromBlocks _ P.flatWeight P.flatBasis i).trans
      (hconj i)
  · exact sameMPV₂Pos_blockScalarMatrix_mul_toTensor P z period hzm
      (fun j N σ h => pgvwc07_stateVector_eq_zero_of_not_dvd (P.basis j) (hPer j) h σ)

end MPSTensor
