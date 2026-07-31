/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.LiebOperatorIntegral
import TNLean.Analysis.SandwichedRenyiTwo
import TNLean.Channel.WhitenedChoi

/-!
# Faithful marginal whitening in arbitrary coordinates

This file removes the eigenbasis restriction from the faithful-marginal
whitened Choi estimate.  The first marginal is diagonalized explicitly.  The
input transpose forced by the Choi convention therefore disappears only after
that basis change.

## Main declaration

* `TNLean.sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank_of_posDef`
  bounds the order-two sandwiched trace by ordinary operator-Schmidt rank when
  both marginals are positive definite.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse fourth power of a positive-definite matrix is the inverse of
its iterated positive square root. -/
theorem PosDef.rpow_neg_quarter_eq_inv_sqrt_sqrt
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    A ^ (-(1 / 4 : ℝ)) = (CFC.sqrt (CFC.sqrt A))⁻¹ := by
  rw [CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow,
    CFC.rpow_rpow _ _ _ (by norm_num)]
  rw [Matrix.nonsing_inv_eq_ringInverse, CFC.inverse_eq_rpow_neg_one]
  rw [CFC.rpow_rpow _ _ _ (by norm_num)]
  congr 1
  ring

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Negative real powers distribute over a positive-semidefinite Kronecker
product. -/
theorem PosSemidef.rpow_kronecker
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (s : ℝ) :
    (A ⊗ₖ B) ^ s = (A ^ s) ⊗ₖ (B ^ s) := by
  rw [CFC.rpow_eq_cfc_real (hA.kronecker hB).nonneg,
    CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg]
  exact cfc_kronecker_of_mul_posSemidef hA hB (fun x : ℝ ↦ x ^ s)
    (fun x y hx hy ↦ Real.mul_rpow hx hy)

/-- The order-two sandwiched trace functional is invariant under unitary
conjugation. -/
theorem sandwichedRenyiTwoTrace_conj_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ ω : Matrix ι ι ℂ}
    (_hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (U : unitary (Matrix ι ι ℂ)) :
    TNLean.sandwichedRenyiTwoTrace
        ((U : Matrix ι ι ℂ) * ρ * star (U : Matrix ι ι ℂ))
        ((U : Matrix ι ι ℂ) * ω * star (U : Matrix ι ι ℂ)) =
      TNLean.sandwichedRenyiTwoTrace ρ ω := by
  let q := ω ^ (-(1 / 4 : ℝ))
  let Umat : Matrix ι ι ℂ := U
  have hq :
      (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) =
        Umat * q * star Umat := by
    exact rpow_conj_unitary hω (-(1 / 4 : ℝ)) U
  have hU : star Umat * Umat = 1 := Unitary.coe_star_mul_self U
  rw [TNLean.sandwichedRenyiTwoTrace, TNLean.sandwichedRenyiTwoTrace]
  change (trace
      (((Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) *
          (Umat * ρ * star Umat) *
          (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ))) *
        ((Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) *
          (Umat * ρ * star Umat) *
          (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ))))).re = _
  rw [hq]
  have hsandwich :
      (Umat * q * star Umat) * (Umat * ρ * star Umat) *
          (Umat * q * star Umat) =
        Umat * (q * ρ * q) * star Umat := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul,
      ← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul]
  rw [hsandwich]
  have hsquare :
      (Umat * (q * ρ * q) * star Umat) *
          (Umat * (q * ρ * q) * star Umat) =
        Umat * ((q * ρ * q) * (q * ρ * q)) * star Umat := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul]
  rw [hsquare, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

end Matrix

namespace TNLean

variable {dA dB : ℕ}

/-- For a positive-semidefinite bipartite operator with faithful marginals,
the order-two sandwiched trace against the product of the two marginals is at
most its operator-Schmidt rank.

The first marginal is conjugated by the adjoint of its eigenvector unitary.
Under the Choi convention the input whitening carries a transpose; it becomes
the ordinary diagonal whitening only in this eigenbasis. -/
theorem sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank_of_posDef
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) (hA : (partialTraceRight ρ).PosDef)
    (hB : (partialTraceLeft ρ).PosDef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let U : unitary (Matrix (Fin dA) (Fin dA) ℂ) :=
    hA.isHermitian.eigenvectorUnitary
  let Kmat : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
    star (U : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)
  have hKmat : Kmat ∈ unitary
      (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) := by
    exact Matrix.kronecker_mem_unitary (star U).prop (by simp)
  let K : unitary (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) := ⟨Kmat, hKmat⟩
  let ρ' : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
    Kmat * ρ * Kmatᴴ
  let p : Fin dA → ℝ := hA.isHermitian.eigenvalues
  have hρ' : ρ'.PosSemidef := by
    exact hρ.mul_mul_conjTranspose_same Kmat
  have hp : ∀ i, 0 < p i := fun i ↦ hA.eigenvalues_pos i
  have hKA : star (U : Matrix (Fin dA) (Fin dA) ℂ)ᴴ *
      star (U : Matrix (Fin dA) (Fin dA) ℂ) = 1 := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Unitary.mul_star_self_of_mem U.prop
  have hstarU : (star (U : Matrix (Fin dA) (Fin dA) ℂ))ᴴ =
      (U : Matrix (Fin dA) (Fin dA) ℂ) := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hKB : (1 : Matrix (Fin dB) (Fin dB) ℂ)ᴴ * 1 = 1 := by simp
  have hA' : partialTraceRight ρ' = diagonal fun i ↦ (p i : ℂ) := by
    dsimp only [ρ', Kmat]
    have h := partialTraceRight_kronecker_conj_of_right_isometry
      (star (U : Matrix (Fin dA) (Fin dA) ℂ))
      (1 : Matrix (Fin dB) (Fin dB) ℂ) hKB ρ
    rw [h, hstarU]
    simpa [U, p, Function.comp_def, Unitary.conjStarAlgAut_star_apply] using
      hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hB' : partialTraceLeft ρ' = partialTraceLeft ρ := by
    dsimp only [ρ', Kmat]
    have h := partialTraceLeft_kronecker_conj_of_left_isometry
      (star (U : Matrix (Fin dA) (Fin dA) ℂ))
      (1 : Matrix (Fin dB) (Fin dB) ℂ) hKA ρ
    simpa using h
  have hbound := supportedMarginalWhitenedState_trace_sq_re_le_operatorSchmidtRank
    ρ' p hρ' hp hA' (hB' ▸ hB)
  have hdiagPD : (diagonal fun i ↦ (p i : ℂ)).PosDef := by
    rw [posDef_diagonal_iff]
    intro i
    exact_mod_cast hp i
  have hqA :
      (diagonal fun i ↦ (p i : ℂ)) ^ (-(1 / 4 : ℝ)) =
        (diagonalMarginalQuarter p)⁻¹ := by
    rw [hdiagPD.rpow_neg_quarter_eq_inv_sqrt_sqrt,
      sqrt_sqrt_diagonal_eq_diagonalMarginalQuarter p hp]
  have hqB :
      (partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)) =
        (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹ :=
    (hB' ▸ hB).rpow_neg_quarter_eq_inv_sqrt_sqrt
  have href :
      partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ' =
        (diagonal fun i ↦ (p i : ℂ)) ⊗ₖ partialTraceLeft ρ' := by rw [hA']
  have hq :
      (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)) =
        (diagonalMarginalQuarter p)⁻¹ ⊗ₖ
          (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹ := by
    rw [href, hdiagPD.posSemidef.rpow_kronecker
      (hB' ▸ hB).posSemidef, hqA, hqB]
  let W := (diagonalMarginalQuarter p)⁻¹ ⊗ₖ
    (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹
  have hW : Wᴴ = W := by
    dsimp only [W]
    rw [← hq]
    exact (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).isHermitian.eq
  have hidentify :
      sandwichedRenyiTwoTrace ρ'
          (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') =
        (trace (supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ') *
          supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ'))).re := by
    rw [sandwichedRenyiTwoTrace]
    unfold supportedMarginalWhitenedState singleKrausMap
    change (trace
      ((((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ))) * ρ' *
          ((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)))) *
        (((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ))) * ρ' *
          ((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)))))).re =
      (trace ((W * ρ' * Wᴴ) * (W * ρ' * Wᴴ))).re
    rw [hq, hW]
  have hOSR : Matrix.operatorSchmidtRank ρ' = Matrix.operatorSchmidtRank ρ := by
    simpa only [ρ', Kmat] using Matrix.operatorSchmidtRank_local_isometry_conj
      (star (U : Matrix (Fin dA) (Fin dA) ℂ))
      (1 : Matrix (Fin dB) (Fin dB) ℂ) hKA hKB ρ
  have hrefConj :
      Kmat * (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) * Kmatᴴ =
        partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ' := by
    rw [hA', hB']
    dsimp only [Kmat]
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
    rw [hstarU]
    congr 1
    simpa [U, p, Function.comp_def, Unitary.conjStarAlgAut_star_apply] using
      hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hQ2 :
      sandwichedRenyiTwoTrace ρ'
          (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') =
        sandwichedRenyiTwoTrace ρ
          (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) := by
    rw [← hrefConj]
    simpa only [ρ', K, star_eq_conjTranspose] using
      Matrix.sandwichedRenyiTwoTrace_conj_unitary hρ
        (hA.posSemidef.kronecker hB.posSemidef) K
  calc
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      sandwichedRenyiTwoTrace ρ'
        (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') := hQ2.symm
    _ = (trace (supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ') *
          supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ'))).re := hidentify
    _ ≤ Matrix.operatorSchmidtRank ρ' := hbound
    _ = Matrix.operatorSchmidtRank ρ := by exact_mod_cast hOSR

end TNLean
