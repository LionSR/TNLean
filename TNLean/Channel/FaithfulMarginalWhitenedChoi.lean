/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
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

namespace TNLean

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- For a positive-semidefinite bipartite operator with faithful marginals,
the order-two sandwiched trace against the product of the two marginals is at
most its operator-Schmidt rank.

The first marginal is conjugated by the adjoint of its eigenvector unitary.
Under the Choi convention the input whitening carries a transpose; it becomes
the ordinary diagonal whitening only in this eigenbasis. -/
theorem sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank_of_posDef
    (ρ : Matrix (α × β) (α × β) ℂ)
    (hρ : ρ.PosSemidef) (hA : (partialTraceRight ρ).PosDef)
    (hB : (partialTraceLeft ρ).PosDef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let U : unitary (Matrix α α ℂ) :=
    hA.isHermitian.eigenvectorUnitary
  let Kmat : Matrix (α × β) (α × β) ℂ :=
    star (U : Matrix α α ℂ) ⊗ₖ (1 : Matrix β β ℂ)
  have hKmat : Kmat ∈ unitary
      (Matrix (α × β) (α × β) ℂ) := by
    exact Matrix.kronecker_mem_unitary (star U).prop (by simp)
  let K : unitary (Matrix (α × β) (α × β) ℂ) := ⟨Kmat, hKmat⟩
  let ρ' : Matrix (α × β) (α × β) ℂ :=
    Kmat * ρ * Kmatᴴ
  let p : α → ℝ := hA.isHermitian.eigenvalues
  have hρ' : ρ'.PosSemidef := by
    exact hρ.mul_mul_conjTranspose_same Kmat
  have hp : ∀ i, 0 < p i := fun i ↦ hA.eigenvalues_pos i
  have hKA : star (U : Matrix α α ℂ)ᴴ *
      star (U : Matrix α α ℂ) = 1 := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Unitary.mul_star_self_of_mem U.prop
  have hstarU : (star (U : Matrix α α ℂ))ᴴ =
      (U : Matrix α α ℂ) := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hKB : (1 : Matrix β β ℂ)ᴴ * 1 = 1 := by simp
  have hA' : partialTraceRight ρ' = diagonal fun i ↦ (p i : ℂ) := by
    dsimp only [ρ', Kmat]
    have h := partialTraceRight_kronecker_conj_of_right_isometry
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKB ρ
    rw [h, hstarU]
    simpa [U, p, Function.comp_def, Unitary.conjStarAlgAut_star_apply] using
      hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hB' : partialTraceLeft ρ' = partialTraceLeft ρ := by
    dsimp only [ρ', Kmat]
    have h := partialTraceLeft_kronecker_conj_of_left_isometry
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKA ρ
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
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKA hKB ρ
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
      sandwichedRenyiTwoTrace_conj_unitary
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
