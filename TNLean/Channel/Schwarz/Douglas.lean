/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Basic
import TNLean.Algebra.MatrixAux
import TNLean.Analysis.MatrixSqrt
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Douglas

variable {D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

theorem factorization_of_range_mulVecLin_le
    {A B : Mat} (hAB : A.mulVecLin.range ≤ B.mulVecLin.range) :
    ∃ C : Mat, A = B * C := by
  classical
  have hcol : ∀ j : Fin D, ∃ c : Fin D → ℂ, B.mulVec c = A.col j := by
    intro j
    have hAj_mem : A.col j ∈ A.mulVecLin.range := by
      refine ⟨Pi.single j 1, ?_⟩
      change A.mulVec (Pi.single j 1) = A.col j
      exact Matrix.mulVec_single_one A j
    have hBj_mem : A.col j ∈ B.mulVecLin.range := hAB hAj_mem
    rcases hBj_mem with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [Matrix.mulVecLin_apply] using hc
  choose c hc using hcol
  let C : Mat := fun i j => c j i
  refine ⟨C, ?_⟩
  apply Matrix.ext_col
  intro j
  have hCcol : C.col j = c j := by ext i; rfl
  calc
    A.col j = B.mulVec (c j) := by symm; exact hc j
    _ = B.mulVec (C.col j) := by rw [hCcol]
    _ = B.mulVec (C.mulVec (Pi.single j 1)) := by rw [Matrix.mulVec_single_one]
    _ = (B * C).mulVec (Pi.single j 1) := by
      simpa using (Matrix.mulVec_mulVec (Pi.single j 1) B C)
    _ = (B * C).col j := by exact Matrix.mulVec_single_one (B * C) j

theorem factorization_of_forall_mulVec_mem_range
    {A B : Mat} (hAB : ∀ v : Fin D → ℂ, A.mulVec v ∈ B.mulVecLin.range) :
    ∃ C : Mat, A = B * C := by
  apply factorization_of_range_mulVecLin_le
  intro w hw; rcases hw with ⟨v, rfl⟩
  simpa [Matrix.mulVecLin_apply] using hAB v

noncomputable def pinv (B : Mat) : Mat :=
  Bᴴ * (Matrix.PosSemidef.supportInv (Matrix.posSemidef_self_mul_conjTranspose B))

abbrev posSemidefBB (B : Mat) : (B * Bᴴ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose B

theorem mul_pinv_eq_supportProj (B : Mat) :
    B * pinv B = (posSemidefBB B).supportProj := by
  unfold pinv
  have h := (posSemidefBB B).self_mul_supportInv
  calc
    B * (Bᴴ * (posSemidefBB B).supportInv) = (B * Bᴴ) * (posSemidefBB B).supportInv := by
      simp [Matrix.mul_assoc]
    _ = (posSemidefBB B).isHermitian.supportProj := h
    _ = (posSemidefBB B).supportProj := rfl

/-! ### Lemma: If A = B·C then AA† ≤ ‖C‖²·BB† -/

theorem le_norm_sq_mul_of_factorization (A B C : Mat) (hA : A = B * C) :
    A * Aᴴ ≤ (‖C‖ ^ 2 : ℝ) • (B * Bᴴ) := by
  rw [hA]
  rw [Matrix.le_iff]
  have h_BCstar : (B * C) * (B * C)ᴴ = B * (C * Cᴴ) * Bᴴ := by
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rw [h_BCstar]
  let s : ℂ := (‖C‖ ^ 2 : ℝ)
  let D := s • (B * Bᴴ) - (B * (C * Cᴴ) * Bᴴ)
  have hD_herm : D.IsHermitian := by
    have hBB_herm : (B * Bᴴ).IsHermitian := (posSemidefBB B).isHermitian
    have h_CC_herm : (C * Cᴴ).IsHermitian := (posSemidefBB C).isHermitian
    have h_s : IsSelfAdjoint s := by
      dsimp [s, IsSelfAdjoint]
      simp
    have h1 : (s • (B * Bᴴ)).IsHermitian := hBB_herm.smul h_s
    have h2 : (B * (C * Cᴴ) * Bᴴ).IsHermitian := by
      have h2' : (B * (C * Cᴴ) * Bᴴ)ᴴ = B * (C * Cᴴ) * Bᴴ := by
        simp [h_CC_herm.eq]
      simpa [Matrix.IsHermitian] using h2'
    exact h1.sub h2
  have hD_nonneg : ∀ x, 0 ≤ star x ⬝ᵥ (D *ᵥ x) := by
    intro x
    set y := Bᴴ *ᵥ x
    set z := Cᴴ *ᵥ y
    have h_alpha : star x ⬝ᵥ ((B * Bᴴ) *ᵥ x) = star y ⬝ᵥ y := by
      calc
        star x ⬝ᵥ ((B * Bᴴ) *ᵥ x) = star x ⬝ᵥ (B *ᵥ (Bᴴ *ᵥ x)) := by
          rw [Matrix.mulVec_mulVec]
        _ = star (Bᴴ *ᵥ x) ⬝ᵥ (Bᴴ *ᵥ x) := star_dotProduct_mulVec B x (Bᴴ *ᵥ x)
        _ = star y ⬝ᵥ y := rfl
    have h_beta : star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x) = star z ⬝ᵥ z := by
      calc
        star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x) =
            star x ⬝ᵥ (B *ᵥ ((C * Cᴴ) *ᵥ (Bᴴ *ᵥ x))) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = star (Bᴴ *ᵥ x) ⬝ᵥ ((C * Cᴴ) *ᵥ (Bᴴ *ᵥ x)) :=
          star_dotProduct_mulVec B x _
        _ = star (Bᴴ *ᵥ x) ⬝ᵥ (C *ᵥ (Cᴴ *ᵥ (Bᴴ *ᵥ x))) := by
          rw [Matrix.mulVec_mulVec]
        _ = star (Cᴴ *ᵥ (Bᴴ *ᵥ x)) ⬝ᵥ (Cᴴ *ᵥ (Bᴴ *ᵥ x)) :=
          star_dotProduct_mulVec C (Bᴴ *ᵥ x) _
        _ = star z ⬝ᵥ z := rfl
    have h_Dx_split : D *ᵥ x = (s • (B * Bᴴ)) *ᵥ x - (B * (C * Cᴴ) * Bᴴ) *ᵥ x := by
      rw [sub_mulVec]
    have h_dot_sub (u v : Fin D → ℂ) : star x ⬝ᵥ (u - v) = star x ⬝ᵥ u - star x ⬝ᵥ v := by
      simp only [dotProduct, Finset.sum_sub_distrib, mul_sub, Pi.sub_apply]
    have h_dot : star x ⬝ᵥ (D *ᵥ x) =
        star x ⬝ᵥ ((s • (B * Bᴴ)) *ᵥ x) -
        star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x) := by
      rw [h_Dx_split, h_dot_sub]
    have h_first : star x ⬝ᵥ ((s • (B * Bᴴ)) *ᵥ x) = s • (star y ⬝ᵥ y) := by
      simp [smul_mulVec, h_alpha, s]
    rw [h_first, h_beta] at h_dot
    rw [h_dot]
    have hy_nonneg : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
    have hz_nonneg : 0 ≤ star z ⬝ᵥ z := dotProduct_star_self_nonneg z
    have h_norm_bound : RCLike.re (star z ⬝ᵥ z) ≤
        ‖C‖ ^ 2 * RCLike.re (star y ⬝ᵥ y) := by
      have h := re_star_dotProduct_mulVec_le_opNorm_sq Cᴴ y
      have h_norm_Cstar : ‖Cᴴ‖ = ‖C‖ := Matrix.l2_opNorm_conjTranspose C
      rw [h_norm_Cstar] at h
      simpa [z] using h
    rw [Complex.nonneg_iff]
    constructor
    · have hy_re_nonneg : 0 ≤ RCLike.re (star y ⬝ᵥ y) :=
        (Complex.nonneg_iff.mp hy_nonneg).1
      have hs_real : RCLike.re s = ‖C‖ ^ 2 := by
        simp [s]
      simp [RCLike.re_sub, RCLike.re_smul_ofReal, s, hs_real]
      nlinarith
    · have hy_im_zero : RCLike.im (star y ⬝ᵥ y) = 0 :=
        (Complex.nonneg_iff.mp hy_nonneg).2
      have hz_im_zero : RCLike.im (star z ⬝ᵥ z) = 0 :=
        (Complex.nonneg_iff.mp hz_nonneg).2
      simp [RCLike.im_sub, RCLike.im_smul, s, hy_im_zero, hz_im_zero]
  have h_s_eq : s • (B * Bᴴ) = (‖C‖ ^ 2 : ℝ) • (B * Bᴴ) := by simp [s]
  rw [h_s_eq]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD_herm hD_nonneg

theorem supportProj_mul_eq_of_conjTranspose_le (A B : Mat) (μ : ℝ) (_hμ : 0 ≤ μ)
    (hle : A * Aᴴ ≤ μ • (B * Bᴴ)) :
    (posSemidefBB B).supportProj * A = A := by
  let P := (posSemidefBB B).supportProj
  let Q := 1 - P
  have hQ_herm : Qᴴ = Q := by
    have hP_herm := (posSemidefBB B).supportProj_isHermitian
    simp [Q, P, hP_herm.eq]
  have hQ_mul_BBstar : Q * (B * Bᴴ) = 0 := by
    have hP_mul_BBstar : P * (B * Bᴴ) = B * Bᴴ :=
      (posSemidefBB B).supportProj_mul_self
    dsimp [Q, P]
    calc
      (1 - P) * (B * Bᴴ) = (B * Bᴴ) - P * (B * Bᴴ) := by simp [Matrix.sub_mul]
      _ = (B * Bᴴ) - (B * Bᴴ) := by rw [hP_mul_BBstar]
      _ = 0 := by simp
  have h_conj_ineq : Q * (A * Aᴴ) * Q ≤ Q * (μ • (B * Bᴴ)) * Q := by
    rw [Matrix.le_iff] at hle ⊢
    have hdiff : Q * (μ • (B * Bᴴ)) * Q - Q * (A * Aᴴ) * Q =
        Q * ((μ • (B * Bᴴ)) - A * Aᴴ) * Qᴴ := by
      simp [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, hQ_herm]
    rw [hdiff]
    exact hle.mul_mul_conjTranspose_same Q
  have h_RHS : Q * (μ • (B * Bᴴ)) * Q = 0 := by
    calc
      Q * (μ • (B * Bᴴ)) * Q = (μ : ℂ) • (Q * (B * Bᴴ) * Q) := by simp
      _ = (μ : ℂ) • ((Q * (B * Bᴴ)) * Q) := by ring
      _ = (μ : ℂ) • (0 * Q) := by rw [hQ_mul_BBstar]
      _ = 0 := by simp
  rw [h_RHS] at h_conj_ineq
  have h_LHS : Q * (A * Aᴴ) * Q = (Q * A) * (Q * A)ᴴ := by
    calc
      Q * (A * Aᴴ) * Q = (Q * A) * (Aᴴ * Q) := by simp [Matrix.mul_assoc]
      _ = (Q * A) * ((Qᴴ * A)ᴴ) := by simp [Matrix.conjTranspose_mul, hQ_herm]
      _ = (Q * A) * (Q * A)ᴴ := by
        simp [Matrix.conjTranspose_mul, hQ_herm, Matrix.mul_assoc]
  rw [h_LHS] at h_conj_ineq
  have h_LHS_nonneg : 0 ≤ (Q * A) * (Q * A)ᴴ :=
    (Matrix.posSemidef_self_mul_conjTranspose (Q * A)).nonneg
  have h_sq_zero : (Q * A) * (Q * A)ᴴ = 0 :=
    le_antisymm h_conj_ineq h_LHS_nonneg
  have h_QA_zero : Q * A = 0 := (self_mul_conjTranspose_eq_zero.mp h_sq_zero)
  dsimp [P, Q] at h_QA_zero ⊢
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h_QA_zero
  exact h_QA_zero.symm

theorem douglas_tfae (A B : Mat) : List.TFAE [
    A.mulVecLin.range ≤ B.mulVecLin.range,
    ∃ (μ : ℝ), 0 ≤ μ ∧ A * Aᴴ ≤ μ • (B * Bᴴ),
    ∃ C : Mat, A = B * C
  ] := by
  tfae_have h31 : 3 → 1 := by
    intro h; rcases h with ⟨C, hC⟩; subst hC
    intro x hx; rcases hx with ⟨v, rfl⟩
    refine ⟨C *ᵥ v, ?_⟩
    simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  tfae_have h12 : 1 → 2 := by
    intro hAB
    rcases factorization_of_range_mulVecLin_le hAB with ⟨C, hC⟩
    exact ⟨‖C‖ ^ 2, pow_two_nonneg _, le_norm_sq_mul_of_factorization A B C hC⟩
  tfae_have h23 : 2 → 3 := by
    intro h; rcases h with ⟨μ, hμ, hle⟩
    have hSPA : (posSemidefBB B).supportProj * A = A :=
      supportProj_mul_eq_of_conjTranspose_le A B μ hμ hle
    let C := pinv B * A
    have hBC : A = B * C := by
      calc
        A = (posSemidefBB B).supportProj * A := hSPA.symm
        _ = (B * pinv B) * A := by rw [mul_pinv_eq_supportProj B]
        _ = B * (pinv B * A) := by simp [Matrix.mul_assoc]
        _ = B * C := rfl
    refine ⟨C, hBC⟩
  tfae_finish

theorem factorization_pinv (A B : Mat) (hAB : A.mulVecLin.range ≤ B.mulVecLin.range) :
    B * (pinv B * A) = A := by
  have hSPA : (posSemidefBB B).supportProj * A = A := by
    rcases (douglas_tfae A B).out 0 1 hAB with ⟨μ, hμ, hle⟩
    exact supportProj_mul_eq_of_conjTranspose_le A B μ hμ hle
  calc
    B * (pinv B * A) = (B * pinv B) * A := by simp [Matrix.mul_assoc]
    _ = (posSemidefBB B).supportProj * A := by rw [mul_pinv_eq_supportProj B]
    _ = A := hSPA

end Douglas
