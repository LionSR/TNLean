/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import QICLean.Analysis.MatrixSqrt

/-!
# Unitary polar factors for two unital Kraus operators

Two square matrices satisfying both Kraus completeness identities have unitary
polar factors whose relative unitary commutes with their positive Gram matrix.
This is the first step of the simultaneous singular-value argument in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 1.

The result includes singular matrices. Unitary polar existence follows from
QICLean's Gram-equality extension theorem. No simultaneous diagonalization or
quantum-circuit construction is asserted in this module.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every square complex matrix has a unitary polar factor, including when it is
singular. This is the polar-completion step in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 1. -/
theorem exists_unitary_polar_factor (E : Matrix n n ℂ) :
    ∃ V : Matrix.unitaryGroup n ℂ,
      E = (V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E) := by
  apply exists_unitary_mul_eq_of_conjTranspose_mul_eq
  rw [conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self _
    (posSemidef_conjTranspose_mul_self E).nonneg]

/-- Equal unitary conjugations of a matrix imply that the relative unitary
commutes with it. This is the algebraic cancellation in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 1. -/
theorem commute_of_unitary_conj_eq (V W : Matrix.unitaryGroup n ℂ) (H : Matrix n n ℂ)
    (hconj : (V : Matrix n n ℂ) * H * (V : Matrix n n ℂ)ᴴ =
      (W : Matrix n n ℂ) * H * (W : Matrix n n ℂ)ᴴ) :
    Commute H ((V : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ)) := by
  change H * ((V : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ)) =
    ((V : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ)) * H
  have hV : (V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) = 1 := by
    simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hW : (W : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ) = 1 := by
    simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  calc
    _ = (V : Matrix n n ℂ)ᴴ *
        ((V : Matrix n n ℂ) * H * (V : Matrix n n ℂ)ᴴ) * W := by
      simp only [← mul_assoc, hV, one_mul]
    _ = (V : Matrix n n ℂ)ᴴ *
        ((W : Matrix n n ℂ) * H * (W : Matrix n n ℂ)ᴴ) * W := by rw [hconj]
    _ = _ := by simp only [mul_assoc, hW, mul_one]

/-- The output Gram matrix is the unitary conjugate of the input Gram matrix
under a unitary polar factor. -/
theorem mul_conjTranspose_eq_of_unitary_polar_factor (E : Matrix n n ℂ)
    (V : Matrix.unitaryGroup n ℂ)
    (hE : E = (V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E)) :
    E * Eᴴ = (V : Matrix n n ℂ) * (Eᴴ * E) * (V : Matrix n n ℂ)ᴴ := by
  calc
    _ = ((V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E)) *
        ((V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E))ᴴ :=
      congrArg (fun X : Matrix n n ℂ => X * Xᴴ) hE
    _ = (V : Matrix n n ℂ) *
        (CFC.sqrt (Eᴴ * E) * CFC.sqrt (Eᴴ * E)) * (V : Matrix n n ℂ)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_cfc_sqrt, mul_assoc]
    _ = _ := by
      rw [CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self E).nonneg]

/-- Both Kraus completeness identities force the two polar factors to give the
same unitary conjugation of the first input Gram matrix.

This is the identity before the relative-polar commutation conclusion in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 1. -/
theorem unitary_polar_conj_eq_of_two_kraus
    (E F : Matrix n n ℂ) (V W : Matrix.unitaryGroup n ℂ)
    (htrace : Eᴴ * E + Fᴴ * F = 1) (hunital : E * Eᴴ + F * Fᴴ = 1)
    (hE : E = (V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E))
    (hF : F = (W : Matrix n n ℂ) * CFC.sqrt (Fᴴ * F)) :
    (V : Matrix n n ℂ) * (Eᴴ * E) * (V : Matrix n n ℂ)ᴴ =
      (W : Matrix n n ℂ) * (Eᴴ * E) * (W : Matrix n n ℂ)ᴴ := by
  have hW : (W : Matrix n n ℂ) * (W : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, star_eq_conjTranspose] using Unitary.coe_mul_star_self W
  have htotal : (W : Matrix n n ℂ) * (Eᴴ * E) * (W : Matrix n n ℂ)ᴴ +
      (W : Matrix n n ℂ) * (Fᴴ * F) * (W : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [mul_add, add_mul, mul_one, hW] using
      congrArg (fun X : Matrix n n ℂ => (W : Matrix n n ℂ) * X *
        (W : Matrix n n ℂ)ᴴ) htrace
  have hsum : (V : Matrix n n ℂ) * (Eᴴ * E) * (V : Matrix n n ℂ)ᴴ +
      (W : Matrix n n ℂ) * (Fᴴ * F) * (W : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [← mul_conjTranspose_eq_of_unitary_polar_factor E V hE,
      ← mul_conjTranspose_eq_of_unitary_polar_factor F W hF] using hunital
  exact add_right_cancel (hsum.trans htotal.symm)

/-- Two square Kraus operators defining a trace-preserving unital map have
unitary polar factors whose relative unitary commutes with the first Gram matrix.

This is the first structural reduction in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 1. Simultaneous
diagonalization and the resulting circuit theorem are separate statements. -/
theorem exists_commuting_unitary_polar_factors
    (E F : Matrix n n ℂ) (htrace : Eᴴ * E + Fᴴ * F = 1)
    (hunital : E * Eᴴ + F * Fᴴ = 1) :
    ∃ V W : Matrix.unitaryGroup n ℂ,
      E = (V : Matrix n n ℂ) * CFC.sqrt (Eᴴ * E) ∧
      F = (W : Matrix n n ℂ) * CFC.sqrt (Fᴴ * F) ∧
      Commute (Eᴴ * E) ((V : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ)) := by
  obtain ⟨V, hV⟩ := exists_unitary_polar_factor E
  obtain ⟨W, hW⟩ := exists_unitary_polar_factor F
  exact ⟨V, W, hV, hW, commute_of_unitary_conj_eq V W (Eᴴ * E)
    (unitary_polar_conj_eq_of_two_kraus E F V W htrace hunital hV hW)⟩

end Matrix
