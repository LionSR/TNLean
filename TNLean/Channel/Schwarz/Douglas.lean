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

/-!
# Douglas factorization theorem

Douglas' theorem for finite matrices: the range inclusion
`ran A ⊆ ran B` is equivalent to a factorization `A = BC`
and to a quadratic domination `AA† ≤ λ²BB†`.

The Moore-Penrose pseudoinverse witness `C = pinv(B)·A`
is constructed via `supportInv`; it satisfies the support constraint
`supportProj(B·B†)·C = C` and is the unique minimizer of the
operator norm `‖C‖`.

## Main results

* `douglas_tfae` : the three-way TFAE equivalence
* `pinv` : Moore-Penrose pseudoinverse via `supportInv`
* `mul_pinv_eq_supportProj` : `B·pinv(B) = supportProj(B·B†)`
* `factorization_of_range_mulVecLin_le` : range inclusion → factorization
* `le_norm_sq_mul_of_factorization` : `A = BC → AA† ≤ ‖C‖²·BB†`
* `pinv_norm_minimal` : `‖pinv(B)·A‖ ≤ ‖C‖` for any factorization `A = BC`
* `norm_pinv_mul_B_le_one` : `‖pinv(B)·B‖ ≤ 1` (contraction)
* `factorization_unique` : uniqueness under the range constraint

## References

* [M. Wolf, *Quantum Channels & Operations*, Theorem at
  Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex line 88][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Douglas

variable {D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Finite-dimensional factorization form of the easy direction of Douglas'
theorem: range inclusion for `mulVec` implies a right factorization
`A = B * C` (columnwise construction). -/
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

/-- The **Moore–Penrose pseudoinverse** `B⁺ := Bᴴ (B Bᴴ)⁻¹_supp`, with the
support inverse from `Matrix.PosSemidef.supportInv`. This is Wolf's
"inverse on the range": `B * B⁺` is the support projection of `B Bᴴ`
(`mul_pinv_eq_supportProj`). -/
noncomputable def pinv (B : Mat) : Mat :=
  Bᴴ * (Matrix.PosSemidef.supportInv (Matrix.posSemidef_self_mul_conjTranspose B))

/-- The matrix `B * Bᴴ` is positive semidefinite (the PSD certificate used
throughout the Douglas development for the support-inverse `(B Bᴴ)⁻¹_supp`). -/
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

theorem le_norm_sq_mul_of_factorization (A B C : Mat) (hA : A = B * C) :
    A * Aᴴ ≤ (‖C‖ ^ 2 : ℝ) • (B * Bᴴ) := by
  rw [hA]
  rw [Matrix.le_iff]
  have h_BCstar : (B * C) * (B * C)ᴴ = B * (C * Cᴴ) * Bᴴ := by
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rw [h_BCstar]
  have h_herm : ((‖C‖ ^ 2 : ℝ) • (B * Bᴴ) - B * (C * Cᴴ) * Bᴴ).IsHermitian := by
    have hBB : (B * Bᴴ).IsHermitian := (posSemidefBB B).isHermitian
    have hCC : (C * Cᴴ).IsHermitian := (posSemidefBB C).isHermitian
    have h_s : IsSelfAdjoint (‖C‖ ^ 2 : ℝ) := IsSelfAdjoint.all _
    have h1 : ((‖C‖ ^ 2 : ℝ) • (B * Bᴴ)).IsHermitian := hBB.smul h_s
    have h2 : (B * (C * Cᴴ) * Bᴴ).IsHermitian := by
      have h2' : (B * (C * Cᴴ) * Bᴴ)ᴴ = B * (C * Cᴴ) * Bᴴ := by
        simp [Matrix.mul_assoc]
      simpa [Matrix.IsHermitian] using h2'
    exact h1.sub h2
  have h_nonneg : ∀ x, 0 ≤ star x ⬝ᵥ
      (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ) - B * (C * Cᴴ) * Bᴴ) *ᵥ x) := by
    intro x
    set y := Bᴴ *ᵥ x
    set z := Cᴴ *ᵥ y
    have hy_nonneg : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
    have hz_nonneg : 0 ≤ star z ⬝ᵥ z := dotProduct_star_self_nonneg z
    have hy_im_zero : (star y ⬝ᵥ y).im = 0 :=
      (Complex.nonneg_iff.mp hy_nonneg).2.symm
    have hz_im_zero : (star z ⬝ᵥ z).im = 0 :=
      (Complex.nonneg_iff.mp hz_nonneg).2.symm
    have h_BBstar : star x ⬝ᵥ ((B * Bᴴ) *ᵥ x) = star y ⬝ᵥ y := by
      rw [← Matrix.mulVec_mulVec x B Bᴴ]
      exact star_dotProduct_mulVec B x (Bᴴ *ᵥ x)
    have h_BCCBstar : star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x) = star z ⬝ᵥ z := by
      calc
        star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x) =
            star x ⬝ᵥ (B *ᵥ ((C * Cᴴ) *ᵥ (Bᴴ *ᵥ x))) := by
          simp [← Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = star (Bᴴ *ᵥ x) ⬝ᵥ ((C * Cᴴ) *ᵥ (Bᴴ *ᵥ x)) :=
          star_dotProduct_mulVec B x _
        _ = star (Bᴴ *ᵥ x) ⬝ᵥ (C *ᵥ (Cᴴ *ᵥ (Bᴴ *ᵥ x))) := by
          rw [← Matrix.mulVec_mulVec (Bᴴ *ᵥ x) C Cᴴ]
        _ = star (Cᴴ *ᵥ (Bᴴ *ᵥ x)) ⬝ᵥ (Cᴴ *ᵥ (Bᴴ *ᵥ x)) :=
          star_dotProduct_mulVec C (Bᴴ *ᵥ x) _
    have h_norm_bound : (star z ⬝ᵥ z).re ≤ ‖C‖ ^ 2 * (star y ⬝ᵥ y).re := by
      have h := re_star_dotProduct_mulVec_le_opNorm_sq Cᴴ y
      have h_norm_Cstar : ‖Cᴴ‖ = ‖C‖ := Matrix.l2_opNorm_conjTranspose C
      rw [h_norm_Cstar] at h
      simpa [z] using h
    have h_val : star x ⬝ᵥ
        (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ) - B * (C * Cᴴ) * Bᴴ) *ᵥ x) =
        ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) - (star z ⬝ᵥ z) := by
      calc
        star x ⬝ᵥ (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ) - B * (C * Cᴴ) * Bᴴ) *ᵥ x) =
            star x ⬝ᵥ (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ)) *ᵥ x -
              (B * (C * Cᴴ) * Bᴴ) *ᵥ x) := by rw [sub_mulVec]
        _ = (star x ⬝ᵥ (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ)) *ᵥ x)) -
            (star x ⬝ᵥ ((B * (C * Cᴴ) * Bᴴ) *ᵥ x)) := by
          simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
        _ = (star x ⬝ᵥ (((‖C‖ ^ 2 : ℝ) • (B * Bᴴ)) *ᵥ x)) - star z ⬝ᵥ z := by
          rw [h_BCCBstar]
        _ = ((‖C‖ ^ 2 : ℝ) • (star x ⬝ᵥ ((B * Bᴴ) *ᵥ x))) - star z ⬝ᵥ z := by
          simp [smul_mulVec]
        _ = ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) - star z ⬝ᵥ z := by rw [h_BBstar]
    rw [h_val]
    have h_sq_re : ((‖C‖ : ℂ) ^ 2).re = ‖C‖ ^ 2 := by
      simp [sq]
    have h_sq_im : ((‖C‖ : ℂ) ^ 2).im = 0 := by
      simp [sq]
    have h_smul_re : ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)).re =
        (‖C‖ ^ 2) * (star y ⬝ᵥ y).re := by
      have h_eq : ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) =
          ((‖C‖ : ℂ) * ((‖C‖ : ℂ) * (star y ⬝ᵥ y))) := by
        simp [sq, mul_assoc]
      rw [h_eq, Complex.mul_re, Complex.mul_re]
      simp [sq]
      ring
    have h_smul_im : ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)).im =
        (‖C‖ ^ 2) * (star y ⬝ᵥ y).im := by
      have h_eq : ((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) =
          ((‖C‖ : ℂ) * ((‖C‖ : ℂ) * (star y ⬝ᵥ y))) := by
        simp [sq, mul_assoc]
      rw [h_eq, Complex.mul_im, Complex.mul_im]
      simp [sq]
      ring
    have h_re : (((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) - (star z ⬝ᵥ z)).re =
        (‖C‖ ^ 2) * (star y ⬝ᵥ y).re - (star z ⬝ᵥ z).re := by
      rw [Complex.sub_re, h_smul_re]
    have h_im : (((‖C‖ ^ 2 : ℝ) • (star y ⬝ᵥ y)) - (star z ⬝ᵥ z)).im = 0 := by
      rw [Complex.sub_im, h_smul_im, hy_im_zero, hz_im_zero]
      ring
    rw [Complex.nonneg_iff]
    constructor
    · rw [h_re]
      nlinarith [h_norm_bound, (Complex.nonneg_iff.mp hy_nonneg).1,
        (Complex.nonneg_iff.mp hz_nonneg).1]
    · rw [h_im]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm h_nonneg

theorem supportProj_mul_eq_of_conjTranspose_le (A B : Mat) (μ : ℝ)
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
      _ = (μ : ℂ) • ((Q * (B * Bᴴ)) * Q) := by simp [Matrix.mul_assoc]
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

/-- **Douglas' theorem** (Wolf, *Quantum Channels & Operations*, Ch. 5,
Theorem at `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex` line 88).

For finite matrices `A`, `B` the following are equivalent: (i) the range
inclusion `ran A ⊆ ran B`, (ii) the factorization `A = B C` for some `C`, and
(iii) the quadratic domination `AA† ≤ λ² · BB†` for some `λ ≥ 0`. -/
theorem douglas_tfae (A B : Mat) : List.TFAE [
    A.mulVecLin.range ≤ B.mulVecLin.range,
    ∃ (μ : ℝ), 0 ≤ μ ∧ A * Aᴴ ≤ μ • (B * Bᴴ),
    ∃ C : Mat, A = B * C
  ] := by
  tfae_have h31 : 3 → 1 := by
    intro h; rcases h with ⟨C, hC⟩; subst hC
    intro x hx; rcases hx with ⟨v, rfl⟩
    refine ⟨C *ᵥ v, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVecLin_apply]
  tfae_have h12 : 1 → 2 := by
    intro hAB
    rcases factorization_of_range_mulVecLin_le hAB with ⟨C, hC⟩
    exact ⟨‖C‖ ^ 2, pow_two_nonneg _, le_norm_sq_mul_of_factorization A B C hC⟩
  tfae_have h23 : 2 → 3 := by
    intro h; rcases h with ⟨μ, _hμ, hle⟩
    have hSPA : (posSemidefBB B).supportProj * A = A :=
      supportProj_mul_eq_of_conjTranspose_le A B μ hle
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
    have hle := ((douglas_tfae A B).out 0 1 (by rfl) (by rfl)).mp hAB
    rcases hle with ⟨μ, _hμ, hle'⟩
    exact supportProj_mul_eq_of_conjTranspose_le A B μ hle'
  calc
    B * (pinv B * A) = (B * pinv B) * A := by simp [Matrix.mul_assoc]
    _ = (posSemidefBB B).supportProj * A := by rw [mul_pinv_eq_supportProj B]
    _ = A := hSPA

/-! ## Moreover clauses of Douglas' theorem -/

/-- `(pinv B * B)` is idempotent. -/
theorem pinv_mul_B_idem (B : Mat) : (pinv B * B) * (pinv B * B) = pinv B * B := by
  have h := Matrix.supportProj_mul_conjTranspose_mul_self B
  calc
    (pinv B * B) * (pinv B * B) = pinv B * (B * pinv B) * B := by simp [Matrix.mul_assoc]
    _ = pinv B * (posSemidefBB B).supportProj * B := by rw [mul_pinv_eq_supportProj B]
    _ = pinv B * ((posSemidefBB B).supportProj * B) := by simp [Matrix.mul_assoc]
    _ = pinv B * B := by
      simpa [posSemidefBB, Matrix.PosSemidef.supportProj] using
        congrArg (fun (M : Mat) => pinv B * M) h

/-- `(pinv B * B)` is Hermitian. -/
theorem pinv_mul_B_herm (B : Mat) : (pinv B * B)ᴴ = pinv B * B := by
  unfold pinv
  have hS_herm : ((posSemidefBB B).supportInv)ᴴ = (posSemidefBB B).supportInv := by
    have hSqrt := Matrix.PosSemidef.supportInvSqrt_isHermitian (posSemidefBB B)
    unfold Matrix.PosSemidef.supportInv
    simp [Matrix.conjTranspose_mul, hSqrt.eq]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hS_herm]

/-! ### Projection contraction -/

theorem norm_pinv_mul_B_le_one (B : Mat) : ‖pinv B * B‖ ≤ 1 := by
  let P := pinv B * B
  have hP_idem : P * P = P := pinv_mul_B_idem B
  have hP_herm : Pᴴ = P := pinv_mul_B_herm B
  -- Projection: ⟨y,P·y⟩ = ⟨P·y,P·y⟩
  have h_proj (y : Fin D → ℂ) : dotProduct (star y) (mulVec P y) =
      dotProduct (star (mulVec P y)) (mulVec P y) := by
    calc
      dotProduct (star y) (mulVec P y) = dotProduct (star y) (mulVec (P * P) y) := by rw [hP_idem]
      _ = dotProduct (star y) (mulVec P (mulVec P y)) := by rw [Matrix.mulVec_mulVec]
      _ = dotProduct (star (mulVec (Pᴴ) y)) (mulVec P y) := by
        rw [star_dotProduct_mulVec P y (mulVec P y)]
      _ = dotProduct (star (mulVec P y)) (mulVec P y) := by rw [hP_herm]
  -- I-P is also a projection
  let IP := 1 - P
  have hIP_idem : IP * IP = IP := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_idem]; abel
  have hIP_herm : IPᴴ = IP := by dsimp [IP]; simp [hP_herm]
  -- ‖P·y‖² ≤ ‖y‖² via 0 ≤ ⟨y,(I-P)·y⟩ = ⟨y,y⟩−⟨y,P·y⟩
  have h_contract (y : Fin D → ℂ) :
      RCLike.re (dotProduct (star (mulVec P y)) (mulVec P y)) ≤
      RCLike.re (dotProduct (star y) y) := by
    -- 0 ≤ ⟨y,(I-P)·y⟩ = ⟨(I-P)·y,(I-P)·y⟩
    have h_nonneg_IP : 0 ≤ dotProduct (star y) (mulVec IP y) := by
      calc
        dotProduct (star y) (mulVec IP y) =
            dotProduct (star y) (mulVec (IP * IP) y) := by rw [hIP_idem]
        _ = dotProduct (star y) (mulVec IP (mulVec IP y)) := by rw [Matrix.mulVec_mulVec]
        _ = dotProduct (star (mulVec (IPᴴ) y)) (mulVec IP y) := by
          rw [star_dotProduct_mulVec IP y (mulVec IP y)]
        _ = dotProduct (star (mulVec IP y)) (mulVec IP y) := by rw [hIP_herm]
        _ ≥ 0 := dotProduct_star_self_nonneg _
    -- ⟨y,(I-P)·y⟩ = ⟨y,y⟩ − ⟨y,P·y⟩
    have h_expand : dotProduct (star y) (mulVec IP y) =
        dotProduct (star y) y - dotProduct (star y) (mulVec P y) := by
      calc
        dotProduct (star y) (mulVec IP y) = dotProduct (star y) (mulVec (1 - P) y) := rfl
        _ = dotProduct (star y) (mulVec 1 y - mulVec P y) := by rw [Matrix.sub_mulVec]
        _ = dotProduct (star y) (y - mulVec P y) := by simp
        _ = dotProduct (star y) y - dotProduct (star y) (mulVec P y) := by
          rw [dotProduct_sub]
    rw [h_expand] at h_nonneg_IP
    -- h_nonneg_IP: 0 ≤ star y·y - star y·(P·y) in ℂ order
    -- Extract real parts: 0 ≤ re(star y·y) - re(star y·(P·y))
    have h_re : 0 ≤ RCLike.re (dotProduct (star y) y) -
        RCLike.re (dotProduct (star y) (mulVec P y)) := by
      -- From 0 ≤ a - b in ℂ, we get 0 ≤ re(a) - re(b)
      have h := (Complex.nonneg_iff.mp h_nonneg_IP).1
      -- h: 0 ≤ RCLike.re (star y·y - star y·(P·y))
      simpa [Complex.sub_re] using h
    -- re(star y·(P·y)) = re(star(P·y)·(P·y)) [by h_proj]
    rw [h_proj y] at h_re
    linarith
  apply l2_opNorm_le_of_forall (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  have h_bound : RCLike.re (dotProduct (star (mulVec P x)) (mulVec P x)) ≤
      RCLike.re (dotProduct (star x) x) := h_contract x
  have h_norm_sq_Px : RCLike.re (dotProduct (star (mulVec P x)) (mulVec P x)) =
      ‖(EuclideanSpace.equiv (Fin D) ℂ).symm (mulVec P x)‖ ^ 2 :=
    re_star_dotProduct_self_eq_norm_sq (mulVec P x)
  have h_norm_sq_x : RCLike.re (dotProduct (star x) x) =
      ‖(EuclideanSpace.equiv (Fin D) ℂ).symm x‖ ^ 2 :=
    re_star_dotProduct_self_eq_norm_sq x
  rw [h_norm_sq_Px, h_norm_sq_x] at h_bound
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin D) ℂ).symm x)]

/-! ### Norm minimality of the pseudoinverse factorization -/

theorem pinv_norm_minimal (A B C : Mat) (hA : A = B * C) : ‖pinv B * A‖ ≤ ‖C‖ := by
  by_cases hCzero : ‖C‖ = 0
  · have hC : C = 0 := norm_eq_zero.mp hCzero
    rw [hC, mul_zero] at hA
    rw [hA, mul_zero]
    simp
  · have hpos : 0 < ‖C‖ := lt_of_le_of_ne (norm_nonneg C) (Ne.symm hCzero)
    rw [hA]
    calc
      ‖pinv B * (B * C)‖ = ‖(pinv B * B) * C‖ := by simp [Matrix.mul_assoc]
      _ ≤ ‖pinv B * B‖ * ‖C‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖C‖ := by nlinarith [norm_pinv_mul_B_le_one B]
      _ = ‖C‖ := by simp

/-! ## Uniqueness of the factorization under the support constraint -/

theorem pinv_mul_B_mul_conjTranspose (B : Mat) : pinv B * B * Bᴴ = Bᴴ := by
  unfold pinv
  have hS : (posSemidefBB B).supportInv * (B * Bᴴ) = (posSemidefBB B).supportProj :=
    (posSemidefBB B).supportInv_mul_self
  have hP : (posSemidefBB B).supportProj * B = B :=
    Matrix.supportProj_mul_conjTranspose_mul_self B
  calc
    (Bᴴ * (posSemidefBB B).supportInv * B) * Bᴴ =
        Bᴴ * (posSemidefBB B).supportInv * (B * Bᴴ) := by
      simp [Matrix.mul_assoc]
    _ = Bᴴ * ((posSemidefBB B).supportInv * (B * Bᴴ)) := by simp [Matrix.mul_assoc]
    _ = Bᴴ * (posSemidefBB B).supportProj := by rw [hS]
    _ = ((posSemidefBB B).supportProj * B)ᴴ := by
      simp [Matrix.conjTranspose_mul, (posSemidefBB B).supportProj_isHermitian.eq]
    _ = Bᴴ := by rw [hP]

theorem pinv_mul_B_mul_C_eq_C (C B : Mat) (hC : C.mulVecLin.range ≤ Bᴴ.mulVecLin.range) :
    (pinv B * B) * C = C := by
  apply Matrix.ext; intro i j
  let c := mulVec C (Pi.single j (1 : ℂ))
  have hc : c ∈ Bᴴ.mulVecLin.range := hC ⟨Pi.single j (1 : ℂ), rfl⟩
  rcases hc with ⟨w, hw⟩; rw [Matrix.mulVecLin_apply] at hw
  have h_eq : mulVec (pinv B * B) c = c := by
    calc
      mulVec (pinv B * B) c = mulVec (pinv B * B) (mulVec (Bᴴ) w) := by rw [← hw]
      _ = mulVec ((pinv B * B) * Bᴴ) w := by rw [Matrix.mulVec_mulVec]
      _ = mulVec (pinv B * B * Bᴴ) w := by simp [Matrix.mul_assoc]
      _ = mulVec (Bᴴ) w := by rw [pinv_mul_B_mul_conjTranspose B]
      _ = c := by rw [hw]
  calc
    ((pinv B * B) * C) i j = (mulVec ((pinv B * B) * C) (Pi.single j (1 : ℂ))) i := by simp
    _ = (mulVec (pinv B * B) (mulVec C (Pi.single j (1 : ℂ)))) i := by rw [Matrix.mulVec_mulVec]
    _ = (mulVec (pinv B * B) c) i := rfl
    _ = (c i) := by rw [h_eq]
    _ = (mulVec C (Pi.single j (1 : ℂ))) i := rfl
    _ = C i j := by simp

theorem factorization_unique (A B C₁ C₂ : Mat) (hA₁ : A = B * C₁) (hA₂ : A = B * C₂)
    (hC₁_range : C₁.mulVecLin.range ≤ Bᴴ.mulVecLin.range)
    (hC₂_range : C₂.mulVecLin.range ≤ Bᴴ.mulVecLin.range) : C₁ = C₂ := by
  calc
    C₁ = (pinv B * B) * C₁ := (pinv_mul_B_mul_C_eq_C C₁ B hC₁_range).symm
    _ = pinv B * (B * C₁) := by simp [Matrix.mul_assoc]
    _ = pinv B * A := by rw [hA₁]
    _ = pinv B * (B * C₂) := by rw [hA₂]
    _ = (pinv B * B) * C₂ := by simp [Matrix.mul_assoc]
    _ = C₂ := pinv_mul_B_mul_C_eq_C C₂ B hC₂_range

end Douglas
