/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Auxiliary matrix lemmas

General-purpose matrix lemmas that are not specific to any chapter's theory.
Extracted from various files for reusability.

## Main results

- `Matrix.sum_mul_mul`: pull fixed left/right factors through a finite sum
- `Matrix.dim_le_of_mulVec_injective`: injective mulVec implies dimension bound
- `ker_add_psd_left/right`: kernel containment for PSD matrix sums
- `Complex.conj_eq_inv_of_norm_eq_one`: conjugation = inversion on the unit circle
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

/-- Pull fixed left and right matrix factors through a finite sum indexed by `Fin d`. -/
theorem sum_mul_mul {α : Type*} [NonUnitalNonAssocSemiring α]
    {d l m n r : ℕ} (L : Matrix (Fin l) (Fin m) α)
    (M : Fin d → Matrix (Fin m) (Fin n) α) (R : Matrix (Fin n) (Fin r) α) :
    ∑ i : Fin d, L * M i * R = L * (∑ i : Fin d, M i) * R := by
  calc
    ∑ i : Fin d, L * M i * R = (∑ i : Fin d, L * M i) * R := by
      simpa [Matrix.mul_assoc] using
        (Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => L * M i) (M := R)).symm
    _ = (L * ∑ i : Fin d, M i) * R := by
      exact congrArg (fun T => T * R) <|
        (Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => M i) (M := L)).symm

/-- If multiplication by a rectangular matrix has trivial kernel, then the source dimension is at
most the target dimension. -/
theorem dim_le_of_mulVec_injective {D₁ D₂ : ℕ} [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h_inj : ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0) :
    D₂ ≤ D₁ := by
  let f : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ) := Matrix.toLin' X
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h_sub : f (u - v) = 0 := by
      simpa using congrArg (fun w => w - f v) huv
    exact sub_eq_zero.mp <| h_inj _ h_sub
  have hfinrank : Module.finrank ℂ (Fin D₂ → ℂ) ≤ Module.finrank ℂ (Fin D₁ → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hf_inj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hfinrank

end Matrix

/-! ## Kernel intersection for PSD matrices -/

section KernelPSD

open Matrix Finset

variable {D : ℕ}

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(A)`.
Proof: `v†(A+B)v = v†Av + v†Bv = 0` with both nonneg implies `v†Av = 0`. -/
theorem ker_add_psd_left
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have hqf : star v ⬝ᵥ ((A + B) *ᵥ v) = 0 := by rw [hv]; simp
  rw [add_mulVec, dotProduct_add] at hqf
  have h1_re := hA.re_dotProduct_nonneg v
  have h2_re := hB.re_dotProduct_nonneg v
  have h3_re : (star v ⬝ᵥ (A *ᵥ v)).re + (star v ⬝ᵥ (B *ᵥ v)).re = 0 := by
    have := congr_arg Complex.re hqf; simpa using this
  change 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re at h1_re
  change 0 ≤ (star v ⬝ᵥ (B *ᵥ v)).re at h2_re
  have hre : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := by linarith
  exact (hA.dotProduct_mulVec_zero_iff v).mp
    (Complex.ext hre (hA.isHermitian.im_star_dotProduct_mulVec_self v))

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(B)`. -/
theorem ker_add_psd_right
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    B *ᵥ v = 0 := by
  exact ker_add_psd_left hB hA v (by simpa [add_comm] using hv)

end KernelPSD

/-! ## Unit circle conjugation -/

/-- On the unit circle, complex conjugation equals inversion: `conj α = α⁻¹` when `‖α‖ = 1`. -/
lemma Complex.conj_eq_inv_of_norm_eq_one {α : ℂ} (h : ‖α‖ = 1) :
    starRingEnd ℂ α = α⁻¹ := by
  have hα_ne : α ≠ 0 := norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)
  have hconj_mul : starRingEnd ℂ α * α = 1 := by
    have hnormSq : Complex.normSq α = 1 := by
      rw [Complex.normSq_eq_norm_sq]; simp [h]
    calc starRingEnd ℂ α * α
        = (↑(Complex.normSq α) : ℂ) := by
          simpa using (Complex.normSq_eq_conj_mul_self (z := α)).symm
      _ = 1 := by simp [hnormSq]
  exact mul_right_cancel₀ hα_ne (by rw [hconj_mul, inv_mul_cancel₀ hα_ne])

/-! ## Characteristic polynomial lemmas -/

section CharpolyAux

open Polynomial

lemma scalar_mul_sub_smul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    Matrix.scalar n (c * z) - c • M = c • (Matrix.scalar n z - M) := by
  ext i j
  simp [Matrix.scalar, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, smul_eq_mul]
  split <;> ring

lemma eval_charpoly_smul_mul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    (c • M).charpoly.eval (c * z) = c ^ Fintype.card n * M.charpoly.eval z := by
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, scalar_mul_sub_smul, Matrix.det_smul]

theorem charpoly_eq_of_smul_charpoly_eq {n : Type*} [DecidableEq n] [Fintype n]
    (c : ℂ) (hc : c ≠ 0) (T U : Matrix n n ℂ)
    (h : (c • T).charpoly = (c • U).charpoly) :
    T.charpoly = U.charpoly := by
  have hcn : c ^ Fintype.card n ≠ 0 := pow_ne_zero _ hc
  apply Polynomial.funext
  intro z
  have h1 := eval_charpoly_smul_mul c z T
  have h2 := eval_charpoly_smul_mul c z U
  have h3 : (c • T).charpoly.eval (c * z) = (c • U).charpoly.eval (c * z) := by rw [h]
  rw [h1] at h3; rw [h2] at h3
  exact mul_left_cancel₀ hcn h3

theorem trace_eq_of_charpoly_eq
    {D : ℕ} [NeZero D]
    (T U : Matrix (Fin D) (Fin D) ℂ)
    (h : T.charpoly = U.charpoly) :
    Matrix.trace T = Matrix.trace U := by
  have : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (NeZero.pos D)
  have hT := Matrix.trace_eq_neg_charpoly_coeff T
  have hU := Matrix.trace_eq_neg_charpoly_coeff U
  rw [hT, hU, h]

end CharpolyAux
