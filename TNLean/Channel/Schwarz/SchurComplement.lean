/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.Douglas
import TNLean.Analysis.MatrixSqrt
import Mathlib.Data.Matrix.Block

/-!
# Block Schur complements

For a self-adjoint 2×2 block matrix `M = [[P, Q], [Q†, R]]`
with `P, R` PSD, the following are equivalent:

1. `M` is PSD
2. `ker(R) ⊆ ker(Q)` and the pseudoinverse Schur complement `P − Q·R⁺·Q†` is PSD
3. `ker(R) ⊆ ker(Q)` and `‖P^{-1/2}·Q·R^{-1/2}‖ ≤ 1` (contraction form)

This file proves:
* `ker_subset_of_block_psd` and `schur_of_block_psd` : (1) ⟹ (2)
* `block_psd_of_schur` : (2) ⟹ (1)
* The equivalence with (3) (contraction form) is deferred to a follow-up.

## Key lemmas

* `supportProj_sq_eq_supportProj` : R² has the same support projection as R
* `pinv_eq_supportInv` : for PSD R, `Douglas.pinv R = hR.supportInv`
* `pinv_mul_R_eq_supportProj` : `pinv R * R = supportProj R`
* `pinv_isHermitian` : `Douglas.pinv R` is Hermitian for PSD R
* `pinv_mul_R_mul_pinv_eq_pinv` : Moore-Penrose condition (2)

## References
* [M. Wolf, *Quantum Channels & Operations*, Theorem 5.2][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace SchurComplement

variable {D₁ D₂ : ℕ}

def blockMatrix (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix ((Fin D₁) ⊕ (Fin D₂)) ((Fin D₁) ⊕ (Fin D₂)) ℂ :=
  Matrix.fromBlocks P Q (Qᴴ) R

/-- The block matrix `[[P, Q], [Q†, R]]` is Hermitian when its diagonal
blocks `P` and `R` are Hermitian. -/
theorem blockMatrix_isHermitian (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.IsHermitian) (hR : R.IsHermitian) : (blockMatrix P Q R).IsHermitian := by
  rw [Matrix.IsHermitian, blockMatrix]
  simp [Matrix.fromBlocks_conjTranspose, hP.eq, hR.eq]

noncomputable def schurComplement (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin D₁) (Fin D₁) ℂ :=
  P - Q * (Douglas.pinv R) * (Qᴴ)

theorem block_quadratic_form (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (x : Fin D₁ → ℂ) (y : Fin D₂ → ℂ) :
    dotProduct (star (Sum.elim x y)) (mulVec (blockMatrix P Q R) (Sum.elim x y)) =
    dotProduct (star x) (mulVec P x) + dotProduct (star x) (mulVec Q y) +
    dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star y) (mulVec R y) := by
  simp [blockMatrix, Matrix.fromBlocks_mulVec, dotProduct_add, Matrix.add_mulVec, Matrix.mulVec_add,
    dotProduct, Matrix.mulVec, Finset.sum_add_distrib]

/-! ### supportProj(R²) = supportProj(R) -/

theorem supportProj_sq_eq_supportProj (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef) :
    (hR.mul hR).supportProj = hR.supportProj := by
  have hR2 : (R * R).PosSemidef := hR.mul hR
  have hkerR_R2 (v : Fin D₂ → ℂ) (hv : R *ᵥ v = 0) : (R * R) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hkerR2_R (v : Fin D₂ → ℂ) (hv : (R * R) *ᵥ v = 0) : R *ᵥ v = 0 := by
    have hdot : star (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = 0 := by
      calc
        star (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = star v ⬝ᵥ (R *ᵥ (R *ᵥ v)) := by
          rw [star_dotProduct_mulVec R v (R *ᵥ v)]
        _ = star v ⬝ᵥ ((R * R) *ᵥ v) := by rw [← Matrix.mulVec_mulVec]
        _ = star v ⬝ᵥ 0 := by rw [hv]
        _ = 0 := dotProduct_zero _
    exact dotProduct_star_self_eq_zero.mp hdot
  have hPR2_PR : hR2.supportProj * hR.supportProj = hR2.supportProj :=
    hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le fun v hv =>
      hR2.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v (hkerR_R2 v hv)
  have hPR_PR2 : hR.supportProj * hR2.supportProj = hR.supportProj :=
    hR2.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le fun v hv =>
      hR.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v (hkerR2_R v hv)
  have hPR_PR2' : hR.supportProj * hR2.supportProj = hR2.supportProj := by
    simpa [Matrix.conjTranspose_mul, hR.supportProj_isHermitian.eq,
      hR2.supportProj_isHermitian.eq] using congrArg Matrix.conjTranspose hPR2_PR
  exact hPR_PR2'.symm.trans hPR_PR2

/-! ### Key algebraic identities for `Douglas.pinv` on PSD `R` -/

section pinvAlgebra

variable (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef)

theorem R_mul_pinv_eq_supportProj : R * (Douglas.pinv R) = hR.supportProj := by
  rw [Douglas.mul_pinv_eq_supportProj R, hR.isHermitian.eq]
  exact supportProj_sq_eq_supportProj R hR

theorem supportProj_mul_pinv_eq_pinv : hR.supportProj * (Douglas.pinv R) = Douglas.pinv R := by
  unfold Douglas.pinv
  rw [hR.isHermitian.eq]
  calc
    hR.supportProj * (R * (hR.mul hR).supportInv) =
        (hR.supportProj * R) * (hR.mul hR).supportInv := by simp [Matrix.mul_assoc]
    _ = R * (hR.mul hR).supportInv := by rw [hR.supportProj_mul_self]

theorem pinv_eq_supportInv : Douglas.pinv R = hR.supportInv := by
  calc
    Douglas.pinv R = hR.supportProj * (Douglas.pinv R) :=
      (supportProj_mul_pinv_eq_pinv R hR).symm
    _ = (hR.supportInv * R) * (Douglas.pinv R) := by rw [hR.supportInv_mul_self]
    _ = hR.supportInv * (R * (Douglas.pinv R)) := by simp [Matrix.mul_assoc]
    _ = hR.supportInv * hR.supportProj := by rw [R_mul_pinv_eq_supportProj R hR]
    _ = hR.supportInv := hR.supportInv_mul_supportProj

theorem pinv_mul_R_eq_supportProj : (Douglas.pinv R) * R = hR.supportProj := by
  rw [pinv_eq_supportInv R hR]
  exact hR.supportInv_mul_self

theorem pinv_mul_R_mul_pinv_eq_pinv : (Douglas.pinv R) * R * (Douglas.pinv R) = Douglas.pinv R := by
  rw [pinv_mul_R_eq_supportProj R hR, supportProj_mul_pinv_eq_pinv R hR]

theorem pinv_isHermitian : (Douglas.pinv R).IsHermitian := by
  rw [pinv_eq_supportInv R hR]
  exact hR.supportInv_isHermitian

end pinvAlgebra

theorem mul_pinv_mul_R_eq_of_ker_subset (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hker : ∀ y : Fin D₂ → ℂ, mulVec R y = 0 → mulVec Q y = 0) :
    Q * (Douglas.pinv R) * R = Q := by
  rw [pinv_mul_R_eq_supportProj R hR]
  exact hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le (B := Q) hker

/-! ### Forward direction: block PSD → ker inclusion + Schur PSD -/

theorem ker_subset_of_block_psd (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hM : (blockMatrix P Q R).PosSemidef) (y : Fin D₂ → ℂ) (hRy : mulVec R y = 0) :
    mulVec Q y = 0 := by
  have h_quad : star (Sum.elim (0 : Fin D₁ → ℂ) y) ⬝ᵥ
      ((blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y) = 0 := by
    rw [block_quadratic_form P Q R 0 y]
    simp [hRy]
  have hMv_zero : (blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y = 0 :=
    ((Matrix.PosSemidef.dotProduct_mulVec_zero_iff hM _).mp h_quad)
  have h_comp : (blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y =
      Sum.elim (mulVec Q y) (mulVec R y) := by
    rw [blockMatrix, Matrix.fromBlocks_mulVec P Q (Qᴴ) R]
    simp [hRy]
  rw [h_comp] at hMv_zero
  have hQy_zero (i : Fin D₁) : mulVec Q y i = 0 := by
    have := congrFun hMv_zero (Sum.inl i)
    simpa using this
  ext i; exact hQy_zero i

theorem schur_of_block_psd (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hM : (blockMatrix P Q R).PosSemidef) (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (schurComplement P Q R).PosSemidef := by
  have hpinv_herm : (Douglas.pinv R).IsHermitian := pinv_isHermitian R hR
  have hpinv_mp2 : (Douglas.pinv R) * R * (Douglas.pinv R) = Douglas.pinv R :=
    pinv_mul_R_mul_pinv_eq_pinv R hR
  have h_schur_herm : (schurComplement P Q R).IsHermitian := by
    rw [Matrix.IsHermitian, schurComplement, Matrix.conjTranspose_sub, hP.isHermitian.eq,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpinv_herm.eq,
      Matrix.conjTranspose_conjTranspose]
    simp [Matrix.mul_assoc]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_schur_herm fun x => ?_
  set u := Qᴴ *ᵥ x with hu
  set y := -((Douglas.pinv R) *ᵥ u) with hy
  have h_block_quad : 0 ≤ dotProduct (star (Sum.elim x y))
      (mulVec (blockMatrix P Q R) (Sum.elim x y)) :=
    hM.dotProduct_mulVec_nonneg (Sum.elim x y)
  rw [block_quadratic_form P Q R x y] at h_block_quad
  have h_cross : dotProduct (star x) (mulVec Q y) + dotProduct (star y) (mulVec (Qᴴ) x)
      + dotProduct (star y) (mulVec R y) = -(dotProduct (star u) (mulVec (Douglas.pinv R) u)) := by
    have h_xQy : dotProduct (star x) (mulVec Q y) = -(dotProduct (star u) (mulVec (Douglas.pinv R) u)) := by
      rw [hy]
      simp only [dotProduct_neg_right, neg_mulVec, Matrix.mulVec_neg, dotProduct_neg_left]
      rw [← star_dotProduct_mulVec Q x ((Douglas.pinv R) *ᵥ u), hu]
      simp
    have h_yQx : dotProduct (star y) (mulVec (Qᴴ) x) = -(dotProduct (star u) (mulVec (Douglas.pinv R) u)) := by
      rw [hy, hu]
      simp only [dotProduct_neg_right, star_neg, neg_mulVec, dotProduct_neg_left]
      rw [hpinv_herm.star_mulVec_dotProduct u u]
    have h_yRy : dotProduct (star y) (mulVec R y) = dotProduct (star u) (mulVec (Douglas.pinv R) u) := by
      rw [hy]
      simp only [neg_mulVec, dotProduct_neg_right, star_neg, Matrix.mulVec_neg,
        dotProduct_neg_left, neg_neg]
      rw [← star_dotProduct_mulVec ((Douglas.pinv R)ᴴ * R) u ((Douglas.pinv R) *ᵥ u)]
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hpinv_herm.eq, hpinv_mp2]
    rw [h_xQy, h_yQx, h_yRy]
    ring
  have h_sum : dotProduct (star x) (mulVec P x) + dotProduct (star x) (mulVec Q y) +
      dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star y) (mulVec R y) =
    dotProduct (star x) (mulVec P x) - dotProduct (star u) (mulVec (Douglas.pinv R) u) := by
    rw [h_cross]; ring
  rw [h_sum] at h_block_quad
  have h_pinv_quad : dotProduct (star u) (mulVec (Douglas.pinv R) u) =
      dotProduct (star x) (mulVec (Q * (Douglas.pinv R) * (Qᴴ)) x) := by
    rw [hu]
    calc
      dotProduct (star (Qᴴ *ᵥ x)) (mulVec (Douglas.pinv R) (Qᴴ *ᵥ x)) =
          dotProduct (star x) (Q *ᵥ ((Douglas.pinv R) *ᵥ (Qᴴ *ᵥ x))) := by
        rw [← (star_dotProduct_mulVec Q x _).symm]; simp
      _ = dotProduct (star x) (mulVec (Q * (Douglas.pinv R) * (Qᴴ)) x) := by
        simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h_pinv_quad] at h_block_quad
  simpa [schurComplement, Matrix.sub_mulVec, dotProduct_sub] using h_block_quad

/-! ### Converse direction: Schur PSD + ker inclusion → block PSD -/

theorem block_psd_of_schur (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hker : ∀ y : Fin D₂ → ℂ, mulVec R y = 0 → mulVec Q y = 0)
    (hS : (schurComplement P Q R).PosSemidef) : (blockMatrix P Q R).PosSemidef := by
  have hpinv_herm : (Douglas.pinv R).IsHermitian := pinv_isHermitian R hR
  have hpinv_mp2 : (Douglas.pinv R) * R * (Douglas.pinv R) = Douglas.pinv R :=
    pinv_mul_R_mul_pinv_eq_pinv R hR
  have h_pinvR_supp : (Douglas.pinv R) * R = hR.supportProj := pinv_mul_R_eq_supportProj R hR
  have h_abs_Qh : R * (Douglas.pinv R) * (Qᴴ) = Qᴴ := by
    calc
      R * (Douglas.pinv R) * (Qᴴ) = (R * (Douglas.pinv R)) * (Qᴴ) := by simp [Matrix.mul_assoc]
      _ = hR.supportProj * (Qᴴ) := by rw [R_mul_pinv_eq_supportProj R hR]
      _ = Qᴴ := by
        simpa [Matrix.conjTranspose_mul, hR.supportProj_isHermitian.eq] using
          congrArg Matrix.conjTranspose
            (hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le (B := Q) hker)
  have h_herm : (blockMatrix P Q R).IsHermitian :=
    blockMatrix_isHermitian P Q R hP.isHermitian hR.isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm fun v => ?_
  let x := fun i : Fin D₁ => v (Sum.inl i)
  let y := fun i : Fin D₂ => v (Sum.inr i)
  have hv : v = Sum.elim x y := by
    ext i; cases i <;> rfl
  rw [hv, block_quadratic_form P Q R x y]
  set K := (Douglas.pinv R) * (Qᴴ) with hK
  set z := y + (K *ᵥ x) with hz
  have h_zRz_expand : dotProduct (star z) (mulVec R z) =
      dotProduct (star y) (mulVec R y) + dotProduct (star x) (mulVec Q y) +
      dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star x) (mulVec (Q * (Douglas.pinv R) * (Qᴴ)) x) := by
    rw [hz]
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, star_add,
      dotProduct_neg_right, dotProduct_neg_left]
    have h1 : dotProduct (star y) (mulVec R (K *ᵥ x)) = dotProduct (star y) (mulVec (Qᴴ) x) := by
      calc
        dotProduct (star y) (mulVec R (K *ᵥ x)) = dotProduct (star y) ((R * K) *ᵥ x) := by
          rw [← Matrix.mulVec_mulVec]
        _ = dotProduct (star y) ((Qᴴ) *ᵥ x) := by
          rw [hK, ← Matrix.mul_assoc, R_mul_pinv_eq_supportProj R hR, h_abs_Qh]
        _ = dotProduct (star y) (mulVec (Qᴴ) x) := rfl
    have h2 : dotProduct (star (K *ᵥ x)) (mulVec R y) = dotProduct (star x) (mulVec Q y) := by
      calc
        dotProduct (star (K *ᵥ x)) (mulVec R y) = dotProduct (star x) (mulVec (Kᴴ * R) y) := by
          rw [star_dotProduct_mulVec K x (mulVec R y), Matrix.mulVec_mulVec]
        _ = dotProduct (star x) (mulVec Q y) := by
          rw [hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpinv_herm.eq,
            Matrix.conjTranspose_conjTranspose]
          simp [Matrix.mul_assoc, h_pinvR_supp,
            hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le (B := Q) hker,
            Matrix.mulVec_mulVec]
    have h3 : dotProduct (star (K *ᵥ x)) (mulVec R (K *ᵥ x)) =
        dotProduct (star x) (mulVec (Q * (Douglas.pinv R) * (Qᴴ)) x) := by
      calc
        dotProduct (star (K *ᵥ x)) (mulVec R (K *ᵥ x)) =
            dotProduct (star x) (mulVec (Kᴴ * R * K) x) := by
          rw [star_dotProduct_mulVec (Kᴴ * R) x (K *ᵥ x)]
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = dotProduct (star x) (mulVec (Q * (Douglas.pinv R) * (Qᴴ)) x) := by
          rw [hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpinv_herm.eq,
            Matrix.conjTranspose_conjTranspose]
          calc
            (Q * (Douglas.pinv R)) * R * ((Douglas.pinv R) * (Qᴴ)) =
                Q * ((Douglas.pinv R) * R * (Douglas.pinv R)) * (Qᴴ) := by simp [Matrix.mul_assoc]
            _ = Q * (Douglas.pinv R) * (Qᴴ) := by rw [hpinv_mp2]
    rw [h1, h2, h3]
    ring
  have h_sum : dotProduct (star x) (mulVec P x) + dotProduct (star x) (mulVec Q y) +
      dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star y) (mulVec R y) =
    dotProduct (star x) (mulVec (schurComplement P Q R) x) + dotProduct (star z) (mulVec R z) := by
    rw [h_zRz_expand]
    dsimp [schurComplement]
    simp only [Matrix.sub_mulVec, dotProduct_sub]
    ring
  rw [h_sum]
  exact add_nonneg (hS.dotProduct_mulVec_nonneg x) (hR.dotProduct_mulVec_nonneg z)

end SchurComplement
