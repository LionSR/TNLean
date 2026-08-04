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

## References

* [M. Wolf, *Quantum Channels & Operations*, Theorem 5.2][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace SchurComplement

variable {D₁ D₂ : ℕ}

/-- A 2×2 block matrix: [[P, Q], [Q†, R]]. -/
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

/-- Pseudoinverse Schur complement: `P − Q·R⁺·Q†`. -/
noncomputable def schurComplement (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin D₁) (Fin D₁) ℂ :=
  P - Q * (Douglas.pinv R) * (Qᴴ)

theorem block_quadratic_form (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (x : Fin D₁ → ℂ) (y : Fin D₂ → ℂ) :
    dotProduct (star (Sum.elim x y)) (mulVec (blockMatrix P Q R) (Sum.elim x y)) =
    dotProduct (star x) (mulVec P x) + dotProduct (star x) (mulVec Q y) +
    dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star y) (mulVec R y) := by
  rw [blockMatrix, Matrix.fromBlocks_mulVec P Q (Qᴴ) R (Sum.elim x y)]
  calc
    star (Sum.elim x y) ⬝ᵥ (Sum.elim (P *ᵥ x + Q *ᵥ y) (Qᴴ *ᵥ x + R *ᵥ y)) =
      star x ⬝ᵥ (P *ᵥ x + Q *ᵥ y) + star y ⬝ᵥ (Qᴴ *ᵥ x + R *ᵥ y) := by
      simp [dotProduct]
    _ = (star x ⬝ᵥ (P *ᵥ x) + star x ⬝ᵥ (Q *ᵥ y)) +
        (star y ⬝ᵥ (Qᴴ *ᵥ x) + star y ⬝ᵥ (R *ᵥ y)) := by simp [dotProduct_add]
    _ = star x ⬝ᵥ (P *ᵥ x) + star x ⬝ᵥ (Q *ᵥ y) +
        star y ⬝ᵥ (Qᴴ *ᵥ x) + star y ⬝ᵥ (R *ᵥ y) := by ring

theorem supportProj_sq_eq_supportProj (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef) :
    (posSemidef_self_mul_conjTranspose R).supportProj = hR.supportProj := by
  let hR2 : (R * R).PosSemidef := by
    have h_eq : R * R = R * Rᴴ := by rw [hR.isHermitian.eq]
    rw [h_eq]
    exact posSemidef_self_mul_conjTranspose R
  let hR2' : (R * Rᴴ).PosSemidef := posSemidef_self_mul_conjTranspose R
  have h_mat_eq : R * Rᴴ = R * R := by rw [hR.isHermitian.eq]
  have h_eq_instances : hR2'.supportProj = hR2.supportProj :=
    PosSemidef.supportProj_congr hR2' hR2 h_mat_eq
  have hkerR_R2 (v : Fin D₂ → ℂ) (hv : R *ᵥ v = 0) : (R * R) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hkerR2_R (v : Fin D₂ → ℂ) (hv : (R * R) *ᵥ v = 0) : R *ᵥ v = 0 := by
    have hdot : star (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = 0 := by
      calc
        star (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = star (Rᴴ *ᵥ v) ⬝ᵥ (R *ᵥ v) := by rw [hR.isHermitian.eq]
        _ = star v ⬝ᵥ (R *ᵥ (R *ᵥ v)) := by rw [← star_dotProduct_mulVec R v (R *ᵥ v)]
        _ = star v ⬝ᵥ ((R * R) *ᵥ v) := by rw [← Matrix.mulVec_mulVec]
        _ = star v ⬝ᵥ 0 := by rw [hv]
        _ = 0 := dotProduct_zero _
    exact dotProduct_star_self_eq_zero.mp hdot
  have hPR2_PR : hR2.supportProj * hR.supportProj = hR2.supportProj :=
    hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le fun v hv =>
      hR2.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v (hkerR_R2 v hv)
  have hPR_PR2 : hR.supportProj * hR2.supportProj = hR.supportProj :=
    hR2.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le (B := hR.supportProj) fun v hv =>
      hR.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v (hkerR2_R v hv)
  have hPR_PR2' : hR.supportProj * hR2.supportProj = hR2.supportProj := by
    simpa [Matrix.conjTranspose_mul, hR.supportProj_isHermitian.eq,
      hR2.supportProj_isHermitian.eq] using congrArg Matrix.conjTranspose hPR2_PR
  have h_eq_supp : hR2.supportProj = hR.supportProj := hPR_PR2'.symm.trans hPR_PR2
  simpa [hR2'] using h_eq_instances.trans h_eq_supp

/-! ### Forward: block PSD → ker inclusion -/


/-! ### Algebraic identities for `Douglas.pinv` on PSD `R` -/

theorem R_mul_pinv_eq_supportProj (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef) :
    R * (Douglas.pinv R) = hR.supportProj := by
  rw [Douglas.mul_pinv_eq_supportProj R]
  exact supportProj_sq_eq_supportProj R hR

/-- Support-projection absorption on the pseudoinverse of a PSD matrix:
`supportProj R * pinv R = pinv R`.

The proof avoids rewriting `Rᴴ = R` inside dependent positions (which breaks
the `rw` motive because `hR : R.PosSemidef` mentions `R`): all conversions are
done in term mode via `congrArg` transitivity chains, factoring `R` as
`√R * √R` and using the support absorption `supportProj R * √R = √R`. -/
theorem supportProj_mul_pinv_eq_pinv (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hR : R.PosSemidef) :
    hR.supportProj * Douglas.pinv R = Douglas.pinv R := by
  have hsqrt : hR.supportProj * hR.isHermitian.cfc Real.sqrt =
      hR.isHermitian.cfc Real.sqrt := hR.supportProj_mul_cfc_sqrt
  have hRR : hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt = R :=
    hR.cfc_sqrt_mul_self
  have e2 : hR.supportProj * (hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt) =
      hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt := by
    rw [← Matrix.mul_assoc, hsqrt]
  have e1 : hR.supportProj * R = R :=
    (congrArg (fun X => hR.supportProj * X) hRR).symm.trans (e2.trans hRR)
  have key : hR.supportProj * Rᴴ = Rᴴ :=
    (congrArg (HMul.hMul hR.supportProj) hR.isHermitian.eq).trans
      (e1.trans hR.isHermitian.eq.symm)
  calc hR.supportProj * Douglas.pinv R
      = (hR.supportProj * Rᴴ) * (Matrix.posSemidef_self_mul_conjTranspose R).supportInv := by
        rw [Douglas.pinv, Matrix.mul_assoc]
    _ = Rᴴ * (Matrix.posSemidef_self_mul_conjTranspose R).supportInv := by rw [key]
    _ = Douglas.pinv R := by rw [Douglas.pinv]

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
  ext i
  have := congrFun hMv_zero (Sum.inl i)
  simpa using this

end SchurComplement