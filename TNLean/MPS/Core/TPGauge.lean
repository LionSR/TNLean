/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.MPS.Core.Transfer
import TNLean.Algebra.MatrixFunctionalCalculus

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# TP gauge from adjoint fixed points

This file constructs the standard trace-preserving gauge from a positive
definite fixed point of the adjoint transfer map. It defines `tpGauge` and
proves the TP normalization theorem
`tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint` together with the
resulting gauge and MPV invariance statements.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC

namespace MPSTensor

open Matrix Finset Complex

variable {d D : ℕ}

/-! ## Auxiliary lemmas about `CFC.sqrt` for positive definite matrices -/

/-- For a positive definite matrix `ρ`, the CFC square root satisfies `sqrt ρ * sqrt ρ = ρ`. -/
lemma cfc_sqrt_mul_self_of_posDef (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    CFC.sqrt ρ * CFC.sqrt ρ = ρ := by
  have hnonneg : (0 : Matrix (Fin D) (Fin D) ℂ) ≤ ρ := hρ.posSemidef.nonneg
  simpa using (CFC.sqrt_mul_sqrt_self ρ hnonneg)

/-- `CFC.sqrt ρ` is Hermitian (self-adjoint). -/
lemma conjTranspose_cfc_sqrt (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
  -- `CFC.sqrt ρ` is nonnegative, hence PSD, hence Hermitian.
  have hpsd : (CFC.sqrt ρ).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef).1 (CFC.sqrt_nonneg ρ)
  simpa using hpsd.isHermitian.eq

/-- If `ρ` is positive definite, then `det (CFC.sqrt ρ)` is a unit.

(We will use this to rewrite `S * S⁻¹ = 1` for `S := CFC.sqrt ρ`.) -/
lemma isUnit_det_cfc_sqrt_of_posDef (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    IsUnit (Matrix.det (CFC.sqrt ρ)) := by
  classical
  have hρ_unit : IsUnit ρ := Matrix.PosDef.isUnit hρ
  have hnonneg : (0 : Matrix (Fin D) (Fin D) ℂ) ≤ ρ := hρ.posSemidef.nonneg
  have hS_unit : IsUnit (CFC.sqrt ρ) := (CFC.isUnit_sqrt_iff ρ hnonneg).2 hρ_unit
  exact (Matrix.isUnit_iff_isUnit_det (CFC.sqrt ρ)).1 hS_unit

/-! ## TP gauge construction -/

/-- Gauge-transformed tensor `B i = ρ^{1/2} A i ρ^{-1/2}`.

We implement `ρ^{1/2}` as `CFC.sqrt ρ`.
(For `ρ` positive definite, this is invertible.) -/
noncomputable def tpGauge (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i => (CFC.sqrt ρ) * A i * (CFC.sqrt ρ)⁻¹

/-- **TP normalisation from an adjoint fixed point.**

Assume `ρ` is positive definite and fixed by the adjoint transfer map
`X ↦ ∑ i, (A i)ᴴ * X * A i` (equivalently `transferMap (fun i => (A i)ᴴ) ρ = ρ`).
Then the gauged tensor `tpGauge A ρ` satisfies the trace-preserving condition
`∑ i, (B i)ᴴ * (B i) = I`.

This is the standard “left-canonical” gauge construction for MPS. -/
theorem tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef)
    (hfix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ρ = ρ) :
    ∑ i : Fin d, (tpGauge (d := d) (D := D) A ρ i)ᴴ * tpGauge (d := d) (D := D) A ρ i = 1 := by
  classical
  -- Notation.
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt ρ
  have hS_mul : S * S = ρ := by
    simpa [S] using cfc_sqrt_mul_self_of_posDef (D := D) ρ hρ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) ρ
  have hStS : Sᴴ * S = ρ := by
    simpa [hS_herm] using hS_mul
  -- Invertibility facts (in the `Matrix` ring inverse sense).
  have hdet : IsUnit S.det := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ
  have hSmul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  have hdetT : IsUnit (Sᴴ.det) := by
    -- `det(Sᴴ) = star(det S)`.
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hdet)
  have hStinv_mul : (Sᴴ)⁻¹ * Sᴴ = 1 := Matrix.nonsing_inv_mul Sᴴ hdetT
  -- Rewrite each summand.
  have h_term : ∀ i : Fin d,
      (S * A i * S⁻¹)ᴴ * (S * A i * S⁻¹) = (Sᴴ)⁻¹ * ((A i)ᴴ * ρ * A i) * S⁻¹ := by
    intro i
    -- Expand the conjugate transpose and use `Sᴴ * S = ρ`.
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    -- Goal is now a reassociation; `simp` proves the required matrix identity.
    simp [Matrix.mul_assoc, ← hStS]
  -- Identify the adjoint fixed point equation as a sum.
  have h_sum_eq : ∑ i : Fin d, (A i)ᴴ * ρ * A i = ρ := by
    -- `transferMap (fun i => (A i)ᴴ) ρ = ∑ i, (A i)ᴴ * ρ * A i`.
    simpa [transferMap_apply, Matrix.mul_assoc] using hfix
  -- Compute the TP normalisation.
  change (∑ i : Fin d, (S * A i * S⁻¹)ᴴ * (S * A i * S⁻¹)) = 1
  simp_rw [h_term]
  -- Factor out `Sᴴ⁻¹` on the left and `S⁻¹` on the right.
  -- Then use the fixed point equation and cancel.
  rw [← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq, ← hStS]
  -- Now the goal is purely matrix algebra.
  -- (Sᴴ)⁻¹ * (Sᴴ * S) * S⁻¹ = ((Sᴴ)⁻¹ * Sᴴ) * (S * S⁻¹) = 1.
  simp [Matrix.mul_assoc, hStinv_mul, hSmul_inv]

/-- The gauge-transformed tensor `tpGauge A ρ` is gauge-equivalent to `A`
(hence has the same MPV). -/
theorem gaugeEquiv_tpGauge (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv (d := d) (D := D) A (tpGauge (d := d) (D := D) A ρ) := by
  classical
  -- `X := sqrt(ρ)` as an element of `GL`.
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ)
      (by
        -- `mk''` needs `IsUnit det`.
        simpa using isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ)
  refine ⟨X, ?_⟩
  intro i
  -- `X⁻¹` coerces to the (nonsingular) matrix inverse.
  simp [tpGauge, X]

/-- **MPV invariance** under the TP gauge transform `tpGauge`.

This follows from gauge equivalence. -/
theorem sameMPV_tpGauge (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SameMPV (d := d) (D := D) A (tpGauge (d := d) (D := D) A ρ) :=
  GaugeEquiv.sameMPV (gaugeEquiv_tpGauge (d := d) (D := D) A ρ hρ)

/-! ## Unital gauge from a transfer-map fixed point -/

/-- Gauge-transformed tensor `B i = ρ^{-1/2} A i ρ^{1/2}`.

This is the right-canonical, or unital, analogue of `tpGauge`. -/
noncomputable def unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i => (CFC.sqrt ρ)⁻¹ * A i * CFC.sqrt ρ

/-- **Unital normalisation from a transfer-map fixed point.**

Assume `ρ` is positive definite and fixed by the transfer map
`X ↦ ∑ i, A i * X * (A i)ᴴ`. Then the gauged tensor
`unitalGauge A ρ` satisfies
`∑ i, B i * (B i)ᴴ = I`.

This is the formal version of the full-rank fixed-point gauge in
Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`,
proof lines 767--769. -/
theorem unitalGauge_isUnital_of_transferMap_fixedPoint
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef)
    (hfix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∑ i : Fin d,
      unitalGauge (d := d) (D := D) A ρ i *
        (unitalGauge (d := d) (D := D) A ρ i)ᴴ = 1 := by
  classical
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt ρ
  have hS_mul : S * S = ρ := by
    simpa [S] using cfc_sqrt_mul_self_of_posDef (D := D) ρ hρ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) ρ
  have hSS : S * Sᴴ = ρ := by
    simpa [hS_herm] using hS_mul
  have hdet : IsUnit S.det := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ
  have hSinv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hdetT : IsUnit (Sᴴ.det) := by
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hdet)
  have hStmul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hdetT
  have h_term : ∀ i : Fin d,
      (S⁻¹ * A i * S) * (S⁻¹ * A i * S)ᴴ =
        S⁻¹ * (A i * ρ * (A i)ᴴ) * (Sᴴ)⁻¹ := by
    intro i
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv]
    simp [Matrix.mul_assoc, ← hSS]
  have h_sum_eq : ∑ i : Fin d, A i * ρ * (A i)ᴴ = ρ := by
    simpa [transferMap_apply, Matrix.mul_assoc] using hfix
  change
    (∑ i : Fin d, (S⁻¹ * A i * S) * (S⁻¹ * A i * S)ᴴ) = 1
  simp_rw [h_term]
  rw [← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq, ← hSS]
  simp [Matrix.mul_assoc, hSinv_mul, hStmul_inv]

/-- Rescaled right-canonical gauge
`B i = r^{-1/2} ρ^{-1/2} A i ρ^{1/2}`. -/
noncomputable def spectralUnitalGauge
    (A : MPSTensor d D) (r : ℝ) (ρ : Matrix (Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • unitalGauge (d := d) (D := D) A ρ i

/-- **Unital normalisation from a positive transfer-map eigenvector.**

Assume `ρ` is positive definite and
`E_A(ρ) = rρ` for a positive real number `r`. Then the rescaled right-canonical
gauge
`B i = r^{-1/2} ρ^{-1/2} A i ρ^{1/2}` satisfies
`∑ i, B i * (B i)ᴴ = I`.

This is the spectral-radius normalization step in Pérez-García, Verstraete,
Wolf, and Cirac, Theorem `Th:TIcanonical`, proof lines 765--769. -/
theorem spectralUnitalGauge_isUnital_of_transferMap_eigenvector
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hρ : ρ.PosDef)
    (hr : 0 < r)
    (hfix : transferMap (d := d) (D := D) A ρ = (r : ℂ) • ρ) :
    ∑ i : Fin d,
      spectralUnitalGauge (d := d) (D := D) A r ρ i *
        (spectralUnitalGauge (d := d) (D := D) A r ρ i)ᴴ = 1 := by
  classical
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt ρ
  let c : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ)
  have hc_star : star c = c := by
    rw [show c = (↑((Real.sqrt r)⁻¹) : ℂ) from rfl, RCLike.star_def,
      Complex.conj_ofReal]
  have hc_sq : c * c = (r : ℂ)⁻¹ := by
    have hcc : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
      rw [← sq, inv_pow, Real.sq_sqrt hr.le]
    rw [show c = (↑((Real.sqrt r)⁻¹) : ℂ) from rfl, ← Complex.ofReal_mul, hcc,
      Complex.ofReal_inv]
  have hS_mul : S * S = ρ := by
    simpa [S] using cfc_sqrt_mul_self_of_posDef (D := D) ρ hρ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) ρ
  have hSS : S * Sᴴ = ρ := by
    simpa [hS_herm] using hS_mul
  have hdet : IsUnit S.det := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ
  have hSinv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hdetT : IsUnit (Sᴴ.det) := by
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hdet)
  have hStmul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hdetT
  have h_term : ∀ i : Fin d,
      (c • (S⁻¹ * A i * S)) * (c • (S⁻¹ * A i * S))ᴴ =
        (r : ℂ)⁻¹ • (S⁻¹ * (A i * ρ * (A i)ᴴ) * (Sᴴ)⁻¹) := by
    intro i
    rw [Matrix.conjTranspose_smul, hc_star]
    calc
      (c • (S⁻¹ * A i * S)) * (c • (S⁻¹ * A i * S)ᴴ)
          = (c * c) • ((S⁻¹ * A i * S) * (S⁻¹ * A i * S)ᴴ) := by
              simp [smul_smul]
      _ = (r : ℂ)⁻¹ • ((S⁻¹ * A i * S) * (S⁻¹ * A i * S)ᴴ) := by
              rw [hc_sq]
      _ = (r : ℂ)⁻¹ • (S⁻¹ * (A i * ρ * (A i)ᴴ) * (Sᴴ)⁻¹) := by
              congr 1
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_nonsing_inv]
              simp [Matrix.mul_assoc, ← hSS]
  have h_sum_eq : ∑ i : Fin d, A i * ρ * (A i)ᴴ = (r : ℂ) • ρ := by
    simpa [transferMap_apply, Matrix.mul_assoc] using hfix
  change
    (∑ i : Fin d, (c • (S⁻¹ * A i * S)) * (c • (S⁻¹ * A i * S))ᴴ) = 1
  simp_rw [h_term]
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq]
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  change (r : ℂ)⁻¹ • (S⁻¹ * ((r : ℂ) • ρ) * (Sᴴ)⁻¹) = 1
  calc
    (r : ℂ)⁻¹ • (S⁻¹ * ((r : ℂ) • ρ) * (Sᴴ)⁻¹)
        = (r : ℂ)⁻¹ • ((r : ℂ) • (S⁻¹ * ρ * (Sᴴ)⁻¹)) := by
            simp [Matrix.mul_assoc]
    _ = ((r : ℂ)⁻¹ * (r : ℂ)) • (S⁻¹ * ρ * (Sᴴ)⁻¹) := by
            rw [smul_smul]
    _ = S⁻¹ * ρ * (Sᴴ)⁻¹ := by
            rw [inv_mul_cancel₀ hr_ne, one_smul]
    _ = 1 := by
            rw [← hSS]
            simp [Matrix.mul_assoc, hSinv_mul, hStmul_inv]

/-- The gauge-transformed tensor `unitalGauge A ρ` is gauge-equivalent to `A`
when `ρ` is positive definite. -/
theorem gaugeEquiv_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv (d := d) (D := D) A (unitalGauge (d := d) (D := D) A ρ) := by
  classical
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ)
      (by
        simpa using isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ)
  refine ⟨X⁻¹, ?_⟩
  intro i
  simp [unitalGauge, X]

/-- **MPV invariance** under the unital gauge transform `unitalGauge`. -/
theorem sameMPV_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SameMPV (d := d) (D := D) A (unitalGauge (d := d) (D := D) A ρ) :=
  GaugeEquiv.sameMPV (gaugeEquiv_unitalGauge (d := d) (D := D) A ρ hρ)

end MPSTensor
