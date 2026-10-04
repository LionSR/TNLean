/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DecayingCorrelations
import TNLean.MPS.Preparation.WindowCorrelator

/-!
# Physical correlations with left and right fixed matrices

Physical insertions transform by congruence under a pure invertible bond gauge.
Transforming the left matrix by inverse congruence and the right matrix by
congruence therefore preserves the connected contraction, at every separation.
For a normalized fixed pair this is the infinite-chain physical correlator of
arXiv:2011.12127, Section II.B.3, lines 433–441. The trace-preserving expression
is its specialization to the identity left matrix.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A pure invertible bond similarity transports every finite physical insertion by
congruence. This is the gauge covariance needed for arXiv:2011.12127,
Section II.B.3, lines 433–441. No unitarity or normalization is assumed. -/
theorem physicalObservableTransfer_congruence_of_gauge
    {A B : MPSTensor d D} (U : (Matrix (Fin D) (Fin D) ℂ)ˣ)
    (hU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ))
    (L : ℕ) (O : Matrix (Cfg d L) (Cfg d L) ℂ)
    (Z : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer B L O ((U : Matrix (Fin D) (Fin D) ℂ) * Z *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) =
      (U : Matrix (Fin D) (Fin D) ℂ) * physicalObservableTransfer A L O Z *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  simp only [physicalObservableTransfer_apply, evalWord_gauge U hU,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  simp only [Units.inv_mul_cancel_left, ← Matrix.conjTranspose_mul,
    Units.inv_mul_cancel_right]

private theorem trace_inverseCongruence_mul_congruence
    (U : (Matrix (Fin D) (Fin D) ℂ)ˣ)
    (ℓ Z : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (((↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * ℓ *
      (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ)) *
      ((U : Matrix (Fin D) (Fin D) ℂ) * Z * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)) =
      Matrix.trace (ℓ * Z) := by
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  simpa only [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Units.inv_mul,
    Matrix.conjTranspose_one, Matrix.mul_one] using
    Matrix.trace_mul_comm (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ
      (ℓ * (Z * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ))

private theorem transferMap_pow_congruence_of_gauge
    {A B : MPSTensor d D} (U : (Matrix (Fin D) (Fin D) ℂ)ˣ)
    (hU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ))
    (n : ℕ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    ((Kraus.transferMap B) ^ n) ((U : Matrix (Fin D) (Fin D) ℂ) * Z *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) =
      (U : Matrix (Fin D) (Fin D) ℂ) * ((Kraus.transferMap A) ^ n) Z *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  simpa only [physicalObservableTransfer_one] using
    physicalObservableTransfer_congruence_of_gauge U hU n
      (1 : Matrix (Cfg d n) (Cfg d n) ℂ) Z

/-- The connected contraction with left matrix `ℓ` and right matrix `ρ`, for physical
operators on independently chosen finite blocks and `n` unobserved intermediate sites.
When these matrices form a normalized positive fixed pair, this is the physical
connected correlator in arXiv:2011.12127, Section II.B.3, lines 433–441. -/
noncomputable def physicalLeftRightConnectedCorrelator (A : MPSTensor d D)
    (ℓ ρ : Matrix (Fin D) (Fin D) ℂ) (L₁ L₂ : ℕ)
    (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (n : ℕ) : ℂ :=
  Matrix.trace (ℓ * physicalObservableTransfer A L₁ X
    (((Kraus.transferMap A) ^ n) (physicalObservableTransfer A L₂ Y ρ))) -
    Matrix.trace (ℓ * physicalObservableTransfer A L₁ X ρ) *
      Matrix.trace (ℓ * physicalObservableTransfer A L₂ Y ρ)

/-- A pure invertible bond gauge preserves the physical connected contraction when
the left and right matrices are transported by inverse congruence and congruence.
This is the gauge independence of the left-right contraction in
arXiv:2011.12127, Section II.B.3, lines 433–441; the identity itself needs no
fixed-point, positivity, or normalization assumptions. -/
theorem physicalLeftRightConnectedCorrelator_eq_of_gauge
    {A B : MPSTensor d D} (U : (Matrix (Fin D) (Fin D) ℂ)ˣ)
    (hU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ))
    (ℓ ρ : Matrix (Fin D) (Fin D) ℂ) (L₁ L₂ : ℕ)
    (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (n : ℕ) :
    physicalLeftRightConnectedCorrelator B
      ((↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * ℓ *
        (↑U⁻¹ : Matrix (Fin D) (Fin D) ℂ))
      ((U : Matrix (Fin D) (Fin D) ℂ) * ρ * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)
      L₁ L₂ X Y n = physicalLeftRightConnectedCorrelator A ℓ ρ L₁ L₂ X Y n := by
  simp only [physicalLeftRightConnectedCorrelator,
    physicalObservableTransfer_congruence_of_gauge U hU,
    transferMap_pow_congruence_of_gauge U hU, trace_inverseCongruence_mul_congruence]

/-- With identity left matrix and a trace-one right fixed state, the left-right
contraction equals the centered trace-preserving expression at every separation.
This is the canonical-gauge form of arXiv:2011.12127, Section II.B.3, lines 433–441. -/
theorem physicalLeftRightConnectedCorrelator_one
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hTr : Matrix.trace ρ = 1) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hFix : Kraus.transferMap A ρ = ρ) (L₁ L₂ : ℕ)
    (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (n : ℕ) :
    physicalLeftRightConnectedCorrelator A 1 ρ L₁ L₂ X Y n =
      physicalConnectedCorrelator A ρ (by simp [hTr]) L₁ L₂ X Y n := by
  simpa only [physicalLeftRightConnectedCorrelator, Matrix.one_mul] using
    (physicalConnectedCorrelator_eq_twoPoint_sub A ρ (by simp [hTr]) hTr hTP hFix
      L₁ L₂ X Y n).symm

end MPSTensor
