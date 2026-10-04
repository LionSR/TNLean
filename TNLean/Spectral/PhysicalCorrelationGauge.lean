/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.NormalGauge
import TNLean.MPS.SharedInfra.PhysicalObservableGauge
import TNLean.Spectral.PhysicalCorrelationDecay

/-!
# Decay of physical correlations in an arbitrary normal representation

A normal tensor has positive definite left and right transfer fixed matrices
whose trace pairing is one. These matrices define the connected physical
correlation by the left-right contraction. Passing to a trace-preserving bond
gauge preserves this contraction and supplies one geometric decay rate for
all finite supports, including adjacent observables.

Normality already includes spectral-radius-one normalization; the bond gauge
in this argument introduces no scalar rescaling.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441.

**Scope restriction (normal tensors):** The theorem assumes irreducibility
and the normalized peripheral spectral condition of normality. The source's
broader class, with a unique eigenvalue of largest modulus that is algebraically
simple but possibly singular fixed matrices, remains untreated; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.

**Local fix (Jordan blocks):** The source's pure-exponential expansion omits
polynomial Jordan factors. The geometric estimate uses a strictly larger rate
without assuming diagonalizability; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

open scoped Matrix BigOperators ComplexOrder NNReal ENNReal
namespace MPSTensor
variable {d D : ℕ}

private theorem gauge_left_posDef (U : GL (Fin D) ℂ) :
    ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (U : Matrix (Fin D) (Fin D) ℂ)).PosDef := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_one] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit U)).mpr
      (Matrix.PosDef.one : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef)

private theorem gauge_right_posDef (U : GL (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    ((↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * ρ * (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ).PosDef := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff (Units.isUnit U⁻¹)).mpr hρ

private theorem gauge_pair_trace (U : GL (Fin D) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (U : Matrix (Fin D) (Fin D) ℂ)) *
      ((↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * ρ *
        (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ)) = ρ.trace := by
  simp only [← Matrix.mul_assoc, Units.mul_inv_cancel_right]
  rw [Matrix.trace_mul_cycle, ← Matrix.conjTranspose_mul, Units.mul_inv,
    Matrix.conjTranspose_one, Matrix.one_mul]

private theorem gauge_right_fixedPoint {A B : MPSTensor d D} (U : GL (Fin D) ℂ)
    (hU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i * (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hFix : Kraus.transferMap B ρ = ρ) :
    Kraus.transferMap A
      ((↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * ρ * (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) =
      (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * ρ * (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have hB : B = fun i => (U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) := funext hU
  have h := Kraus.transferMap_gauge_conj A U ρ
  rw [← Matrix.GeneralLinearGroup.coe_inv, ← hB, hFix] at h
  have h' := congrArg (fun Z => (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * Z *
    (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) h
  simpa only [Matrix.mul_assoc, Units.inv_mul_cancel_left, ← Matrix.conjTranspose_mul,
    Units.inv_mul, Matrix.conjTranspose_one, Matrix.mul_one] using h'.symm

private theorem gauge_left_fixedPoint {A B : MPSTensor d D} (U : GL (Fin D) ℂ)
    (hU : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i * (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ))
    (hTP : ∑ i, (B i)ᴴ * B i = 1) :
    Kraus.transferMap (fun i => (A i)ᴴ)
      ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (U : Matrix (Fin D) (Fin D) ℂ)) =
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (U : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  have hUA (i : Fin d) : (U : Matrix (Fin D) (Fin D) ℂ) * A i =
      B i * (U : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hU i]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hUAh (i : Fin d) := congrArg Matrix.conjTranspose (hUA i)
  simp only [Matrix.conjTranspose_mul] at hUAh
  calc
    _ = ∑ i, ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (B i)ᴴ) *
        (B i * (U : Matrix (Fin D) (Fin D) ℂ)) := by
      simp only [Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
        ← Matrix.mul_assoc, hUAh]
      simp only [Matrix.mul_assoc, hUA]
    _ = (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (∑ i, (B i)ᴴ * B i) *
        (U : Matrix (Fin D) (Fin D) ℂ) := by
      simp only [Matrix.mul_assoc, Matrix.mul_sum, Matrix.sum_mul]
    _ = _ := by rw [hTP, Matrix.mul_one]

/-- A normal tensor admits positive left and right transfer fixed matrices with
trace pairing one, and one rate strictly below one controls every connected
physical correlation on independently chosen finite supports.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. Normality includes
the source's leading-eigenvalue normalization. No trace-preserving gauge is
assumed for the given tensor. -/
theorem IsNormalTensor.exists_physicalLeftRightCorrelation_decay
    {A : MPSTensor d D} (hNormal : IsNormalTensor A) :
    ∃ ℓ ρ : Matrix (Fin D) (Fin D) ℂ,
      ℓ.PosDef ∧ ρ.PosDef ∧ Kraus.transferMap (fun i => (A i)ᴴ) ℓ = ℓ ∧
      Kraus.transferMap A ρ = ρ ∧ Matrix.trace (ℓ * ρ) = 1 ∧
      ∃ rate : ℝ≥0, 0 < rate ∧ rate < 1 ∧
        ∀ (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
          (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ),
          ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
            ‖physicalLeftRightConnectedCorrelator A ℓ ρ L₁ L₂ X Y n‖ ≤
              C * (rate : ℝ) ^ n := by
  obtain ⟨B, L, ρB, hG, -, -, hTP, hρB, hFix, hTr⟩ := hNormal.exists_normalGauge
  have hNormalB := hNormal.of_gaugeEquiv hG.symm
  obtain ⟨U, hU⟩ := hG
  have hU' : ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using hU
  let ℓ := (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * (U : Matrix (Fin D) (Fin D) ℂ)
  let ρ := (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) * ρB *
    (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ
  refine ⟨ℓ, ρ, gauge_left_posDef U, gauge_right_posDef U ρB hρB,
    gauge_left_fixedPoint U hU' hTP, gauge_right_fixedPoint U hU' ρB hFix,
    (gauge_pair_trace U ρB).trans hTr, ?_⟩
  obtain ⟨rate, hRate, hRate1, hBound⟩ :=
    exists_rate_physicalConnectedCorrelator_le_geometric hNormalB hTP hρB.posSemidef hTr hFix
  have hRate0 : 0 < rate := by
    have h : (0 : ℝ≥0∞) < (rate : ℝ≥0∞) := lt_of_le_of_lt bot_le hRate
    exact_mod_cast h
  have hℓ : (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ * ℓ *
      (↑(U⁻¹) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simp only [ℓ, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      ← Matrix.conjTranspose_mul, Matrix.conjTranspose_one]
  have hρ : (U : Matrix (Fin D) (Fin D) ℂ) * ρ *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = ρB := by
    simp only [ρ, Matrix.mul_assoc, Units.mul_inv_cancel_left,
      ← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨rate, hRate0, hRate1, fun L₁ L₂ X Y => ?_⟩
  obtain ⟨C, hC, hCn⟩ := hBound L₁ L₂ X Y
  refine ⟨C, hC, fun n => ?_⟩
  rw [← physicalLeftRightConnectedCorrelator_eq_of_gauge U hU' ℓ ρ L₁ L₂ X Y n,
    hℓ, hρ, physicalLeftRightConnectedCorrelator_one B ρB hTr hTP hFix]
  exact hCn n
end MPSTensor
