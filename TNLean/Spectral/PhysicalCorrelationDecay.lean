/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Analysis.SpectralRadiusPowerDecay
import TNLean.MPS.Preparation.DecayingCorrelations

/-!
# Exponential decay of physical connected correlations

For a normal tensor in trace-preserving gauge, the transfer map minus its
fixed-state projection has spectral radius strictly below one. Physical
observables on arbitrary finite blocks therefore have a connected correlator
bounded at every prescribed rate strictly above that spectral radius. The
bound holds also for adjacent blocks, because the inner insertion is centered.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441.

**Scope restriction (trace-preserving gauge):** The normality-based gap and
rate-existence theorems assume the trace-preserving gauge and a normalized
positive fixed state. Transporting physical connected correlations from an
arbitrary normal representation still requires covariance of the physical
insertions under the gauge transformation. The existing normal-gauge
existence results do not supply that identity; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.

**Local fix (Jordan blocks):** The source's unqualified pure-exponential
expansion omits polynomial factors at defective eigenvalues. The decay theorem
uses any strictly larger rate, with no diagonalizability hypothesis; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

open scoped Matrix BigOperators NNReal ENNReal ComplexOrder Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-- Normality, trace preservation, and a normalized positive fixed state imply
that the complementary transfer map has spectral radius less than one.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. Irreducibility and
absence of nontrivial peripheral eigenvalues are supplied by normality. -/
theorem normalTensor_complement_spectralRadius_lt_one
    {A : MPSTensor d D} (hNormal : IsNormalTensor A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hTr : Matrix.trace ρ = 1) (hFix : Kraus.transferMap A ρ = ρ) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      (Kraus.transferMap A - fixedPointProj ρ (by simp [hTr]))) < 1 := by
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  obtain ⟨htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap A) (Kraus.isChannel_mapLM A hTP)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hNormal.no_invariant_proj)
      hNormal.primitive_transfer ρ hρ (by intro h; simp [h] at hTr) hFix
  exact hgap

/-- Physical connected correlations on independently chosen finite supports
are bounded by a geometric sequence at every rate strictly above the actual
complementary spectral radius, including zero unobserved intermediate sites.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. The rate may lie
below one whenever the tensor is normal in trace-preserving gauge. -/
theorem exists_physicalConnectedCorrelator_le_geometric
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (L₁ L₂ : ℕ)
    (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) (rate : ℝ≥0)
    (hRate : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - fixedPointProj ρ htr)) < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖physicalConnectedCorrelator A ρ htr L₁ L₂ X Y n‖ ≤ C * (rate : ℝ) ^ n := by
  obtain ⟨C, hC, hpow⟩ := geometric_apply_bound_of_spectralRadius_lt
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      (Kraus.transferMap A - fixedPointProj ρ htr)) rate hRate
  let ℓ : Matrix (Fin D) (Fin D) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (physicalObservableTransfer A L₁ X)).toContinuousLinearMap
  let Z := physicalObservableTransfer A L₂ Y ρ -
    fixedPointProj ρ htr (physicalObservableTransfer A L₂ Y ρ)
  obtain ⟨M, hM, hℓ⟩ := ℓ.bound
  refine ⟨M * C * ‖Z‖ + 1, by positivity, fun n => ?_⟩
  refine (hℓ (((Kraus.transferMap A - fixedPointProj ρ htr) ^ n) Z)).trans ?_
  have hpowZ : ‖((Kraus.transferMap A - fixedPointProj ρ htr) ^ n) Z‖ ≤
      C * (rate : ℝ) ^ n * ‖Z‖ := by
    have hp := hpow n Z
    rw [← map_pow] at hp
    exact hp
  refine (mul_le_mul_of_nonneg_left hpowZ hM.le).trans ?_
  nlinarith [pow_nonneg rate.coe_nonneg n]

/-- A normal tensor in trace-preserving gauge has one rate strictly between the
actual complementary spectral radius and one which bounds the connected
correlations of every pair of independently supported physical observables.

Reference: arXiv:2011.12127, Section II.B.3, lines 433–441. The rate depends only
on the tensor and fixed state; the constant may depend on the observables. -/
theorem exists_rate_physicalConnectedCorrelator_le_geometric
    {A : MPSTensor d D} (hNormal : IsNormalTensor A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hTr : Matrix.trace ρ = 1) (hFix : Kraus.transferMap A ρ = ρ) :
    ∃ rate : ℝ≥0, spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap A - fixedPointProj ρ (by simp [hTr]))) < (rate : ℝ≥0∞) ∧
      rate < 1 ∧ ∀ (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
        (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ),
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          ‖physicalConnectedCorrelator A ρ (by simp [hTr]) L₁ L₂ X Y n‖ ≤ C * (rate : ℝ) ^ n := by
  obtain ⟨rate, hRate, hRate1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (normalTensor_complement_spectralRadius_lt_one hNormal hTP hρ hTr hFix)
  refine ⟨rate, hRate, by exact_mod_cast hRate1, ?_⟩
  exact fun L₁ L₂ X Y =>
    exists_physicalConnectedCorrelator_le_geometric A ρ (by simp [hTr]) L₁ L₂ X Y rate hRate

end MPSTensor
