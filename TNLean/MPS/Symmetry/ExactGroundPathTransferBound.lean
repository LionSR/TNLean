/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathWindowClustering
import TNLean.MPS.Preparation.FiniteRingCorrelationLimit
import TNLean.MPS.Symmetry.InjectiveTracePreservingGauge

/-!
# A common transfer spectral bound from the actual physical gap

The physical path supplies a common finite-ring correlation rate. Actual
window geometry and equality of the periodic rays transfer it to each
trace-preserving representative. Pointwise primitivity proves the
finite-to-limiting correlation passage, so no common transfer gap or
limiting-correlation bound is assumed. The actual eigenvalue observers
then force the same bound below one on the nonunit transfer spectrum.

The faithful-fixed-point data and trace-preserving gauge are then derived
for every unital injective representative. Gauge invariance of the actual
periodic rays and transfer spectrum removes these auxiliary choices from
the common unital transfer bound.

Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953, and
Hastings–Koma, arXiv:math-ph/0507008, Section 3.
-/

noncomputable section

open Filter
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The actual physical gap gives a common bound below one on the
nonunit transfer spectrum of every trace-preserving block-injective
representative of the periodic rays with a faithful trace-one fixed
density. Its finite-ring convergence is derived pointwise; no uniform
transfer-gap or correlation conclusion is an extra premise.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_tracePreserving_transfer_bound
    (Q : ExactMPSGroundPath P) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ D : ℕ, ∀ _ : NeZero D,
      ∀ A : MPSTensor d D, SamePositiveMpvRay (Q.tensor γ) A →
      ∀ L : ℕ, 0 < L → Kraus.IsNBlkInjective A L →
      (∑ i, (A i)ᴴ * A i = 1) →
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef →
      Kraus.transferMap A ρ = ρ → Matrix.trace ρ = 1 →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ r := by
  obtain ⟨K, κ, hK, hκ, hEst⟩ := Q.exists_uniform_ray_window_correlation_bound
  refine ⟨Real.exp (-κ), Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hκ)
  intro γ hγ D hD A hRay L hL hInj hTP ρ hρ hfix htr z hz hzne
  let : NeZero D := hD
  apply norm_transfer_spectrum_le_of_finite_mpvConnectedCorrelator_bound
    hL hInj hTP hρ hfix htr (Real.exp_pos _) ?_ hz hzne
  intro X Y
  refine ⟨K * ((L : ℝ) + 1) * ‖X‖ * ‖Y‖, 1, fun t ht ↦ ?_⟩
  filter_upwards [eventually_ge_atTop t] with n hn
  have h := hEst γ hγ D A hRay L hL X Y t ht n hn
  simpa only [← Real.exp_nat_mul, mul_comm (t : ℝ) (-κ)] using h

/-- The actual physical gap gives one common bound below one for all
unital injective representatives of its periodic rays. Trace-preserving
normalization, the faithful stationary density, finite-ring convergence
and the spectral comparison are all derived. No transfer-bound or
continuous minimal-gauge choice is assumed.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_unital_transfer_bound
    (Q : ExactMPSGroundPath P) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ D : ℕ, 0 < D →
      ∀ A : MPSTensor d D, Kraus.IsInjective A → Kraus.IsUnital A →
      SamePositiveMpvRay (Q.tensor γ) A →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ r := by
  obtain ⟨r, hr, hrOne, hEst⟩ := Q.exists_uniform_tracePreserving_transfer_bound
  refine ⟨r, hr, hrOne, ?_⟩
  intro γ hγ D hD A hA hUnital hRay z hz hzne
  let : NeZero D := ⟨hD.ne'⟩
  obtain ⟨B, ρ, _, hB, hTP, hρ, hfix, htr, hAB, hSpec⟩ :=
    exists_tpGauge_of_isInjective_unital hA hUnital
  rw [hSpec] at hz
  exact hEst γ hγ D inferInstance B (hRay.trans hAB) 1 zero_lt_one
    (Kraus.isNBlkInjective_one_of_isInjective hB) hTP ρ hρ hfix htr z hz hzne

end MPSTensor
