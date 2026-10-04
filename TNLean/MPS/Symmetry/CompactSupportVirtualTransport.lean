/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ProjectiveGaugeTransport
import TNLean.MPS.CanonicalForm.TranslationInvariantUniqueness
import TNLean.Algebra.UnitaryGeneralLinearInverse

/-!
# Virtual symmetry transport at a compact stationary-support limit

Gauge equivalence up to a nonzero scalar preserves injectivity and the
virtual cohomology class. For two unital tensors, the bond gauge may be
chosen unitary. Transport along this unitary supplies a unitary virtual
representation on the limiting support with exactly the original factor.
No convergence of virtual representatives is required.

These are finite-dimensional auxiliary statements for arXiv:1010.3732,
Appendix C, lines 2653–2717. No physical-gap implication is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

private theorem exists_smul_gauge_of_gaugePhaseEquiv
    {d D : ℕ} {A B : MPSTensor d D} (h : GaugePhaseEquiv A B) :
    ∃ c : ℂ, c ≠ 0 ∧ GaugeEquiv (c • A) B := by
  obtain ⟨X, c, hc, hX⟩ := h
  refine ⟨c, hc, X, fun i => ?_⟩
  simpa only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul] using hX i

/-- Gauge equivalence up to a scalar preserves the virtual cohomology class
of an injective tensor. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717, and Section II.F.2, gauge independence of the class. -/
theorem cohomologousTo_of_injective_gaugePhaseEquiv
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    {A B : MPSTensor d D} (hA : Kraus.IsInjective A) (hGauge : GaugePhaseEquiv A B)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (h₀ : ∀ g i, twistedTensor A U g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (h₁ : ∀ g i, twistedTensor B U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ω₁.CohomologousTo ω₀ := by
  obtain ⟨c, hc, hG⟩ := exists_smul_gauge_of_gaugePhaseEquiv hGauge
  exact cohomologousTo_of_smul_gaugeEquiv
    (isInjective_of_gaugeEquiv (hA.smul hc) hG) U c hG ρ₀ ρ₁ h₀ h₁

/-- Unital gauge-phase equivalent tensors admit unitary virtual actions with
exactly the same projective factor. A unitary bond gauge transports the action;
no limit of supplied virtual matrices is needed. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717, using the unital gauge
uniqueness argument of arXiv:quant-ph/0608197, lines 1097–1108. -/
theorem exists_unitary_virtualRep_of_unital_gaugePhaseEquiv
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    {A B : MPSTensor d D} (hA : Kraus.IsInjective A)
    (hAU : Kraus.IsUnital A) (hBU : Kraus.IsUnital B)
    (hGauge : GaugePhaseEquiv A B)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∃ σ : ProjectiveRepresentation (D := D) ω,
      (∀ g, (σ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      ∀ g, rotatePhysical (U g) B = fun i =>
        (σ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * B i *
          (σ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨c, hc, hG⟩ := exists_smul_gauge_of_gaugePhaseEquiv hGauge
  have hBInj := isInjective_of_gaugeEquiv (hA.smul hc) hG
  obtain ⟨X, hX⟩ := hG
  have hRel : ∀ i, (X : Matrix (Fin D) (Fin D) ℂ) * A i =
      c⁻¹ • (B i * (X : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    rw [hX i]
    simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      show (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) * X = 1 by simp,
      Matrix.mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨W, _, hW⟩ := exists_unitaryConj_of_intertwines_of_isNBlkInjective
    hBU hAU (Kraus.isNBlkInjective_one_of_isInjective hBInj) (Units.ne_zero X) hc hRel
  let Y : GL (Fin D) ℂ := Unitary.toUnits W
  have hY : ∀ i, B i = (Y : Matrix (Fin D) (Fin D) ℂ) * (c • A i) *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro i
    change B i = (W : Matrix (Fin D) (Fin D) ℂ) * (c • A i) *
      (W : Matrix (Fin D) (Fin D) ℂ)ᴴ
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hW i
  have hUnitary : ∀ g, ((ρ.conjugate Y).X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup _ ℂ := by
    intro g
    change (W : Matrix (Fin D) (Fin D) ℂ) * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
      (star W : Matrix.unitaryGroup (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ
    exact (Matrix.unitaryGroup _ ℂ).mul_mem
      ((Matrix.unitaryGroup _ ℂ).mul_mem W.property (hρ g)) (star W).property
  refine ⟨ρ.conjugate Y, hUnitary, ?_⟩
  intro g
  funext i
  have h₀ : ∀ g i, twistedTensor A
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro g i
    rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hρ g⁻¹)]
    exact congrFun (hCov g) i
  have h := twistedTensor_covariance_of_smul_gauge
    ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) ρ h₀ c Y hY g i
  rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hUnitary g⁻¹)] at h
  exact h

end MPSTensor
