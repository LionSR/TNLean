/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathPhysicalClass
import TNLean.MPS.Symmetry.PositiveRayVirtualCohomology

/-!
# Prescribed endpoint classes of an exact physical gapped MPS path

The constant virtual class derived from the physical Hamiltonian gap agrees
with every prescribed virtual action of either endpoint ray. Minimal bond
dimensions, tensor normalizations, bond gauges, and the physical characters
at the two endpoints need not be identified in advance.

Source: arXiv:1010.3732, Section II.F.2, lines 929–993, and Appendix C.
-/

open scoped Matrix TNLean.Algebra.ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

/-- A physical gapped path in the exact MPS regime identifies the classes
of prescribed injective endpoint representations. Both endpoint character
changes are permitted independently. Their compatibility with the path is
derived from periodic ray equality. Source: arXiv:1010.3732, Section II.F.2
and Appendix C; physical character changes are allowed in Section II.C.2. -/
theorem ExactMPSGroundPath.cohomologousTo_endpoints
    {G : Type} [Group G] {d D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    {A₀ : MPSTensor d D₀} {A₁ : MPSTensor d D₁}
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁)
    (hRay₀ : SamePositiveMpvRay (Q.tensor 0) A₀)
    (hRay₁ : SamePositiveMpvRay (Q.tensor 1) A₁)
    (χ₀ χ₁ : G →* ℂ) (hχ₀ : ∀ g, ‖χ₀ g‖ = 1) (hχ₁ : ∀ g, ‖χ₁ g‖ = 1)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A₀ ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₀ hχ₀ U)) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A₁ ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₁ hχ₁ U)) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀))) := by
  obtain ⟨χ, hχ, D, A, ω, ρ, hω, hD, hA, hRay, hUnitary, hCov, hClass⟩ :=
    Q.exists_constant_virtual_class
  have : NeZero (D 0) := ⟨(hD 0).1.ne'⟩
  have : NeZero (D 1) := ⟨(hD 1).1.ne'⟩
  have hInvCov : ∀ (t : unitInterval) g i,
      twistedTensor (A t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
        (physicalCharacterUntwist χ hχ U)) g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((((ρ t).X (g⁻¹))⁻¹ : GL (Fin (D t)) ℂ) :
          Matrix (Fin (D t)) (Fin (D t)) ℂ) := by
    intro t g i
    rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hUnitary t g⁻¹)]
    exact congrFun (hCov t g) i
  have hEnd₀ := cohomologousTo_of_samePositiveMpvRay_character_covariance
    hA₀ (hA 0).1 (hRay₀.symm.trans (hRay 0)) U χ₀ χ hχ₀ hχ
    ρ₀ (ρ 0) hρ₀ (hInvCov 0)
  have hEnd₁ := cohomologousTo_of_samePositiveMpvRay_character_covariance
    hA₁ (hA 1).1 (hRay₁.symm.trans (hRay 1)) U χ₁ χ hχ₁ hχ
    ρ₁ (ρ 1) hρ₁ (hInvCov 1)
  exact hEnd₁.symm.trans ((hClass 0 1).trans hEnd₀)

end MPSTensor
