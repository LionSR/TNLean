/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PositiveRayFiniteTraceData
import TNLean.MPS.Symmetry.FiniteRingReconstruction
import TNLean.MPS.Symmetry.ProjectiveGaugeTransport
import TNLean.MPS.Symmetry.PhysicalCharacterTwist

/-!
# Virtual cohomology of a periodic state ray

Injective tensors representing the same positive-length periodic rays have
identical minimal bond dimensions. The two- and three-site trace data recover
a scalar bond gauge, which transports the virtual action without changing its
factor system. Physical character changes are also determined by that ray:
injective gauge-phase uniqueness removes their apparent ambiguity.

Source: arXiv:1010.3732, Sections II.C.2 and II.F.2, and Appendix C.
-/

open scoped Matrix TNLean.Algebra.ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

/-- The periodic ray determines the injective bond dimension. Source:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem bondDimension_eq_of_samePositiveMpvRay
    {d D E : ℕ} [NeZero D] {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (hRay : SamePositiveMpvRay A B) : D = E := by
  obtain ⟨c₂, -, hc₂, -, hpair, -⟩ :=
    exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay hA hRay.symm
  exact bondDimension_eq_of_twoSite_trace_eq hA hB c₂ hc₂ hpair

/-- Injective representatives of the same periodic ray have the same virtual
class, even if their bond dimensions were initially different. Source:
arXiv:1010.3732, Section II.F.2 and Appendix C. -/
theorem cohomologousTo_of_samePositiveMpvRay
    {G : Type} [Group G] {d D E : ℕ} [NeZero D] [NeZero E]
    {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (hRay : SamePositiveMpvRay A B) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := E) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A U g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₁ : ∀ g i, twistedTensor B U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ) * B i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin E) ℂ) : Matrix (Fin E) (Fin E) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos E))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D))) := by
  obtain ⟨c₂, c₃, hc₂, hc₃, hpair, htriple⟩ :=
    exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay hA hRay.symm
  have hDE := bondDimension_eq_of_samePositiveMpvRay hA hB hRay
  subst E
  exact cohomologousTo_of_smul_gaugeEquiv hB U (c₃ / c₂)
    (gaugeEquiv_smul_of_two_three_trace_eq hA hB c₂ c₃ hc₂ hc₃ hpair htriple)
    ρ₀ ρ₁ hρ₀ hρ₁

private theorem cohomologousTo_of_character_covariance
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (χ₀ χ₁ : G →* ℂ) (hχ₀ : ∀ g, ‖χ₀ g‖ = 1) (hχ₁ : ∀ g, ‖χ₁ g‖ = 1)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (h₀ : ∀ g i, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₀ hχ₀ U)) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (h₁ : ∀ g i, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₁ hχ₁ U)) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D))) := by
  apply cohomologousTo_of_isInjective A hA _ (NeZero.pos D) h₀
  intro g i
  have hχne : χ₁ g ≠ 0 := norm_ne_zero_iff.mp (by rw [hχ₁]; exact one_ne_zero)
  have hTw : ∀ j, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₀ hχ₀ U)) g j =
      ((χ₀ g)⁻¹ * χ₁ g) •
        twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
          (physicalCharacterUntwist χ₁ hχ₁ U)) g j := by
    intro j
    simp only [twistedTensor_physicalCharacterUntwist, Pi.smul_apply, smul_smul,
      mul_assoc, mul_inv_cancel₀ hχne, mul_one]
  have hRel : ∀ j,
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A j *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      ((χ₀ g)⁻¹ * χ₁ g) •
        ((ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A j *
          (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro j
    rw [← h₀ g j, hTw j, h₁ g j]
  have hc := (gauge_phase_unique hA
    (X := (ρ₀.X (g⁻¹))⁻¹) (Y := (ρ₁.X (g⁻¹))⁻¹)
    (by simpa only [inv_inv] using hRel)).1
  exact (h₀ g i).trans (by simpa only [hc, one_smul] using hRel i)

/-- Physical character changes and a choice of injective representative do
not change the virtual class of a positive-length periodic ray. Character
compatibility follows from injectivity, rather than being assumed. Source:
arXiv:1010.3732, Sections II.C.2 and II.F.2 and Appendix C. -/
theorem cohomologousTo_of_samePositiveMpvRay_character_covariance
    {G : Type} [Group G] {d D E : ℕ} [NeZero D] [NeZero E]
    {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (hRay : SamePositiveMpvRay A B) (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (χ₀ χ₁ : G →* ℂ) (hχ₀ : ∀ g, ‖χ₀ g‖ = 1) (hχ₁ : ∀ g, ‖χ₁ g‖ = 1)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := E) ω₁)
    (h₀ : ∀ g i, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₀ hχ₀ U)) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (h₁ : ∀ g i, twistedTensor B ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₁ hχ₁ U)) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ) * B i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin E) ℂ) : Matrix (Fin E) (Fin E) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos E))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D))) := by
  obtain ⟨c₂, c₃, hc₂, hc₃, hpair, htriple⟩ :=
    exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay hA hRay.symm
  have hDE := bondDimension_eq_of_samePositiveMpvRay hA hB hRay
  subst E
  obtain ⟨Y, hY⟩ :=
    gaugeEquiv_smul_of_two_three_trace_eq hA hB c₂ c₃ hc₂ hc₃ hpair htriple
  exact cohomologousTo_of_character_covariance hB U χ₀ χ₁ hχ₀ hχ₁
    (ρ₀.conjugate Y) ρ₁
    (twistedTensor_covariance_of_smul_gauge _ ρ₀ h₀ (c₃ / c₂) Y hY) h₁

end MPSTensor
