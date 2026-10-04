/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PreparedPolarGappedPath
import TNLean.MPS.Symmetry.ProjectiveGaugeTransport

/-!
# Virtual cohomology along the symmetric polar deformation

The virtual unitary matrices obtained from an injective unital tensor can
be assembled into a projective representation. The same representation
implements the symmetry at every point of the polar path. Gauge independence
therefore identifies the classes of any virtual representations chosen at
its endpoints.

Source: arXiv:1010.3732, Sections II.C and II.F.2. The statements concern
exact symmetry of the periodic MPS vectors.

**Scope restriction (one-site injective tensors):** the polar path and its
gap are proved in the single-block, one-site injective case. The several-block
case is documented in `docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

/-- The symmetric polar path of an injective unital tensor has a single
unitary projective representation implementing its virtual covariance at
all parameters. Source: arXiv:1010.3732, Section II.C, “Isometric form and
symmetries”, and Section II.F.2, projective virtual symmetry. -/
theorem exists_unitary_virtualRep_polarDeformation
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ ω : ScalarCocycle G, ∃ ρ : ProjectiveRepresentation (D := D) ω,
      (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ) ∧
      ∀ (γ : ℝ) g i,
        twistedTensor (polarDeformation A γ)
          ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * polarDeformation A γ i *
          (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨X, hX⟩ := exists_unitary_virtual_covariance_of_isOnSiteSymmetric_unital
    A hA hNorm U hSym
  obtain ⟨ω, ρ, hρX, _⟩ := exists_projectiveRepresentation_of_virtual_covariance
    A hA ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)
    (fun g => Unitary.toUnits (X g)) (fun g i => congrFun (hX g) i)
  refine ⟨ω, ρ, ?_, ?_⟩
  · intro g
    rw [hρX]
    exact SetLike.coe_mem (X (g⁻¹))
  · intro γ g i
    rw [hρX, inv_inv]
    exact congrFun (rotatePhysical_polarDeformation_of_unitary_covariance hA
      (U g) (X g) (SetLike.coe_mem _) (SetLike.coe_mem _) (hX g) γ) i

/-- Any virtual representations chosen at the endpoints of the symmetric
polar path have cohomologous factor systems. Source: arXiv:1010.3732,
Sections II.C and II.F.2, preservation of the virtual class on passing to
isometric form. -/
theorem cohomologousTo_polarIsometricTensor_of_isInjective_unital
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U))
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (hρ₀ : ∀ g i, twistedTensor (polarIsometricTensor A)
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * polarIsometricTensor A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ω₁.CohomologousTo ω₀ := by
  obtain ⟨ω, ρ, _, hρ⟩ := exists_unitary_virtualRep_polarDeformation A hA hNorm U hSym
  have h₀ := cohomologousTo_of_isInjective (polarIsometricTensor A)
    (by simpa using isInjective_polarDeformation hA (γ := 0) (by simp))
    _ (NeZero.pos D) (ρ₁ := ρ) (ρ₂ := ρ₀)
    (by simpa using hρ 0) hρ₀
  have h₁ := cohomologousTo_of_isInjective A hA _ (NeZero.pos D)
    (ρ₁ := ρ) (ρ₂ := ρ₁) (by simpa using hρ 1) hρ₁
  exact h₁.trans h₀.symm

/-- Preparation and polar deformation join the original parent to an
isometric parent while retaining the original virtual cohomology class.
The virtual representation of the prepared tensor is unitary and implements
the entire polar path. Source: arXiv:1010.3732, Sections II.C and II.F.2. -/
theorem exists_prepared_polarGappedInteractionPath_with_virtual_class
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U))
    {ωA : ScalarCocycle G} (ρA : ProjectiveRepresentation (D := D) ωA)
    (hρA : ∀ g i, twistedTensor A
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρA.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρA.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ (B : MPSTensor d D) (c : ℂ) (ω : ScalarCocycle G)
      (ρ : ProjectiveRepresentation (D := D) ω),
      c ≠ 0 ∧ GaugeEquiv (c • A) B ∧ Kraus.IsInjective B ∧
      Kraus.transferMap B 1 = 1 ∧
      (∀ L, parentInteraction A L = parentInteraction B L) ∧
      ω.CohomologousTo ωA ∧
      (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ) ∧
      (∀ (γ : ℝ) g i, twistedTensor (polarDeformation B γ)
        ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * polarDeformation B γ i *
          (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ∧
      Nonempty (SymmetricGappedInteractionPath U
        (LinearMap.toMatrix' (parentInteraction (polarIsometricTensor B) 2))
        (LinearMap.toMatrix' (parentInteraction A 2))) := by
  obtain ⟨B, c, hc, hGauge, hB, hNorm, hParent, hPath⟩ :=
    exists_prepared_polarGappedInteractionPath_of_isOnSiteSymmetric A hA U hSym
  obtain ⟨ω, ρ, hUnitary, hρ⟩ := exists_unitary_virtualRep_polarDeformation
    B hB hNorm U ((hSym.smul c).of_gaugeEquiv hGauge)
  refine ⟨B, c, ω, ρ, hc, hGauge, hB, hNorm, hParent, ?_, hUnitary, hρ, hPath⟩
  exact cohomologousTo_of_smul_gaugeEquiv hB _ c hGauge ρA ρ hρA
    (by simpa using hρ 1)

end MPSTensor
