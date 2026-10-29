/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathTransferBound
import TNLean.MPS.Symmetry.ExactGroundPathTransferClass

/-!
# Virtual class invariance from the actual physical ground-state gap

The physical gap gives ordinary connected clustering, then a common
transfer spectral bound for every unital injective representative of the
periodic rays. The existing compact-limit argument now applies without
its auxiliary transfer-bound premise. The minimal bond dimension may
change along the path; no continuous minimal gauge or virtual action is
chosen. This is the converse obstruction for the exact MPS path domain.

Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953,
Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717.
-/

noncomputable section

open scoped Matrix TNLean.Algebra.ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

/-- An exact physical gapped MPS path has a common virtual cohomology
class, including when its minimal injective bond dimension changes.
The common physical character, injective unital representatives and
unitary virtual actions are derived. There is no transfer-bound,
clustering, limiting-correlation or continuous minimal-gauge premise.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953,
Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717. -/
theorem ExactMPSGroundPath.exists_constant_virtual_class
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
    ∃ D : unitInterval → ℕ, ∃ A : ∀ t, MPSTensor d (D t),
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t),
    ∃ hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t),
      (∀ t, 0 < D t ∧ D t ≤ Q.bondDimension) ∧
      (∀ t, Kraus.IsInjective (A t) ∧ Kraus.IsUnital (A t)) ∧
      (∀ t : unitInterval, SamePositiveMpvRay (Q.tensor t) (A t)) ∧
      (∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
        Matrix.unitaryGroup _ ℂ) ∧
      (∀ t g, rotatePhysical (physicalCharacterUntwist χ hχ U g) (A t) = fun i ↦
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
          ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) ∧
      ∀ s t, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω t)) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω s)) := by
  obtain ⟨r, hr, hrOne, hTransfer⟩ := Q.exists_uniform_unital_transfer_bound
  apply Q.exists_constant_virtual_class_of_uniform_transfer_bound r hr.le hrOne
  intro t D hD A hA hUnital hRay z hz hzne
  exact hTransfer t t.property D hD A hA hUnital hRay z hz hzne

end MPSTensor
