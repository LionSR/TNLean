/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedWeakHopfAverage
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedParentCommutation

/-!
# The completed weak-Hopf parent on the enlarged mixed physical space

Average on the active square alphabet, add the represented-unit complement,
then include the result in the enlarged physical space with the usual unused
space penalty. The result is exactly the continuous arbitrary-alphabet mixed
interaction on the closed interval. It commutes with the periodic common MPO
on every ring of length at least two, with no separate adjoint-closure premise.

**Scope restriction (supplied active realization):** the compressed common MPO's
weak-Hopf realization remains an explicit
hypothesis. This does not construct it from fusion tensors and F-symbols.
The literal enlarged realization is obstructed by its zero physical summands;
see `MixedWeakHopfRealizationObstruction` and
`docs/paper-gaps/glm23_mixed_weak_hopf_realization.tex`.
Source: arXiv:2203.12563v3, Section 5 and Appendix B.
-/

open scoped Matrix ComplexOrder

open ManyBody
open MPOTensor.PhysicalSectorFactorization

noncomputable section

namespace MPOTensor.WeakHopfRepresentation

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
  [StarRing H] [StarModule ℂ H] {d e D : ℕ}

/-- Physical inclusion preserves the adjoint boundary supplied by a
weak-Hopf realization, even when the inclusion is rectangular. -/
theorem exists_adjointBoundary_changePhysicalBasis
    (W : WeakHopfRepresentation H d D) (J : Matrix (Fin e) (Fin d) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, ∀ n,
      (mpoWithBoundary (changePhysicalBasis J W.tensor) X n)ᴴ =
        mpoWithBoundary (changePhysicalBasis J W.tensor) Y n := by
  obtain ⟨Y, hY⟩ := W.exists_conjTranspose_mpoWithBoundary_eq X
  refine ⟨Y, fun n => ?_⟩
  have htransport (Z : Matrix (Fin D) (Fin D) ℂ) :
      mpoWithBoundary (changePhysicalBasis J W.tensor) Z n =
        singleKrausMap (Matrix.tensorPower n J) (mpoWithBoundary W.tensor Z n) := by
    simp only [mpoWithBoundary_eq_physCloseN,
      singleKrausMap_tensorPower_physCloseN]
  rw [htransport, htransport]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hY n, Matrix.mul_assoc]

end MPOTensor.WeakHopfRepresentation

namespace MPSTensor.MPOSymmetry

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
  [StarRing H] [StarModule ℂ H] {d₀ d₁ D₀ D₁ χ₀ χ₁ m N : ℕ}

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (W : MPOTensor.WeakHopfRepresentation H ((D₀ + D₁) * (D₀ + D₁)) (χ₀ + χ₁))

/-- Average and complete in support coordinates before extending to the
common physical space. This includes both complement penalties. -/
def arbitraryPhysicalMixedWeakHopfParent (γ : ℝ) :=
  isometricInteractionExtension
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (mixedWeakHopfCompletedInteraction (polarPosTensor A₀) (polarPosTensor A₁) W γ)

variable [NeZero D₀] [NeZero D₁]
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
    (fun _ : Fin m => A₀) V₀ W₀)
  (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
    (fun _ : Fin m => A₁) V₁ W₁)
  (hW : W.tensor = mixedEndpointMPO (polarSupportMPO A₀ T₀) (polarSupportMPO A₁ T₁)
    V₀ V₁ W₀ W₁)

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed integral construction equals the existing enlarged mixed
interaction throughout the closed parameter interval. -/
theorem arbitraryPhysicalMixedWeakHopfParent_eq
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    arbitraryPhysicalMixedWeakHopfParent A₀ A₁ W γ =
      arbitraryPhysicalMixedInteraction A₀ A₁ γ := by
  unfold arbitraryPhysicalMixedWeakHopfParent arbitraryPhysicalMixedInteraction
  rw [mixedWeakHopfCompletedInteraction_eq
    (polarPosTensor A₀) (polarPosTensor A₁) (polarSupportMPO A₀ T₀) (polarSupportMPO A₁ T₁)
    V₀ V₁ W₀ W₁ W (isBiorthogonalDecomposition_polarSupportMPO h₀)
    (isBiorthogonalDecomposition_polarSupportMPO h₁) hW
    (isInjective_polarPosTensor hInj₀) (isInjective_polarPosTensor hInj₁) hγ]

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed enlarged path is continuous on the closed interval. -/
theorem continuousOn_arbitraryPhysicalMixedWeakHopfParent :
    ContinuousOn (arbitraryPhysicalMixedWeakHopfParent A₀ A₁ W) (Set.Icc (0 : ℝ) 1) := by
  apply (continuous_arbitraryPhysicalMixedInteraction A₀ A₁ hInj₀ hInj₁).continuousOn.congr
  intro γ hγ
  exact arbitraryPhysicalMixedWeakHopfParent_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W hInj₀ hInj₁ h₀ h₁ hW hγ

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed enlarged terms are positive semidefinite. -/
theorem arbitraryPhysicalMixedWeakHopfParent_posSemidef
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (arbitraryPhysicalMixedWeakHopfParent A₀ A₁ W γ).PosSemidef := by
  rw [arbitraryPhysicalMixedWeakHopfParent_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W hInj₀ hInj₁ h₀ h₁ hW hγ]
  exact arbitraryPhysicalMixedInteraction_posSemidef A₀ A₁ γ

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The periodic completed enlarged Hamiltonian commutes with the actual
common MPO at every ring length at least two. The realization is on the active
space; no realization on the enlarged space or adjoint-closure premise is assumed. -/
theorem hamiltonian_arbitraryPhysicalMixedWeakHopfParent_commute
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedWeakHopfParent A₀ A₁ W γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) := by
  have : NeZero N := ⟨by omega⟩
  rw [arbitraryPhysicalMixedWeakHopfParent_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W hInj₀ hInj₁ h₀ h₁ hW hγ]
  apply hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁ _ hγ hN
  intro X
  obtain ⟨Y, hY⟩ := W.exists_adjointBoundary_changePhysicalBasis
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) X
  exact ⟨Y, by simpa only [hW, arbitraryPhysicalMixedMPO] using hY 2⟩

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed integral path has a positive spectral gap above its zero
ground energy, uniform in the parameter and all periodic ring lengths at least
two. This uses equality with the already established mixed parent path; no gap
is asserted for the literal uncompleted average. -/
theorem exists_uniform_arbitraryPhysicalMixedWeakHopfParent_gap :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ γ : unitInterval, ∀ N : ℕ, ∀ hN : 2 ≤ N,
      IsGapped (Interaction.translationInvariant hN
        (arbitraryPhysicalMixedWeakHopfParent A₀ A₁ W γ)).hamiltonian 0 δ := by
  obtain ⟨δ, hδ, hδ₁, hg⟩ := exists_uniform_arbitraryPhysicalMixed_periodic_path_gap
    A₀ A₁ hInj₀ hInj₁
  refine ⟨δ, hδ, hδ₁, fun γ N hN => ?_⟩
  rw [arbitraryPhysicalMixedWeakHopfParent_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W hInj₀ hInj₁ h₀ h₁ hW γ.property]
  exact hg γ N hN

end MPSTensor.MPOSymmetry
