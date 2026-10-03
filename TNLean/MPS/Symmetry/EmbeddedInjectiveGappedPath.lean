/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Symmetry.CanonicalInjectiveGappedPath
import TNLean.MPS.Symmetry.PolarDeformation

/-!
# Injective parent paths in a common physical representation

A physical isometry intertwining two on-site actions transports a continuous
injective tensor family into the common physical representation. Compactness
then gives a uniform gap for the embedded canonical parent interactions,
including their action on unused physical states.

**Scope restriction (one-site injective tensors):** the parent paths constructed
here are the single-block, one-site injective case of arXiv:1010.3732,
Sections II.C and II.F.2, equation eq:1d-sym:jointsym. The source also treats
several-block normal forms. Documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Sections II.C and II.F.2
-/

open scoped Matrix

namespace MPSTensor

/-- A fixed physical map acts continuously on tensors.
Source context: arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem continuous_rotatePhysical {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) :
    Continuous fun A : MPSTensor d D => rotatePhysical E A := by
  unfold rotatePhysical
  fun_prop

/-- An intertwining physical map transports bond-conjugation covariance.
Source context: arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem gaugeEquiv_rotatePhysical_of_intertwiner {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin m) (Fin m) ℂ)
    (hE : V * E = E * U) (hCov : GaugeEquiv A (rotatePhysical U A)) :
    GaugeEquiv (rotatePhysical E A) (rotatePhysical V (rotatePhysical E A)) := by
  rw [rotatePhysical_rotatePhysical, hE, ← rotatePhysical_rotatePhysical]
  exact hCov.sum_smul E

/-- A continuous injective family embedded by an intertwining physical
isometry has a uniformly gapped canonical parent path under the prescribed
common on-site action. Source context: arXiv:1010.3732, Sections II.C and
II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def embeddedCanonicalInjectiveGappedPath
    {G : Type} [Group G] {d m D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (hInt : ∀ g, (V g : Matrix (Fin m) (Fin m) ℂ) * E =
      E * (U g : Matrix (Fin d) (Fin d) ℂ))
    (A : ℝ → MPSTensor d D) (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hInj : ∀ γ ∈ Set.Icc (0 : ℝ) 1, Kraus.IsInjective (A γ))
    (hCov : ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ g,
      GaugeEquiv (A γ) (rotatePhysical (U g) (A γ))) :
    SymmetricGappedInteractionPath V
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical E (A 0)) 2))
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical E (A 1)) 2)) :=
  canonicalInjectiveGappedPath V (fun γ => rotatePhysical E (A γ))
    ((continuous_rotatePhysical E).comp_continuousOn hA)
    (fun γ hγ => isInjective_kraus_isometry (A γ) E hE (hInj γ hγ))
    (fun γ hγ g => gaugeEquiv_rotatePhysical_of_intertwiner
      E (A γ) (U g) (V g) (hInt g) (hCov γ hγ g))

/-- The embedded canonical parents of an injective tensor and its polar
isometric form are connected under the prescribed common physical action.
Source context: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym. -/
noncomputable def embeddedPolarGappedInteractionPath
    {G : Type} [Group G] {d m D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (hInt : ∀ g, (V g : Matrix (Fin m) (Fin m) ℂ) * E =
      E * (U g : Matrix (Fin d) (Fin d) ℂ))
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : G → Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A =
      fun i => (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    SymmetricGappedInteractionPath V
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical E (polarIsometricTensor A)) 2))
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical E A) 2)) := by
  let P := embeddedCanonicalInjectiveGappedPath U V E hE hInt (polarDeformation A)
      (continuous_polarDeformation A).continuousOn
      (fun _ hγ => isInjective_polarDeformation hA hγ)
      (fun γ _ g => gaugeEquiv_polarDeformation_of_unitary_covariance hA
        (U g) (X g) (SetLike.coe_mem _) (SetLike.coe_mem _) (hCov g) γ)
  exact {
    interaction γ := LinearMap.toMatrix'
      (parentInteraction (rotatePhysical E (polarDeformation A γ)) 2)
    interaction_zero := by rw [polarDeformation_zero]
    interaction_one := by rw [polarDeformation_one]
    hermitian := P.hermitian
    norm_le_one := P.norm_le_one
    continuous := P.continuous
    gap := P.gap
    symmetric := P.symmetric }

end MPSTensor
