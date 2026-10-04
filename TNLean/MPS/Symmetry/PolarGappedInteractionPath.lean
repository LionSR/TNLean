/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CanonicalInjectiveGappedPath
import TNLean.MPS.Symmetry.PolarDeformation

/-!
# The symmetric gapped interaction path of a polar deformation

For a one-site injective tensor in unitary virtual gauge, the polar
deformation gives a symmetric gapped path between the canonical parents of
its isometric form and of the original tensor, on the original physical space.

**Scope restriction (one-site injective tensors):** this is the single-block,
one-site injective case of arXiv:1010.3732, Section II.C and Appendix A.
The source also treats several-block normal forms. Documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- The canonical parents of an injective tensor and its isometric form
are joined by a symmetric gapped interaction path, provided the tensor's
covariance is expressed by unitary bond conjugation. The same physical
space and on-site representation are used throughout. Source:
arXiv:1010.3732, Section II.C, “Isometric form and symmetries”. -/
noncomputable def polarGappedInteractionPath
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : G → Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A =
      fun i => (X g : Matrix (Fin D) (Fin D) ℂ) * A i * (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    SymmetricGappedInteractionPath U
      (LinearMap.toMatrix' (parentInteraction (polarIsometricTensor A) 2))
      (LinearMap.toMatrix' (parentInteraction A 2)) := by
  simpa only [polarDeformation_zero, polarDeformation_one] using
    canonicalInjectiveGappedPath U (polarDeformation A)
      (continuous_polarDeformation A).continuousOn
      (fun _ hγ => isInjective_polarDeformation hA hγ)
      (fun γ _ g => gaugeEquiv_polarDeformation_of_unitary_covariance hA
        (U g) (X g) (SetLike.coe_mem _) (SetLike.coe_mem _) (hCov g) γ)

end MPSTensor
