/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.UniformProjectiveRigidity

/-!
# Local constancy of the virtual class near an injective tensor

Continuity of the tensor and injectivity at one parameter make the virtual
adjoint actions uniformly close under a fixed physical symmetry. Uniform
projective rigidity then makes the cohomology class locally constant. The
parameter space is arbitrary, so this result also applies to convergent
sequences; no interpolation of the virtual representatives is required.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The tensor family
and its exact covariance are supplied. Their derivation from a physical gap
is not asserted here.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.Frobenius Topology

namespace MPSTensor

/-- For a continuous tensor family injective at the base point, exact covariance
under a fixed unitary physical action makes the virtual projective class locally
constant. Virtual representatives may be chosen independently at each parameter.
This is an auxiliary finite-dimensional rigidity result for arXiv:1010.3732,
Appendix C, lines 2653–2717, and does not construct tensors or virtual actions
from a gapped Hamiltonian path. -/
theorem eventually_cohomologousTo_of_continuousAt_exact_unitary_covariance
    {T : Type*} [TopologicalSpace T] {G : Type} [Group G]
    {d D : ℕ} [NeZero D] (C : T → MPSTensor d D) (t₀ : T)
    (hC : ContinuousAt C t₀) (hInject : Kraus.IsInjective (C t₀))
    (U : G → Matrix.unitaryGroup (Fin d) ℂ)
    (ω : T → TNLean.Algebra.ScalarCocycle G)
    (ρ : ∀ t, TNLean.Algebra.ProjectiveRepresentation (D := D) (ω t))
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ t g i, ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • C t j =
      ((ρ t).X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * C t i *
        ((ρ t).X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  obtain ⟨δ, hδ, hRigidity⟩ :=
    TNLean.Algebra.ProjectiveRepresentation.exists_uniform_adjoint_rigidity_radius (D := D)
  have hEstimate := eventually_uniform_conjugationEuclideanCLM_of_covariance
    (C t₀) hInject U (fun g => ((ρ t₀).X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)) (hCov t₀) δ hδ
  filter_upwards [hC.eventually hEstimate] with t ht
  apply hRigidity G (ω t₀) (ω t) (ρ t₀) (ρ t) (hUnitary t₀) (hUnitary t)
  intro g
  simpa only [inv_inv] using ht g⁻¹ ((ρ t).X g) (by simpa only [inv_inv] using hCov t g⁻¹)

end MPSTensor
