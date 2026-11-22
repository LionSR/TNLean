/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.KernelGapPerturbation
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity

/-!
# Local stability of finite-window parent-Hamiltonian gaps

At a fixed window length, continuity of an injective tensor family gives
continuity of the Hamiltonian and its ground-space projection. Therefore
any strict lower gap bound persists near a given parameter. This is the
finite-window continuity step in arXiv:1010.3732, Appendix A; choosing a
common interaction range and a bound uniform in all chain lengths remains
a separate argument.
-/

open scoped Topology

namespace MPSTensor

/-- Every strictly smaller finite-window gap of the Hamiltonian of the parent interaction on the
open chain persists locally along a continuous tensor family injective at the interaction and
window lengths. The complement here is the canonical MPS ground space. Source:
arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem eventually_hamiltonian_parentChainInteraction_gap
    {X : Type*} [TopologicalSpace X] {d D R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hR : ∀ x, Kraus.IsNBlkInjective (A x) R)
    (hN : ∀ x, Kraus.IsNBlkInjective (A x) N) {x₀ : X}
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hgap : ∀ v ∈ (groundSpaceES (A x₀) N)ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (parentChainInteraction (A x₀) R N).hamiltonian v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ v ∈ (groundSpaceES (A x) N)ᗮ,
      δ' * ‖v‖ ≤ ‖Matrix.toEuclideanLin (parentChainInteraction (A x) R N).hamiltonian v‖ := by
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d N) (Cfg d N) ℂ ≃⋆ₐ[ℂ] _)
  have hH : Continuous fun x ↦ e (parentChainInteraction (A x) R N).hamiltonian :=
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_hamiltonian_parentChainInteraction_family A hA hR)
  apply ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun x ↦ e (parentChainInteraction (A x) R N).hamiltonian)
    (fun x => groundSpaceES (A x) N) hH.continuousAt
    (continuous_groundSpaceES_starProjection_family A hA N hN).continuousAt
    (by rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
        exact groundSpaceES_le_ker_hamiltonian_parentChainInteraction (A x₀) R N)
    hδ hδ' hgap

end MPSTensor
