/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KernelGapPerturbation
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

/-- Every strictly smaller finite-window gap persists locally along a
continuous tensor family injective at the interaction and window lengths.
The complement here is the canonical MPS ground space. Source:
arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem eventually_openParentHamiltonianES_gap
    {X : Type*} [TopologicalSpace X] {d D R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hRN : R ≤ N)
    (hR : ∀ x, Kraus.IsNBlkInjective (A x) R)
    (hN : ∀ x, Kraus.IsNBlkInjective (A x) N) {x₀ : X}
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hgap : ∀ v ∈ (groundSpaceES (A x₀) N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES (A x₀) R N v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ v ∈ (groundSpaceES (A x) N)ᗮ,
      δ' * ‖v‖ ≤ ‖openParentHamiltonianES (A x) R N v‖ := by
  apply ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun x => LinearMap.toContinuousLinearMap (openParentHamiltonianES (A x) R N))
    (fun x => groundSpaceES (A x) N)
    (continuous_openParentHamiltonianES_family A hA hRN hR).continuousAt
    (continuous_groundSpaceES_starProjection_family A hA N hN).continuousAt
    (groundSpaceES_le_ker_openParentHamiltonianES (A x₀) R N) hδ hδ' hgap

end MPSTensor
