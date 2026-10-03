/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactGapBounds
import TNLean.Algebra.KernelGapPerturbation
import TNLean.Algebra.OrthogonalKernelGap

/-!
# Uniform finite-dimensional gaps on compact parameter sets

A continuous family of operators on a finite-dimensional Hilbert space has a
uniform positive lower norm bound away from its kernels on a compact parameter
set, provided the orthogonal kernel projections are continuous. Positivity and
self-adjointness are unnecessary for this norm estimate.

This isolates the finite-window continuity argument in arXiv:1010.3732,
Appendix A, lines 2575--2578, from the structure of matrix product states.
-/

open scoped Topology

namespace ContinuousLinearMap

/-- Continuous operators with continuous orthogonal kernel projections have a
uniform positive norm gap on compact parameter sets. The pointwise gaps follow
from finite dimensionality. Source: arXiv:1010.3732, Appendix A, lines 2575--2578,
for the application to finite-window parent Hamiltonians. -/
theorem exists_uniform_norm_gap_of_compact
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : X → E →L[ℂ] E) (hH : Continuous H)
    (hK : Continuous fun x => (LinearMap.ker (H x).toLinearMap).starProjection)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ := by
  suffices ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ by
    obtain ⟨δ, hδ, _, hgap⟩ := this
    exact ⟨δ, hδ, hgap⟩
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ _ x => ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ,
      δ * ‖v‖ ≤ ‖H x v‖)
  · exact fun hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv)
  · exact fun _ hgap => hgap
  · intro x _hx
    obtain ⟨γ, hγ, hgap⟩ :=
      (H x).toLinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
    refine ⟨γ / 2, half_pos hγ, 0, ?_⟩
    apply eventually_norm_gap_on_orthogonal H
      (fun y => LinearMap.ker (H y).toLinearMap)
      hH.continuousAt hK.continuousAt le_rfl hγ (half_lt_self hγ) hgap

end ContinuousLinearMap
