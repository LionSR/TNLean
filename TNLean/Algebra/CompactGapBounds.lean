/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Group.Basic
import QICLean.Topology.CompactUniformBounds

/-!
# Uniform norm lower bounds on a tail over a compact set

Locally uniform norm lower bounds, valid for every length beyond a threshold, have one positive
constant and one threshold over a compact parameter set. This is the norm-form specialization of
the compactness step in the gap argument of arXiv:1010.3732, Appendix A, whose general form
`IsCompact.exists_uniform_pos_nat_bounds` is in QICLean. No spectral assertion is built into
this lemma.
-/

open scoped Topology

namespace IsCompact

/-- Locally uniform norm lower bounds on a tail have one positive constant
and one threshold over a compact parameter set. This specializes the compactness
step of arXiv:1010.3732, Appendix A; linearity is unnecessary. -/
theorem exists_uniform_norm_lower_bound_on_tail
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {E F : ℕ → Type*} [∀ N, SeminormedAddCommGroup (E N)]
    [∀ N, SeminormedAddCommGroup (F N)]
    (H : X → ∀ N : ℕ, E N → F N) (V : X → ∀ N : ℕ, Set (E N))
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ᶠ y in 𝓝 x, ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V y N, δ * ‖v‖ ≤ ‖H y N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖ := by
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ N₀ x => ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖)
  · intro δ δ' N₀ x hle hgap N hN v hv
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv)
  · intro δ N₀ N₁ x hle hgap N hN
    exact hgap N (hle.trans hN)
  · exact hlocal

end IsCompact
