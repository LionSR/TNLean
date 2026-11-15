/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Basic.Real.Basic

/-!
# Uniform bounds from local bounds on a compact set

A neighborhood bound at each parameter can be made uniform on a compact
parameter set when it persists after decreasing its positive real constant
and increasing its natural-number threshold. The interiors of the sets where
each bound holds form a directed open cover, so one of them covers the compact set.

This is the compactness step in the gap argument of arXiv:1010.3732,
Appendix A. No spectral assertion is built into this lemma.
-/

open scoped Topology

namespace IsCompact

/-- A positive constant and a natural-number threshold, valid locally at
every point of a compact set, can be chosen uniformly when the assertion is
monotone under weakening these bounds. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_pos_nat_bounds {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) (P : ℝ → ℕ → X → Prop)
    (hδ : ∀ {δ δ' : ℝ} {N : ℕ} {x : X}, δ ≤ δ' → P δ' N x → P δ N x)
    (hN : ∀ {δ : ℝ} {N N' : ℕ} {x : X}, N ≤ N' → P δ N x → P δ N' x)
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧
      ∃ N : ℕ, ∀ᶠ y in 𝓝 x, P δ N y) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S, P δ N x := by
  let U : {δ : ℝ // 0 < δ} × ℕ → Set X :=
    fun b ↦ interior {x | P b.1 b.2 x}
  letI : Nonempty ({δ : ℝ // 0 < δ} × ℕ) := ⟨(⟨1, zero_lt_one⟩, 0)⟩
  obtain ⟨⟨δ, N⟩, hcover⟩ := hS.elim_directed_cover U (fun _ ↦ isOpen_interior) (by
    intro x hx
    obtain ⟨δ, hδpos, N, hnear⟩ := hlocal x hx
    exact Set.mem_iUnion.mpr ⟨(⟨δ, hδpos⟩, N), mem_interior_iff_mem_nhds.mpr hnear⟩) (by
    rintro ⟨δ₁, N₁⟩ ⟨δ₂, N₂⟩
    refine ⟨(⟨min δ₁.1 δ₂.1, lt_min δ₁.property δ₂.property⟩, max N₁ N₂), ?_, ?_⟩
    · exact interior_mono fun x hx ↦ hN (le_max_left N₁ N₂) (hδ (min_le_left _ _) hx)
    · exact interior_mono fun x hx ↦ hN (le_max_right N₁ N₂) (hδ (min_le_right _ _) hx))
  exact ⟨δ, δ.property, N, fun x hx ↦ interior_subset (hcover hx)⟩

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
