/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactGapBounds
import TNLean.MPS.ParentHamiltonian.KnabeGapNeighborhood
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.PeriodicShortGapContinuity

/-!
# Uniform parent-Hamiltonian gaps on compact parameter sets

For a continuous one-site injective tensor family, pointwise strict Knabe
windows give a positive periodic gap uniform in the parameter and in all
sufficiently large chain lengths. The windows may have different lengths:
a finite subcover gives one common length threshold and gap bound.
Injectivity supplies the pointwise windows. Continuity of the periodic
ground-state projection handles the finitely many shorter rings, giving
one positive bound for every chain of at least two sites. This is the
compactness step in arXiv:1010.3732, Appendix A.
-/

open scoped Topology

namespace MPSTensor

/-- Pointwise strict nearest-neighbor Knabe windows give a uniform gap on a
compact parameter set. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_parentHamiltonianES_gap_of_strict_openWindows
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S)
    (hWindows : ∀ x ∈ S, ∃ m : ℕ, 2 ≤ m ∧ ∃ γ : ℝ,
      1 < (m : ℝ) * γ ∧
      ∀ v ∈ (groundSpaceES (A x) (m + 1))ᗮ,
        γ * ‖v‖ ≤ ‖openParentHamiltonianES (A x) 2 (m + 1) v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ := by
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ N₀ x => ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖)
  · intro δ δ' N₀ x hle hgap N hN v hv
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv)
  · intro δ N₀ N₁ x hle hgap N hN
    exact hgap N (hle.trans hN)
  · intro x hx
    obtain ⟨m, hm, γ, hnum, hgap⟩ := hWindows x hx
    obtain ⟨δ, hδ, hnear⟩ :=
      eventually_parentHamiltonianES_gap_of_strict_openGap A hA hInj hm hnum hgap
    exact ⟨δ, hδ, 2 * m, hnear⟩

/-- A continuous compact family of one-site injective tensors has a positive
nearest-neighbor parent-Hamiltonian gap uniform in the parameter and all
sufficiently large periodic chain lengths. No finite-window estimate is
assumed: it follows from injectivity. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ :=
  exists_uniform_parentHamiltonianES_gap_of_strict_openWindows A hA hInj hS
    (fun x _ => exists_strict_openParentHamiltonianES_two_window_of_isInjective (A x) (hInj x))

/-- A continuous compact family of one-site injective tensors has one positive
nearest-neighbor parent-Hamiltonian gap valid for every periodic chain of at
least two sites. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ := by
  classical
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isInjective A hA hInj hS
  have hshort : ∀ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ (2 ≤ N → ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨δ, hδ, hgap⟩ :=
        exists_uniform_parentHamiltonianES_two_gap_fixed_volume A hA hInj hS hN
      exact ⟨δ, hδ, fun _ => hgap⟩
    · exact ⟨1, zero_lt_one, fun h => (hN h).elim⟩
  choose ε hε hshort using hshort
  have ht : (Finset.range (N₀ + 1)).Nonempty := ⟨0, by simp⟩
  let δ₁ := (Finset.range (N₀ + 1)).inf' ht ε
  have hδ₁ : 0 < δ₁ := (Finset.lt_inf'_iff _).2 (fun n _ => hε n)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro x hx N hN v hv
  by_cases hlongN : N₀ ≤ N
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans
      (hlong x hx N hlongN v hv)
  · have hmem : N ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
    have hle : min δ₀ δ₁ ≤ ε N := (min_le_right _ _).trans (Finset.inf'_le ε hmem)
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans
      (hshort N hN x hx v hv)

end MPSTensor
