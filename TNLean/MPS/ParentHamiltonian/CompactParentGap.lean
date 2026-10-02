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

**Scope restriction (one-site injective tensors):** arXiv:1010.3732,
Appendix A, lines 2475--2580, proves the uniform gap along a path of tensors in
normal form, possibly with several blocks. The two compact-gap theorems here
treat continuous families of one-site injective tensors with the canonical
two-site interaction, replacing Nachtergaele's bound by Knabe's criterion.
The normal-family and multiblock extensions are proved separately in
`CompactNormalParentGap.lean` and `CompactBlockParentGap.lean`; continuous
positive interactions are treated in `CompactParentInteractionGap.lean`.
The earlier restriction and its resolution are documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
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
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isInjective A hA hInj hS
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => 2 ≤ N → ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖)
    (fun N γ δ hle h hN x hx v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (h hN x hx v hv))
    (fun N => by
      by_cases hN : 2 ≤ N
      · obtain ⟨δ, hδ, hgap⟩ :=
          exists_uniform_parentHamiltonianES_two_gap_fixed_volume A hA hInj hS hN
        exact ⟨δ, hδ, fun _ => hgap⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN _ x hx => hlong x hx N hN)
  exact ⟨δ, hδ, fun x hx N hN => hgap N hN x hx⟩

end MPSTensor
