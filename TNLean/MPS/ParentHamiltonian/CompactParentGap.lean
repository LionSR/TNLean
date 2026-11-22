/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.CompactKernelGap
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
The multiblock, positive-interaction, and isometric-deformation results in
`CompactBlockParentGap.lean`, `CompactParentInteractionGap.lean`, and
`IsometricDeformation.lean` remove this restriction for the source path;
documented in `docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

/-- Pointwise strict nearest-neighbor Knabe windows give a uniform gap on a
compact parameter set: every eigenvalue other than zero of the Hamiltonians of the two-site
parent interaction on the long rings is at least the gap. Source: arXiv:1010.3732,
Appendix A. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_strict_openWindows
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S)
    (hWindows : ∀ x ∈ S, ∃ m : ℕ, 2 ≤ m ∧ ∃ γ : ℝ,
      1 < (m : ℝ) * γ ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction (A x) 2 (m + 1)).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  refine hS.exists_uniform_pos_nat_bounds (fun δ N₀ x ↦ ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ)
    (fun hle hgap N _ hN ↦ ManyBody.forall_hasEigenvalue_mono hle (hgap N hN))
    (fun hle hgap N _ hN ↦ hgap N (hle.trans hN)) fun x hx ↦ ?_
  obtain ⟨m, hm, γ, hnum, hgap⟩ := hWindows x hx
  obtain ⟨δ, hδ, hnear⟩ :=
    eventually_hamiltonian_parentRingInteraction_gap_of_strict_openGap A hA hInj hm hnum hgap
  exact ⟨δ, hδ, 2 * m, hnear.mono fun y hy N _ hN ↦ hy N hN⟩

/-- A continuous compact family of one-site injective tensors has a positive
gap of the Hamiltonians of the two-site parent interaction, uniform in the parameter and all
sufficiently large rings. No finite-window estimate is
assumed: it follows from injectivity. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ :=
  exists_uniform_hamiltonian_parentRingInteraction_gap_of_strict_openWindows A hA hInj hS
    (fun x _ => exists_strict_hamiltonian_parentChainInteraction_two_window_of_isInjective (A x)
        (hInj x))

/-- A continuous compact family of one-site injective tensors has one positive
gap valid on every ring of at least two sites: the Hamiltonian of the two-site parent
interaction is gapped above its zero ground energy. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective_all_lengths
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) 2 N).hamiltonian 0 δ := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective A hA hInj hS
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ hN : 2 ≤ N, ∀ x ∈ S, haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) 2 N).hamiltonian 0 δ)
    (fun N γ δ hle h hN x hx => (h hN x hx).mono hle)
    (fun N => by
      by_cases hN : 2 ≤ N
      · obtain ⟨δ, hδ, hgap⟩ :=
          exists_uniform_hamiltonian_parentRingInteraction_two_gap_fixed_volume A hA hInj hS hN
        exact ⟨δ, hδ, fun _ => hgap⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN hN2 x hx =>
      haveI : NeZero N := ⟨by omega⟩
      ManyBody.isGapped_zero_iff.mpr
        ⟨groundSpace_hamiltonian_parentRingInteraction_two_ne_bot (A x) (hInj x) hN2,
          hlong x hx N hN⟩)
  exact ⟨δ, hδ, fun x hx N hN => hgap N hN x hx⟩

end MPSTensor
