/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KernelGap
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.FiniteRangeKnabeGap
import TNLean.MPS.Tensor.Words.WordSpan
import QICLean.Spectral.Gap.EigenvalueGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Continuity.PeriodicShortGapContinuity

/-!
# Local stability of finite-window parent-Hamiltonian gaps

At a fixed window length, continuity of an injective tensor family gives
continuity of the Hamiltonian and its ground-space projection. Therefore
any strict lower gap bound persists near a given parameter. This is the
finite-window continuity step in arXiv:1010.3732, Appendix A; choosing a
common interaction range and a bound uniform in all chain lengths remains
a separate argument.

## Parameter neighborhoods with a uniform nearest-neighbor gap

A strict finite-window Knabe estimate is stable along a continuous family
of one-site injective tensors. Consequently one positive periodic gap bound
works in a whole parameter neighborhood and for every sufficiently long
chain. This is a local ingredient of the compact-parameter gap argument in
arXiv:1010.3732, Appendix A.

## Uniform parent-Hamiltonian gaps on compact parameter sets

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

section

open scoped Topology

namespace MPSTensor

/-- Every strictly smaller finite-window gap of the Hamiltonian of the parent interaction on the
open chain persists locally along a continuous tensor family injective at the interaction and
window lengths, together with the identification of the kernel with the canonical MPS ground
space. Source: arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem eventually_hamiltonian_parentChainInteraction_gap
    {X : Type*} [TopologicalSpace X] {d D R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hR : ∀ x, Kraus.IsNBlkInjective (A x) R)
    (hN : ∀ x, Kraus.IsNBlkInjective (A x) N) {x₀ : X}
    {δ δ' : ℝ} (hδ' : δ' < δ)
    (hgap : ManyBody.groundSpace (parentChainInteraction (A x₀) R N).hamiltonian 0 =
        groundSpaceES (A x₀) N ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction (A x₀) R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ᶠ x in 𝓝 x₀,
      ManyBody.groundSpace (parentChainInteraction (A x) R N).hamiltonian 0 =
          groundSpaceES (A x) N ∧
        ∀ μ : ℂ, Module.End.HasEigenvalue
          (Matrix.toEuclideanLin (parentChainInteraction (A x) R N).hamiltonian) μ →
            μ = 0 ∨ (δ' : ℂ) ≤ μ :=
  ManyBody.eventually_groundSpace_zero_eq_and_forall_hasEigenvalue
    (continuous_hamiltonian_parentChainInteraction_family A hA hR).continuousAt
    (Filter.Eventually.of_forall fun x ↦ posSemidef_hamiltonian_parentChainInteraction (A x) R N)
    (continuous_groundSpaceES_starProjection_family A hA N hN).continuousAt
    (Filter.Eventually.of_forall fun x ↦ by
      rw [ManyBody.groundSpace_zero]
      exact groundSpaceES_le_ker_hamiltonian_parentChainInteraction (A x) R N)
    hgap hδ'

end MPSTensor

end

section

open scoped Topology ComplexOrder

namespace MPSTensor

/-- A strict nearest-neighbor Knabe window at one parameter yields a gap
uniform over a neighborhood and all chains beyond the same length threshold.
Source: arXiv:1010.3732, Appendix A; the finite-size estimate is the
nearest-neighbor case of Knabe's inequality. -/
theorem eventually_hamiltonian_parentRingInteraction_gap_of_strict_openGap
    {X : Type*} [TopologicalSpace X] {d D m : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hm : 2 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : 1 < (m : ℝ) * γ)
    (hgap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction (A x₀) 2 (m + 1)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ (N : ℕ) (hN : 2 * m ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < γ := (div_lt_iff₀ hmpos).2 (by simpa [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hnear := ManyBody.eventually_forall_hasEigenvalue
    (continuous_hamiltonian_parentChainInteraction_family A hA (N := m + 1) fun x ↦
      Kraus.isNBlkInjective_of_le one_pos
        (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega)).continuousAt
    (Filter.Eventually.of_forall fun x ↦
      posSemidef_hamiltonian_parentChainInteraction (A x) 2 (m + 1))
    (by
      refine (continuous_groundSpaceES_starProjection_family A hA (m + 1) fun x ↦
        Kraus.isNBlkInjective_of_le one_pos (Kraus.isNBlkInjective_one_of_isInjective (hInj x))
          (by omega)).continuousAt.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [ManyBody.groundSpace_zero,
        ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
          (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega) (by omega)])
    hgap hγ'upper
  have hnum' : ((2 : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    have h := (div_lt_iff₀ hmpos).1 hγ'lower
    norm_num at *
    nlinarith
  let δ : ℝ := ((m : ℝ) * γ' - ((2 : ℝ) - 1) ^ 2) / ((m : ℝ) - 2 + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx N hN
    refine (hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap (A x)
      (R := 2) (m := m) (by omega) hm hnum' ?_).2 N hN
    rw [show m + 2 - 1 = m + 1 by omega]
    exact hx

end MPSTensor

end

section

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

end
