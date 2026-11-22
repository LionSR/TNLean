/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Perturbation.KernelGapPerturbation
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.FiniteRangeKnabeGap
import TNLean.MPS.Tensor.Words.WordSpan
import QICLean.Spectral.Gap.CompactKernelGap
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

end

section

open scoped Topology

namespace MPSTensor

/-- A strict nearest-neighbor Knabe window at one parameter yields a gap
uniform over a neighborhood and all chains beyond the same length threshold.
Source: arXiv:1010.3732, Appendix A; the finite-size estimate is the
nearest-neighbor case of Knabe's inequality. -/
theorem eventually_parentHamiltonianES_gap_of_strict_openGap
    {X : Type*} [TopologicalSpace X] {d D m : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hm : 2 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : 1 < (m : ℝ) * γ)
    (hgap : ∀ v ∈ (groundSpaceES (A x₀) (m + 1))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES (A x₀) 2 (m + 1) v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ N : ℕ, 2 * m ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < γ := (div_lt_iff₀ hmpos).2 (by simpa [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ := (div_pos zero_lt_one hmpos).trans hthreshold
  have hnear := eventually_openParentHamiltonianES_gap A hA (by omega : 2 ≤ m + 1)
    (fun x => isNBlkInjective_of_le one_pos
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega))
    (fun x => isNBlkInjective_of_le one_pos
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega)) hγpos hγ'upper hgap
  have hnum' : ((2 : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    have h := (div_lt_iff₀ hmpos).1 hγ'lower
    norm_num at *
    nlinarith
  let δ := ((m : ℝ) * γ' - ((2 : ℝ) - 1) ^ 2) / ((m : ℝ) - 2 + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx
    apply (parentHamiltonianES_gap_of_openParentHamiltonianES_gap (A x)
      (R := 2) (m := m) (by omega) hm hnum' ?_).2
    rw [show m + 2 - 1 = m + 1 by omega,
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega) (by omega)]
    exact hx

end MPSTensor

end

section

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
  refine hS.exists_uniform_norm_lower_bound_on_tail (fun x N => parentHamiltonianES (A x) 2 N)
    (fun x N => (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ) fun x hx => ?_
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

end
