/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import QICLean.Analysis.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicRangeComparison

/-!
# Transferring a parent-Hamiltonian gap to a prescribed range

If the open-chain Hamiltonian of range \(R\) on \(W\) sites has kernel
\(\mathcal G_W(A)\), it is comparable to the parent projection of range
\(W\). Summing all cyclic translates gives two-sided bounds on the periodic
Hamiltonians, and hence equal periodic kernels. A uniform gap at range
\(W\) therefore gives a uniform gap at range \(R\).

The transfer is stated, in the last section, for the Hamiltonians of the parent interactions on
the ring (`parentRingInteraction`) and on the open chain (`parentChainInteraction`).

**Transitional (#10948).** `exists_parentHamiltonianES_gap_of_larger_range` is kept, unchanged,
for unconverted users and is deleted when its last user is converted.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

/-- A uniform periodic gap at a longer range transfers to a prescribed range
whose open-chain kernel on that longer interval is the full local MPS space. -/
theorem exists_parentHamiltonianES_gap_of_larger_range
    {d D R W : ℕ} (A : MPSTensor d D) (hR : 0 < R) (hRW : 2 * R ≤ W)
    (hker : LinearMap.ker (openParentHamiltonianES A R W) = groundSpaceES A W)
    {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ᶠ N : ℕ in atTop, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A W N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES A W N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
    exists_pos_parentInteractionES_openParentHamiltonianES_comparison A hker
  have hm : 0 < W - R + 1 := by omega
  have hmR : R ≤ W - R + 1 := by omega
  have hlength : (W - R + 1) + R - 1 = W := by omega
  refine ⟨κ * γ / (W - R + 1 : ℕ), div_pos (mul_pos hκ hγ)
    (Nat.cast_pos.mpr hm), ?_⟩
  filter_upwards [hGap, eventually_ge_atTop (2 * (W - R + 1))] with N hGapN hN
  have : NeZero N := ⟨by omega⟩
  have hComparison := parentHamiltonianES_comparison_of_local_open_comparison A
    (κ := κ) (C := C) hR hmR hN (by rw [hlength]; exact hLower)
    (by rw [hlength]; exact hUpper)
  exact (parentHamiltonianES_isPositive A W N).norm_gap_of_smul_le_of_le_smul
    (parentHamiltonianES_isPositive A R N) hκ (Nat.cast_pos.mpr hm) hC hγ
    (by simpa only [hlength, Complex.ofReal_natCast] using hComparison.1)
    (by simpa only [hlength, Complex.ofReal_natCast] using hComparison.2) hGapN

/-! ### The parent interactions on the ring and on the open chain -/

/-- A uniform gap of the Hamiltonians of the parent interaction of a longer range on the rings
transfers to a prescribed range whose open-chain Hamiltonian on that longer interval has the
full local MPS space as kernel. Each gap is stated above the kernel: every eigenvalue is `0` or
at least the gap. -/
theorem exists_hamiltonian_parentRingInteraction_gap_of_larger_range
    {d D R W : ℕ} (A : MPSTensor d D) (hR : 0 < R) (hRW : 2 * R ≤ W)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) =
      groundSpaceES A W)
    {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ᶠ N : ℕ in atTop, ∀ hWN : W ≤ N, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A hWN).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ hRN : R ≤ N, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A hRN).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison A hker
  have hm : 0 < W - R + 1 := by omega
  have hmR : R ≤ W - R + 1 := by omega
  have hlength : (W - R + 1) + R - 1 = W := by omega
  refine ⟨κ * γ / (W - R + 1 : ℕ), div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr hm), ?_⟩
  filter_upwards [hGap, eventually_ge_atTop (2 * (W - R + 1))] with N hGapN hN hRN
  have : NeZero N := ⟨by omega⟩
  have hWN : W ≤ N := by omega
  have hham : ∀ {L L' : ℕ} (_ : L = L') (h : L ≤ N) (h' : L' ≤ N),
      (parentRingInteraction A h).hamiltonian = (parentRingInteraction A h').hamiltonian := by
    rintro L L' rfl h h'
    rfl
  have hComparison := hamiltonian_parentRingInteraction_comparison_of_local_open_comparison A
    (κ := κ) (C := C) hR hmR hN (by rw [hlength]; exact hLower) (by rw [hlength]; exact hUpper)
  rw [hham hlength _ hWN] at hComparison
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hComparison.1
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hComparison.2
  rw [map_smul, map_smul] at h1 h2
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (posSemidef_hamiltonian_parentRingInteraction A hRN)).mpr ?_
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentRingInteraction A hWN)).norm_gap_of_smul_le_of_le_smul
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentRingInteraction A hRN))
    hκ (Nat.cast_pos.mpr hm) hC hγ (by simpa only [Complex.ofReal_natCast] using h1)
    (by simpa only [Complex.ofReal_natCast] using h2)
    ((ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentRingInteraction A hWN)).mp (hGapN hWN))

end MPSTensor
