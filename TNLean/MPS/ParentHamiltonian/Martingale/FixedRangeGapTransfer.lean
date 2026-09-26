/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicRangeComparison

/-!
# Transferring a parent-Hamiltonian gap to a prescribed range

If the open-chain Hamiltonian of range \(R\) on \(W\) sites has kernel
\(\mathcal G_W(A)\), it is comparable to the parent projection of range
\(W\). Summing all cyclic translates gives two-sided bounds on the periodic
Hamiltonians, and hence equal periodic kernels. A uniform gap at range
\(W\) therefore gives a uniform gap at range \(R\).
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

end MPSTensor
