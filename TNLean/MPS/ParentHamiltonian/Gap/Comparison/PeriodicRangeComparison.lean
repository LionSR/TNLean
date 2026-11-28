/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import QICLean.Spectral.Gap.PositiveComparisonGap

/-!
# Periodic comparison from a finite open interval

A comparison between a parent projector and a shorter-range open Hamiltonian
can be translated around a periodic chain. Summing the translated inequalities
counts each shorter-range interaction once for every position within the open
window. This gives an operator comparison between the periodic Hamiltonians.

## Transferring a parent-Hamiltonian gap to a prescribed range

If the open-chain Hamiltonian of range \(R\) on \(W\) sites has kernel
\(\mathcal G_W(A)\), it is comparable to the parent projection of range
\(W\). Summing all cyclic translates gives two-sided bounds on the periodic
Hamiltonians, and hence equal periodic kernels. A uniform gap at range
\(W\) therefore gives a uniform gap at range \(R\).

The transfer is stated for the Hamiltonians of the parent interactions on
the ring (`parentRingInteraction`) and on the open chain (`parentChainInteraction`).
-/

section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-! ### The comparison for the Hamiltonians of the parent interactions

The comparison for the Hamiltonians of the parent interactions on the ring
(`parentRingInteraction`) and on the open interval (`parentChainInteraction`), in the matrix
order. -/

section Interaction

open scoped MatrixOrder
open Fin.CommRing

/-- The term with index `0` of the parent interaction on the ring of `W` sites is the local
parent interaction: its window is the whole ring. -/
theorem parentRingInteraction_term_zero_self (A : MPTensor α (Fin D)) {W : ℕ} (hW : 0 < W) :
    haveI : NeZero W := ⟨by omega⟩;
    (parentRingInteraction A W W).term ⟨0, hW⟩ =
      LinearMap.toMatrix' (parentInteraction A W) := by
  have : NeZero W := ⟨by omega⟩
  rw [ManyBody.Interaction.translationInvariant_term_of_le _ (le_refl W)]
  have hw : ManyBody.ringWindow (le_refl W) (⟨0, hW⟩ : Fin W) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun j ↦ Fin.ext (by
      simp [ManyBody.ringWindow_apply])
  rw [hw, ManyBody.placeAlong_refl]

/-- **Periodic comparison from an open window.** A two-sided comparison between the local parent
projection on \(m + R - 1\) sites and the range-\(R\) open-chain parent Hamiltonian on those sites
gives a two-sided comparison of the periodic parent Hamiltonians of ranges \(m + R - 1\) and
\(R\): each range-\(R\) term occurs in exactly \(m\) windows. This is the finite-range comparison
used in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`. -/
theorem hamiltonian_parentRingInteraction_comparison_of_local_open_comparison
    (A : MPTensor α (Fin D)) {R m N : ℕ}
    (hR : 1 ≤ R) (hmR : R ≤ m) (hN : 2 * m ≤ N) {κ C : ℝ}
    (hLower : (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A (m + R - 1)) ≤
      (parentChainInteraction A R (m + R - 1)).hamiltonian)
    (hUpper : (parentChainInteraction A R (m + R - 1)).hamiltonian ≤
      (C : ℂ) • LinearMap.toMatrix' (parentInteraction A (m + R - 1))) :
    haveI : NeZero N := ⟨by omega⟩;
    (κ : ℂ) • (parentRingInteraction A (m + R - 1) N).hamiltonian ≤
        (m : ℂ) • (parentRingInteraction A R N).hamiltonian ∧
      (m : ℂ) • (parentRingInteraction A R N).hamiltonian ≤
        (C : ℂ) • (parentRingInteraction A (m + R - 1) N).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  have hWN : m + R - 1 ≤ N := by omega
  have hsum : ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ α) (ManyBody.ringWindow hWN i)
      (parentChainInteraction A R (m + R - 1)).hamiltonian =
      (m : ℂ) • (parentRingInteraction A R N).hamiltonian := by
    simp only [← ManyBody.Interaction.translationInvariant_term_of_le _ hWN,
      ManyBody.Interaction.translationInvariant_term_hamiltonian_chainTranslates _ hWN]
    rw [Finset.sum_comm]
    have hshift (j : Fin (m + R - 1 + 1 - R)) :
        ∑ i : Fin N, (parentRingInteraction A R N).term (i + (j.val : Fin N)) =
          (parentRingInteraction A R N).hamiltonian :=
      Fintype.sum_equiv (Equiv.addRight (j.val : Fin N)) _ _ fun _ ↦ rfl
    simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      show m + R - 1 + 1 - R = m by omega, Nat.cast_smul_eq_nsmul]
  have hring (W : ℕ) (hW : W ≤ N) (c : ℂ) : c • (parentRingInteraction A W N).hamiltonian =
      ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ α) (ManyBody.ringWindow hW i)
        (c • LinearMap.toMatrix' (parentInteraction A W)) := by
    simp only [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hW,
      ManyBody.placeAlong_smul, Finset.smul_sum]
  constructor
  · rw [hring _ hWN, ← hsum]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hLower
  · rw [hring _ hWN, ← hsum]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hUpper

end Interaction

end MPSTensor

end

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

/-- A uniform gap of the Hamiltonians of the parent interaction of a longer range on the rings
transfers to a prescribed range whose open-chain Hamiltonian on that longer interval has the
full local MPS space as kernel. Each gap is stated above the kernel: every eigenvalue is `0` or
at least the gap. -/
theorem exists_hamiltonian_parentRingInteraction_gap_of_larger_range
    {d D R W : ℕ} (A : MPTensor α (Fin D)) (hR : 0 < R) (hRW : 2 * R ≤ W)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) =
      ((groundSpace A W).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ᶠ N : ℕ in atTop, ∀ [NeZero N],
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction A W N).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N],
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison A hker
  have hm : 0 < W - R + 1 := by omega
  have hmR : R ≤ W - R + 1 := by omega
  have hlength : (W - R + 1) + R - 1 = W := by omega
  refine ⟨κ * γ / (W - R + 1 : ℕ), div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr hm), ?_⟩
  filter_upwards [hGap, eventually_ge_atTop (2 * (W - R + 1))] with N hGapN hN _
  have hComparison := hamiltonian_parentRingInteraction_comparison_of_local_open_comparison A
    (κ := κ) (C := C) hR hmR hN (by rw [hlength]; exact hLower) (by rw [hlength]; exact hUpper)
  rw [hlength] at hComparison
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hComparison.1
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hComparison.2
  rw [map_smul, map_smul] at h1 h2
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentRingInteraction A _ _)).forall_hasEigenvalue_of_smul_le_of_le_smul
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentRingInteraction A _ _))
    hκ (Nat.cast_pos.mpr hm) hC hγ (by simpa only [Complex.ofReal_natCast] using h1)
    (by simpa only [Complex.ofReal_natCast] using h2) hGapN

end MPSTensor

end
