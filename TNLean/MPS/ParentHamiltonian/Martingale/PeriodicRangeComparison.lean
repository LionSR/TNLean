/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import QICLean.Analysis.EuclideanFiberwiseMap

/-!
# Periodic comparison from a finite open interval

A comparison between a parent projector and a shorter-range open Hamiltonian
can be translated around a periodic chain. Summing the translated inequalities
counts each shorter-range interaction once for every position within the open
window. This gives an operator comparison between the periodic Hamiltonians.

**Transitional (#10948).** `localTermES_self_zero_eq_parentInteractionES` (stated for the
Euclidean-space operators) is kept until its last user is converted.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The full-length interaction starting at zero is the canonical parent
projection on that interval. -/
theorem localTermES_self_zero_eq_parentInteractionES (A : MPSTensor d D)
    {W : ℕ} (hW : 0 < W) :
    localTermES A W (⟨0, hW⟩ : Fin W) = parentInteractionES A W := by
  have hcfg (ω σ : Cfg d W) :
      cyclicCfg hW W (⟨0, hW⟩ : Fin W) ω σ = ω :=
    funext fun k ↦ by simp [cyclicCfg, Nat.mod_eq_of_lt k.isLt]
  have hext (σ : Cfg d W) : extractWindow W (⟨0, hW⟩ : Fin W) σ = σ :=
    funext fun k ↦ by simp [extractWindow, Nat.mod_eq_of_lt k.isLt]
  have hr (σ : Cfg d W) : cyclicRestrictES hW W (⟨0, hW⟩ : Fin W) σ =
      (LinearMap.id : EuclideanSpace ℂ (Cfg d W) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d W)) :=
    LinearMap.ext fun v ↦ PiLp.ext fun ω ↦ congrArg v (hcfg ω σ)
  exact LinearMap.ext fun v ↦ PiLp.ext fun σ ↦ by
    simpa only [hr, hext, LinearMap.id_apply] using
      localTermES_apply A W (⟨0, hW⟩ : Fin W) le_rfl v σ

/-! ### The comparison for the Hamiltonians of the parent interactions

The same comparison for the Hamiltonians of the parent interactions on the ring
(`parentRingInteraction`) and on the open interval (`parentChainInteraction`), in the matrix
order. -/

section Interaction

open scoped MatrixOrder
open Fin.CommRing

/-- The term with index `0` of the parent interaction on the ring of `W` sites is the local
parent interaction: its window is the whole ring. -/
theorem parentRingInteraction_term_zero_self (A : MPSTensor d D) {W : ℕ} (hW : 0 < W) :
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
    (A : MPSTensor d D) {R m N : ℕ} [NeZero N]
    (hR : 1 ≤ R) (hmR : R ≤ m) (hN : 2 * m ≤ N) {κ C : ℝ}
    (hLower : (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A (m + R - 1)) ≤
      (parentChainInteraction A R (m + R - 1)).hamiltonian)
    (hUpper : (parentChainInteraction A R (m + R - 1)).hamiltonian ≤
      (C : ℂ) • LinearMap.toMatrix' (parentInteraction A (m + R - 1))) :
    (κ : ℂ) • (parentRingInteraction A (m + R - 1) N).hamiltonian ≤
        (m : ℂ) • (parentRingInteraction A R N).hamiltonian ∧
      (m : ℂ) • (parentRingInteraction A R N).hamiltonian ≤
        (C : ℂ) • (parentRingInteraction A (m + R - 1) N).hamiltonian := by
  have hWN : m + R - 1 ≤ N := by omega
  have hsum : ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hWN i)
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
      ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hW i)
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
