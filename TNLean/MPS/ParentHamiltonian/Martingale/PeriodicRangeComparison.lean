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

**Transitional (#10948).** `localTermES_self_zero_eq_parentInteractionES` and
`parentHamiltonianES_comparison_of_local_open_comparison` (stated for the Euclidean-space
operators) are kept until their last users are converted; the last section states them for the
Hamiltonians of the parent interactions.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

private theorem sum_cyclicWindowSum_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {N : ℕ} [NeZero N]
    (h : ZMod N → E →ₗ[ℂ] E) (m : ℕ) :
    (∑ s : ZMod N, ProjectionGeometry.cyclicWindowSum h m s) =
      m • ∑ s : ZMod N, h s := by
  simp only [ProjectionGeometry.cyclicWindowSum]
  rw [Finset.sum_comm]
  simp only [ZModCyclicSums.sum_comp_addRight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]

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

/-- Two-sided comparison on one open interval implies two-sided comparison of
periodic parent Hamiltonians. Each range-\(R\) term occurs in exactly \(m\)
translated windows of active length \(m+R-1\). This is the finite-range
comparison used in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`. -/
theorem parentHamiltonianES_comparison_of_local_open_comparison
    (A : MPSTensor d D) {R m N : ℕ} [NeZero N]
    (hR : 1 ≤ R) (hmR : R ≤ m) (hN : 2 * m ≤ N) {κ C : ℝ}
    (hLower : (κ : ℂ) • parentInteractionES A (m + R - 1) ≤
      openParentHamiltonianES A R (m + R - 1))
    (hUpper : openParentHamiltonianES A R (m + R - 1) ≤
      (C : ℂ) • parentInteractionES A (m + R - 1)) :
    (κ : ℂ) • parentHamiltonianES A (m + R - 1) N ≤
        (m : ℂ) • parentHamiltonianES A R N ∧
      (m : ℂ) • parentHamiltonianES A R N ≤
        (C : ℂ) • parentHamiltonianES A (m + R - 1) N := by
  have hW : 0 < m + R - 1 := by omega
  have hWindow (s : ZMod N) :
      (κ : ℂ) • zmodLocalTermES A (m + R - 1) s ≤
          ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s ∧
        ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s ≤
          (C : ℂ) • zmodLocalTermES A (m + R - 1) s := by
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d (m + R - 1)
      (by omega) ((ZMod.finEquiv N).symm s)
    -- Caching this instance is load-bearing: without it, synthesizing
    -- `ContinuousSMul ℂ` on this Euclidean space times out in the statements below.
    let : T2Space (EuclideanSpace ℂ (Cfg d (m + R - 1))) := inferInstance
    have hShort : U.toLinearEquiv.conj
        (ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s) =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap
            (openParentHamiltonianES A R (m + R - 1)))).toLinearMap := by
      simpa only [U, LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
        cyclicWindowSum_zmodLocalTermES_conj_cyclicActiveBlock A hR hmR hN s
    have hLong : U.toLinearEquiv.conj (zmodLocalTermES A (m + R - 1) s) =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap (parentInteractionES A (m + R - 1)))).toLinearMap := by
      simpa only [U, zmodLocalTermES, Fin.val_mk, cyclicForwardSite_zero,
        localTermES_self_zero_eq_parentInteractionES A hW,
        LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
        (localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv A
          (R := m + R - 1) (by omega : m + R - 1 ≤ N)
          ((ZMod.finEquiv N).symm s) ⟨0, hW⟩ (by simp))
    have hmono {G H : EuclideanSpace ℂ (Cfg d (m + R - 1)) →ₗ[ℂ]
        EuclideanSpace ℂ (Cfg d (m + R - 1))} (h : G ≤ H) :
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap G)).toLinearMap ≤
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1)))
          (LinearMap.toContinuousLinearMap H)).toLinearMap :=
      ContinuousLinearMap.rightFiberwiseMap_mono h
    refine ⟨(U.conj_le_conj_iff _ _).mp ?_, (U.conj_le_conj_iff _ _).mp ?_⟩
    · have h := hmono hLower
      rw [map_smul, ContinuousLinearMap.rightFiberwiseMap_smul,
        ContinuousLinearMap.toLinearMap_smul] at h
      rwa [map_smul, hLong, hShort]
    · have h := hmono hUpper
      rw [map_smul, ContinuousLinearMap.rightFiberwiseMap_smul,
        ContinuousLinearMap.toLinearMap_smul] at h
      rwa [map_smul, hLong, hShort]
  constructor
  · simpa only [← Finset.smul_sum, sum_cyclicWindowSum_eq,
      sum_zmodLocalTermES_eq_parentHamiltonianES, Nat.cast_smul_eq_nsmul] using
      (Finset.sum_le_sum fun (s : ZMod N) (_ : s ∈ Finset.univ) ↦ (hWindow s).1)
  · simpa only [← Finset.smul_sum, sum_cyclicWindowSum_eq,
      sum_zmodLocalTermES_eq_parentHamiltonianES, Nat.cast_smul_eq_nsmul] using
      (Finset.sum_le_sum fun (s : ZMod N) (_ : s ∈ Finset.univ) ↦ (hWindow s).2)

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
    (parentRingInteraction A (le_refl W)).term ⟨0, hW⟩ =
      LinearMap.toMatrix' (parentInteraction A W) := by
  rw [ManyBody.Interaction.translates_term]
  have hw : ManyBody.ringWindow (le_refl W) (⟨0, hW⟩ : Fin W) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun j ↦ Fin.ext (by
      simp [ManyBody.ringWindow_apply, Fin.val_add, Nat.mod_eq_of_lt j.isLt])
  rw [hw, ManyBody.placeAlong_refl]

private theorem placeAlong_ringWindow_hamiltonian_parentChainInteraction (A : MPSTensor d D)
    {R W N : ℕ} [NeZero N] (hRW : R ≤ W) (hWN : W ≤ N) (i : Fin N) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hWN i)
        (parentChainInteraction A R W).hamiltonian =
      ∑ j : Fin (W + 1 - R),
        (parentRingInteraction A (hRW.trans hWN)).term (i + (j.val : Fin N)) := by
  rw [ManyBody.Interaction.hamiltonian, ManyBody.placeAlong_sum]
  refine Fintype.sum_congr _ _ fun j ↦ ?_
  rw [ManyBody.Interaction.translates_term, ManyBody.placeAlong_placeAlong,
    ManyBody.chainWindow_trans_ringWindow]
  rfl

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
    (κ : ℂ) • (parentRingInteraction A (show m + R - 1 ≤ N by omega)).hamiltonian ≤
        (m : ℂ) • (parentRingInteraction A (show R ≤ N by omega)).hamiltonian ∧
      (m : ℂ) • (parentRingInteraction A (show R ≤ N by omega)).hamiltonian ≤
        (C : ℂ) • (parentRingInteraction A (show m + R - 1 ≤ N by omega)).hamiltonian := by
  have hRW : R ≤ m + R - 1 := by omega
  have hWN : m + R - 1 ≤ N := by omega
  have hsum : ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hWN i)
      (parentChainInteraction A R (m + R - 1)).hamiltonian =
      (m : ℂ) • (parentRingInteraction A (hRW.trans hWN)).hamiltonian := by
    simp only [placeAlong_ringWindow_hamiltonian_parentChainInteraction A hRW hWN]
    rw [Finset.sum_comm]
    have hshift (j : Fin (m + R - 1 + 1 - R)) :
        ∑ i : Fin N, (parentRingInteraction A (hRW.trans hWN)).term (i + (j.val : Fin N)) =
          (parentRingInteraction A (hRW.trans hWN)).hamiltonian :=
      Fintype.sum_equiv (Equiv.addRight (j.val : Fin N)) _ _ fun _ ↦ rfl
    simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      show m + R - 1 + 1 - R = m by omega, Nat.cast_smul_eq_nsmul]
  have hring (W : ℕ) (hW : W ≤ N) (c : ℂ) : c • (parentRingInteraction A hW).hamiltonian =
      ∑ i : Fin N, ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hW i)
        (c • LinearMap.toMatrix' (parentInteraction A W)) := by
    simp only [ManyBody.Interaction.hamiltonian, ManyBody.Interaction.translates_term,
      ManyBody.placeAlong_smul, Finset.smul_sum]
  constructor
  · rw [hring _ hWN, ← hsum]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hLower
  · rw [hring _ hWN, ← hsum]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hUpper

end Interaction

end MPSTensor
