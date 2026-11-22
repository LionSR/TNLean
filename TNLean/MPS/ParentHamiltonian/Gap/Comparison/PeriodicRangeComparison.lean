/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
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
-/

section

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

end MPSTensor

end

section

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

end
