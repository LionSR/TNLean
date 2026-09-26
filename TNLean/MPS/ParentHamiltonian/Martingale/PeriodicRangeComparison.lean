/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorOrder

/-!
# Periodic comparison from a finite open interval

A comparison between a parent projector and a shorter-range open Hamiltonian
can be translated around a periodic chain. Summing the translated inequalities
counts each shorter-range interaction once for every position within the open
window. This gives an operator comparison between the periodic Hamiltonians.
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
    refine ⟨(U.conj_le_conj_iff _ _).mp ?_, (U.conj_le_conj_iff _ _).mp ?_⟩
    · simpa only [map_smul, hLong, hShort, ContinuousLinearMap.rightFiberwiseMap_smul,
        ContinuousLinearMap.toLinearMap_smul] using!
        (ContinuousLinearMap.rightFiberwiseMap_mono (S := Cfg d (N - (m + R - 1)))
          (G := LinearMap.toContinuousLinearMap
            ((κ : ℂ) • parentInteractionES A (m + R - 1)))
          (H := LinearMap.toContinuousLinearMap (openParentHamiltonianES A R (m + R - 1)))
          hLower)
    · simpa only [map_smul, hLong, hShort, ContinuousLinearMap.rightFiberwiseMap_smul,
        ContinuousLinearMap.toLinearMap_smul] using!
        (ContinuousLinearMap.rightFiberwiseMap_mono (S := Cfg d (N - (m + R - 1)))
          (G := LinearMap.toContinuousLinearMap (openParentHamiltonianES A R (m + R - 1)))
          (H := LinearMap.toContinuousLinearMap
            ((C : ℂ) • parentInteractionES A (m + R - 1)))
          hUpper)
  constructor
  · simpa only [← Finset.smul_sum, sum_cyclicWindowSum_eq,
      sum_zmodLocalTermES_eq_parentHamiltonianES, Nat.cast_smul_eq_nsmul] using
      (Finset.sum_le_sum fun (s : ZMod N) (_ : s ∈ Finset.univ) ↦ (hWindow s).1)
  · simpa only [← Finset.smul_sum, sum_cyclicWindowSum_eq,
      sum_zmodLocalTermES_eq_parentHamiltonianES, Nat.cast_smul_eq_nsmul] using
      (Finset.sum_le_sum fun (s : ZMod N) (_ : s ∈ Finset.univ) ↦ (hWindow s).2)

end MPSTensor
