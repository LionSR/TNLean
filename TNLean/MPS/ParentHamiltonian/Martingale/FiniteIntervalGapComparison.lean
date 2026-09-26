/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PositiveGapTransfer
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-interval comparison with the parent projection

If the kernel of an open parent Hamiltonian is the full local MPS space,
finite dimensionality bounds its excitation projection by a positive multiple
of that Hamiltonian. This is the local comparison needed to transfer a
parent-Hamiltonian gap between admissible interaction ranges; see
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

open scoped InnerProductSpace ComplexOrder

private theorem exists_pos_norm_gap_on_orthogonal_ker
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (H : E →ₗ[ℂ] E) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  have hker : (H.domRestrict (LinearMap.ker H)ᗮ).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (LinearMap.injective_domRestrict_iff.mpr (LinearMap.ker H).orthogonal_disjoint.symm)
  obtain ⟨K, hK, hBound⟩ :=
    (H.domRestrict (LinearMap.ker H)ᗮ).exists_antilipschitzWith hker
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr (NNReal.coe_pos.mpr hK), fun v hv ↦ ?_⟩
  exact (inv_mul_le_iff₀ (NNReal.coe_pos.mpr hK)).mpr
    (ZeroHomClass.bound_of_antilipschitz (H.domRestrict (LinearMap.ker H)ᗮ)
      hBound ⟨v, hv⟩)

private theorem inner_eq_inner_orthogonal_ker_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive) (v : E) :
    ⟪H v, v⟫_ℂ =
      ⟪H ((LinearMap.ker H)ᗮ.starProjection v),
        (LinearMap.ker H)ᗮ.starProjection v⟫_ℂ := by
  have hproj : H ((LinearMap.ker H).starProjection v) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  simp only [Submodule.starProjection_orthogonal_val, map_sub, sub_zero,
    hH.isSymmetric v, hproj, sub_zero]

namespace LinearMap.IsPositive

/-- A positive operator on a finite-dimensional Hilbert space dominates a
positive multiple of the orthogonal projection onto its kernel complement. -/
theorem exists_pos_smul_orthogonal_ker_projection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive) :
    ∃ γ : ℝ, 0 < γ ∧
      (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H := by
  obtain ⟨γ, hγ, hGap⟩ := exists_pos_norm_gap_on_orthogonal_ker H
  refine ⟨γ, hγ, hH.isSymmetric.sub
    ((LinearMap.ker H)ᗮ.starProjection_isSymmetric.smul (by simp)), ?_⟩
  intro v
  have h := hH.re_inner_ge_of_norm_gap hγ.le hGap
    ((LinearMap.ker H)ᗮ.starProjection v) (Submodule.starProjection_apply_mem _ _)
  have hnorm : (⟪(LinearMap.ker H)ᗮ.starProjection v, v⟫_ℂ).re =
      ‖(LinearMap.ker H)ᗮ.starProjection v‖ ^ 2 :=
    (Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ) (LinearMap.ker H)ᗮ v)
  change 0 ≤ (⟪H v - (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection v, v⟫_ℂ).re
  simpa only [inner_sub_left, inner_smul_left, Complex.sub_re,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    hnorm,
    inner_eq_inner_orthogonal_ker_projection hH v, sub_nonneg] using h

/-- A positive operator is bounded above by a positive multiple of the
orthogonal projection onto its kernel complement. -/
theorem exists_pos_le_smul_orthogonal_ker_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive) :
    ∃ C : ℝ, 0 < C ∧
      H ≤ (C : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap := by
  let C : ℝ := ‖H.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC,
    ((LinearMap.ker H)ᗮ.starProjection_isSymmetric.smul (by simp)).sub hH.isSymmetric,
    ?_⟩
  intro v
  let w := (LinearMap.ker H)ᗮ.starProjection v
  have hbound : (⟪H w, w⟫_ℂ).re ≤ C * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖H w‖ * ‖w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ (‖H.toContinuousLinearMap‖ * ‖w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (H.toContinuousLinearMap.le_opNorm w) (norm_nonneg _)
      _ ≤ C * ‖w‖ ^ 2 := by dsimp [C]; nlinarith [sq_nonneg ‖w‖]
  have hnorm : (⟪(LinearMap.ker H)ᗮ.starProjection v, v⟫_ℂ).re =
      ‖(LinearMap.ker H)ᗮ.starProjection v‖ ^ 2 :=
    Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ) (LinearMap.ker H)ᗮ v
  change 0 ≤ (⟪(C : ℂ) • (LinearMap.ker H)ᗮ.starProjection v - H v, v⟫_ℂ).re
  simpa only [inner_sub_left, inner_smul_left, Complex.sub_re,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hnorm,
    inner_eq_inner_orthogonal_ker_projection hH v, sub_nonneg] using hbound

end LinearMap.IsPositive

namespace MPSTensor

/-- If the open-chain kernel equals the local MPS space, its Hamiltonian and
its parent projection bound one another by positive constants. -/
theorem exists_pos_parentInteractionES_openParentHamiltonianES_comparison
    {d D R W : ℕ} (A : MPSTensor d D)
    (hker : LinearMap.ker (openParentHamiltonianES A R W) = groundSpaceES A W) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • parentInteractionES A W ≤ openParentHamiltonianES A R W ∧
      openParentHamiltonianES A R W ≤ (C : ℂ) • parentInteractionES A W := by
  obtain ⟨κ, hκ, hLower⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (openParentHamiltonianES_isPositive A R W)
  obtain ⟨C, hC, hUpper⟩ :=
    LinearMap.IsPositive.exists_pos_le_smul_orthogonal_ker_projection
      (openParentHamiltonianES_isPositive A R W)
  exact ⟨κ, C, hκ, hC, by simpa only [hker, parentInteractionES] using hLower,
    by simpa only [hker, parentInteractionES] using hUpper⟩

end MPSTensor
