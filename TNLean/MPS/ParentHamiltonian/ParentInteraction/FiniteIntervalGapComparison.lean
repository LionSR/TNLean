/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
import QICLean.Spectral.Gap.OrthogonalKernelGap
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TNLean.MPS.ParentHamiltonian.ParentInteraction.PhysicalDeformation

/-!
# Finite-interval comparison with the parent projection

If the kernel of an open parent Hamiltonian is the full local MPS space,
finite dimensionality bounds its excitation projection by a positive multiple
of that Hamiltonian. This is the local comparison needed to transfer a
parent-Hamiltonian gap between admissible interaction ranges; see
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.

The comparison is stated for the Hamiltonian of the parent interaction on the open chain
(`parentChainInteraction`) and the matrix of the local parent interaction.

## Comparison of parent interactions with the canonical projection

A positive local interaction with the prescribed MPS kernel bounds, and is
bounded by, positive multiples of the canonical parent projection. The constants
depend only on the local interaction. This finite-dimensional comparison is the
local step in extending the parent-Hamiltonian gap to arbitrary fixed parent
interactions, as defined in CPGSV21, arXiv:2011.12127, lines 1996--1999. It is
the remark at line 2170 that non-projector interactions are bounded above and
below by projectors up to a constant, which reduces the gap theorem at lines
2183--2187 to the canonical projection interaction.
-/

section

open scoped InnerProductSpace ComplexOrder

private theorem inner_eq_inner_orthogonal_ker_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive) (v : E) :
    ⟪H v, v⟫_ℂ =
      ⟪H ((LinearMap.ker H)ᗮ.starProjection v),
        (LinearMap.ker H)ᗮ.starProjection v⟫_ℂ := by
  have hproj : H ((LinearMap.ker H).starProjection v) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  simp only [Submodule.starProjection_orthogonal_val, map_sub, sub_zero,
    hH.isSymmetric v, hproj]

namespace LinearMap.IsPositive

/-- A norm gap of a positive operator gives a lower order bound by the
orthogonal projection onto its kernel complement. -/
theorem smul_orthogonal_ker_projection_le_of_norm_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖) :
    (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H := by
  refine ⟨hH.isSymmetric.sub
    ((LinearMap.ker H)ᗮ.starProjection_isSymmetric.smul (by simp)), ?_⟩
  intro v
  have h := hH.re_inner_ge_of_norm_gap hγ hGap
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

/-- A gap `γ ≥ 0` above the kernel of a positive operator, every eigenvalue other than `0` being
at least `γ`, gives a lower order bound by the orthogonal projection onto its kernel
complement. -/
theorem smul_orthogonal_ker_projection_le_of_forall_hasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H :=
  hH.smul_orthogonal_ker_projection_le_of_norm_gap hγ (hH.forall_hasEigenvalue_iff_norm.mp hGap)

/-- A positive operator on a finite-dimensional Hilbert space dominates a
positive multiple of the orthogonal projection onto its kernel complement. -/
theorem exists_pos_smul_orthogonal_ker_projection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} (hH : H.IsPositive) :
    ∃ γ : ℝ, 0 < γ ∧
      (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H := by
  obtain ⟨γ, hγ, hGap⟩ := H.exists_pos_mul_norm_le_of_mem_orthogonal_ker
  exact ⟨γ, hγ, hH.smul_orthogonal_ker_projection_le_of_norm_gap hγ.le hGap⟩

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

/-! ### The Hamiltonian of the parent interaction on the open chain -/

section ChainInteraction

open scoped MatrixOrder

/-- If the kernel of the operator of the Hamiltonian of the parent interaction on the open chain
is the local MPS space, that Hamiltonian and the local parent interaction bound one another, in
the Loewner order, by positive constants. -/
theorem exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison
    {d D R W : ℕ} (A : MPSTensor d D)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) =
      groundSpaceES A W) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A W) ≤
        (parentChainInteraction A R W).hamiltonian ∧
      (parentChainInteraction A R W).hamiltonian ≤
        (C : ℂ) • LinearMap.toMatrix' (parentInteraction A W) := by
  have hH := Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentChainInteraction A R W)
  obtain ⟨κ, hκ, hLower⟩ := LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le hH
  obtain ⟨C, hC, hUpper⟩ := LinearMap.IsPositive.exists_pos_le_smul_orthogonal_ker_projection hH
  rw [hker, ← toEuclideanLin_toMatrix'_parentInteraction, ← map_smul] at hLower hUpper
  exact ⟨κ, C, hκ, hC, Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp hLower,
    Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp hUpper⟩

end ChainInteraction

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

/-- Every positive parent interaction is comparable in both directions to the operator of the
matrix of the canonical parent interaction. The constants are strictly positive, including
when both operators vanish.

Source: CPGSV21, arXiv:2011.12127, lines 1996--1999 and line 2170. -/
theorem IsParentInteraction.exists_pos_comparison_toEuclideanLin_toMatrix'_parentInteraction
    {d D R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A R)) ≤ h ∧
      h ≤ (C : ℂ) • Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A R)) := by
  obtain ⟨κ, hκ, hLower⟩ :=
    hh.isPositive.exists_pos_smul_orthogonal_ker_projection_le
  obtain ⟨C, hC, hUpper⟩ :=
    hh.isPositive.exists_pos_le_smul_orthogonal_ker_projection
  rw [toEuclideanLin_toMatrix'_parentInteraction]
  exact ⟨κ, C, hκ, hC, by simpa only [hh.ker_eq] using hLower,
    by simpa only [hh.ker_eq] using hUpper⟩

end MPSTensor

end
