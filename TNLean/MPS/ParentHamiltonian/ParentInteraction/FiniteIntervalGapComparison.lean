/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
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
