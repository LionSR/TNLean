/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison

/-!
# Comparison of parent interactions with the canonical projection

A positive local interaction with the prescribed MPS kernel bounds, and is
bounded by, positive multiples of the canonical parent projection. The constants
depend only on the local interaction. This finite-dimensional comparison is the
local step in extending the parent-Hamiltonian gap to arbitrary fixed parent
interactions, as defined in CPGSV21, arXiv:2011.12127, lines 1996--1999 and used
in its gap theorem at lines 2183--2187.
-/

open scoped ComplexOrder

namespace MPSTensor

/-- Every positive parent interaction is comparable in both directions to the
canonical parent projection. The constants are strictly positive, including
when both operators vanish.

Source: CPGSV21, arXiv:2011.12127, lines 1996--1999 and 2183--2187. -/
theorem IsParentInteraction.exists_pos_comparison
    {d D R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • parentInteractionES A R ≤ h ∧
      h ≤ (C : ℂ) • parentInteractionES A R := by
  obtain ⟨κ, hκ, hLower⟩ :=
    hh.isPositive.exists_pos_smul_orthogonal_ker_projection_le
  obtain ⟨C, hC, hUpper⟩ :=
    hh.isPositive.exists_pos_le_smul_orthogonal_ker_projection
  exact ⟨κ, C, hκ, hC,
    by simpa only [hh.ker_eq, parentInteractionES] using hLower,
    by simpa only [hh.ker_eq, parentInteractionES] using hUpper⟩

end MPSTensor
