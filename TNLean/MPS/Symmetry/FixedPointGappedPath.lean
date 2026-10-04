/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.TwoSiteBondInteraction
import TNLean.MPS.Symmetry.BondProductContinuity
import TNLean.Algebra.MatrixProjectionReindex

/-!
# A symmetric gapped path for the direct-sum fixed points

The normalized bond interpolation of arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, gives bounded two-site interactions with a uniform
spectral gap. This constructs a path on the common physical space of the
direct-sum virtual representation. Identifying arbitrary injective parent
Hamiltonians with these endpoints requires the separate polar-deformation
and embedding arguments.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- The two-site parent interaction of the normalized direct-sum bond.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def normalizedBondInteraction (D₀ D₁ : ℕ) (γ : ℝ) :
    MPOTensor.ChainOperator ((D₀ + D₁) * (D₀ + D₁)) 2 :=
  twoSiteBondInteraction (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
    (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)))

/-- The normalized bond interaction is an orthogonal projection, including
both endpoints. Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedBondInteraction_isStarProjection {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    IsStarProjection (normalizedBondInteraction D₀ D₁ γ) := by
  apply twoSiteBondInteraction_isStarProjection
  have h := bondPenalty_isStarProjection _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)
  exact Matrix.isStarProjection_reindex finProdFinEquiv.symm _ h

/-- The normalized two-site interaction depends continuously on the
parameter. Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem continuous_normalizedBondInteraction {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (normalizedBondInteraction D₀ D₁) := by
  apply continuous_matrix
  intro s t
  simp only [normalizedBondInteraction, twoSiteBondInteraction_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_const.mul ((continuous_apply _).comp
    ((continuous_apply _).comp ((continuous_bondPenalty _).comp
      (continuous_normalizedBondInterpolationVector h₀ h₁))))).mul continuous_const

end MPSTensor
