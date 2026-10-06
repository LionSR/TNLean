/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointProjectorComparison

/-! Regression tests for the first-endpoint comparison. The local statements
must not require injectivity, a fixed-point form, or a gap hypothesis. -/

open MPSTensor MPSTensor.MPOSymmetry
open scoped ComplexOrder

variable {D₀ D₁ : ℕ}
variable (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)

example :
    (groundSpaceES (mixedEndpointLeftTensor A₀ D₁) 2).starProjection.toLinearMap =
      mixedEndpointRowSector D₀ D₁ 0 * mixedEndpointColumnSector D₀ D₁ 1 *
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
          (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap :=
  mixedEndpointLeftTensor_starProjection_eq_outerCorner A₀ A₁

example :
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap ≤
      parentInteractionES (mixedEndpointLeftTensor A₀ D₁) 2 :=
  mixedEndpointParentInteraction_zero_le_parentInteractionES A₀ A₁

example :
    parentInteractionES (mixedEndpointLeftTensor A₀ D₁) 2 ≤
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap +
        (1 - mixedEndpointRowSector D₀ D₁ 0) +
        (1 - mixedEndpointColumnSector D₀ D₁ 1) :=
  parentInteractionES_mixedEndpointLeftTensor_le A₀ A₁

example : 1 - mixedEndpointColumnSector D₀ D₁ 0 ≤
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁

example : 1 - mixedEndpointRowSector D₀ D₁ 1 ≤
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  mixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁

example (γ : ℝ) : (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap.IsPositive :=
  mixedEndpointParentInteraction_isPositive A₀ A₁ γ
