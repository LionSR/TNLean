/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointReducingSectors

/-!
# Local comparison of the joint endpoint interactions

The extended interaction lies below the joint canonical interaction. Their
difference is bounded by the two outer phase penalties; the two inner
phase penalties are each bounded by the extended interaction. All these
inequalities follow from the actual boundary-map support.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The full joint canonical support is contained in the actual extended
support at the first endpoint. Source: arXiv:2203.12563, Section 5,
lines 1695–1777. -/
theorem groundSpaceES_jointMixedEndpointLeftTensor_le_extendedSupport
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    groundSpaceES (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 ≤
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range := by
  rw [← jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES A₀ A₁]
  rintro _ ⟨v, hv, rfl⟩
  apply range_blockInsertedBoundaryMap_jointMixed_invariant_rowSector A₀ A₁ _
  refine ⟨_, ?_, rfl⟩
  exact range_blockInsertedBoundaryMap_jointMixed_invariant_columnSector A₀ A₁ _
    ⟨v, hv, rfl⟩

/-- The extended endpoint term lies below the common canonical parent
term; no separate block gaps or orthogonality are used.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpointParentInteraction_zero_le_parentInteractionES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap ≤
      parentInteractionES (toTensorFromBlocks (μ := fun _ => 1)
        (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 := by
  have hle : (groundSpaceES (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2).starProjection.toLinearMap ≤
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap := by
    apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
      (Submodule.isSymmetricProjection_starProjection _) |>.mpr
    simpa only [Submodule.range_starProjection] using
      groundSpaceES_jointMixedEndpointLeftTensor_le_extendedSupport A₀ A₁
  simpa only [jointMixedEndpointParentInteraction, parentInteractionES,
    Submodule.starProjection_orthogonal', ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one] using sub_le_sub_left hle 1

/-- The common canonical term differs from the extended term by at most
the two outer phase penalties. Source: arXiv:2203.12563, Section 5,
lines 1695–1777. -/
theorem parentInteractionES_jointMixedEndpointLeftTensor_le
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    parentInteractionES (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap +
        (1 - jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)) +
        (1 - jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)) := by
  let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range
  have hupper := (Submodule.isSymmetricProjection_starProjection S).one_sub_mul_mul_le
    (jointMixedRowSector_isSymmetricProjection (d₀ := d₀) (d₁ := d₁)
      (D₀ := D₀) (D₁ := D₁) (0 : Fin 2))
    (jointMixedColumnSector_isSymmetricProjection (d₀ := d₀) (d₁ := d₁)
      (D₀ := D₀) (D₁ := D₁) (1 : Fin 2))
    (jointMixedRowSector_commute_columnSector (d₀ := d₀) (d₁ := d₁)
      (D₀ := D₀) (D₁ := D₁) (0 : Fin 2) 1)
    (jointMixedRowSector_commute_extendedSupport_starProjection A₀ A₁ 0)
    (jointMixedColumnSector_commute_extendedSupport_starProjection A₀ A₁ 1)
  simpa only [parentInteractionES, Submodule.starProjection_orthogonal',
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one,
    jointMixedEndpointLeftTensor_starProjection_eq_outerCorner A₀ A₁,
    jointMixedEndpointParentInteraction] using hupper

private theorem extendedSupport_starProjection_le_sector
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (Q : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2))
    (hQ : Q.IsSymmetricProjection)
    (hfix : ∀ X, Q (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 (blockBoundaryEquiv.symm X)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap ≤
        Q := by
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range hQ |>.mpr
  rw [Submodule.range_starProjection]
  rintro _ ⟨v, rfl⟩
  obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
  exact ⟨_, hfix X⟩

/-- The first-column phase penalty is supplied by the actual extended
interaction. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_one_sub_columnSector_zero_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2) ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (jointMixedColumnSector_isSymmetricProjection 0)
    (jointMixedColumnSector_zero_blockInsertedBoundaryMap A₀ A₁)) 1

/-- The second-row phase penalty is supplied by the actual extended
interaction. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_one_sub_rowSector_one_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2) ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap :=
  sub_le_sub_left (extendedSupport_starProjection_le_sector A₀ A₁ _
    (jointMixedRowSector_isSymmetricProjection 1)
    (jointMixedRowSector_one_blockInsertedBoundaryMap A₀ A₁)) 1

end MPSTensor.MPOSymmetry
