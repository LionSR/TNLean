/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFrameSupport
import TNLean.MPS.ParentHamiltonian.Martingale.SupportedParentProjection

/-!
# Reduction of the actual joint endpoint interaction by its boundary frame

The actual two-site support is contained in the product of the two joint
boundary polar-frame ranges. Consequently its orthogonal projector is
absorbed by the frame projection, the actual parent interaction is reduced
by that projection, and the interaction penalizes the entire complementary
physical sector with coefficient one.

Under simultaneous one-site spanning the rectangular frame is isometric.
Its compression of the actual interaction is then exactly the complementary
projection of the adjoint image of the actual support. Both boundary changes
act on this single two-site term, which is counted only once.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private def matrixLinearIsometry {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι κ ℂ) (hM : M.IsIsometry) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanLin M).isometryOfInner fun v w => by
    have hU : (Matrix.toEuclideanLin M).adjoint ∘ₗ Matrix.toEuclideanLin M =
        LinearMap.id := by
      calc
        _ = Matrix.toEuclideanLin Mᴴ ∘ₗ Matrix.toEuclideanLin M := by
          rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        _ = Matrix.toEuclideanLin (Mᴴ * M) := (Matrix.toLpLin_mul_same 2 Mᴴ M).symm
        _ = LinearMap.id := by
          rw [show Mᴴ * M = 1 from hM]
          exact Matrix.toLpLin_one 2
    calc
      _ = inner ℂ v ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M w)) :=
        (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin M) v _).symm
      _ = _ := congrArg (inner ℂ v) (LinearMap.congr_fun hU w)

/-- Orthogonal projection onto the full product of the actual joint
boundary frame ranges, without extending a rectangular frame to a unitary.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSiteFrameProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁)).range.starProjection.toLinearMap

/-- The full boundary frame fixes the actual extended support projection.
The inclusion is derived from the actual trace contraction.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSiteFrameProjection_mul_supportProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedTwoSiteFrameProjection A₀ A₁ *
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap =
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap :=
  Submodule.starProjection_comp_starProjection_eq_right_of_le
    (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁)

/-- The actual parent interaction is reduced by the full joint boundary
frame projection. No reducing-subspace premise is supplied.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSiteFrameProjection_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedTwoSiteFrameProjection A₀ A₁)
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap) :=
  Submodule.commute_starProjection_one_sub_starProjection_of_le
    (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁)

/-- The actual interaction is the identity on the entire physical
complement of the joint boundary frame.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedParentInteraction_apply_eq_self_of_orthogonal_frame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2))
    (hv : v ∈ (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁)).rangeᗮ) :
    (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)
        v = v :=
  Submodule.one_sub_starProjection_apply_of_mem_orthogonal_of_le
    (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁) hv

/-- The local complementary-frame penalty is bounded by the actual
interaction, with coefficient one and no injectivity assumption.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedTwoSiteFrameProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedTwoSiteFrameProjection A₀ A₁ ≤
      1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap :=
  Submodule.one_sub_starProjection_le_one_sub_starProjection_of_le
    (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁)

/-- The actual local energy controls the squared norm outside the full
boundary frame. The constant is independent of all physical dimensions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedParentInteraction_frameComplement_norm_sq_le
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)) :
    ‖v - jointMixedTwoSiteFrameProjection A₀ A₁ v‖ ^ 2 ≤
      (⟪(1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)
          v, v⟫_ℂ).re := by
  simpa only [Submodule.starProjection_orthogonal_val, jointMixedTwoSiteFrameProjection,
    ContinuousLinearMap.coe_coe] using
    Submodule.norm_sq_starProjection_orthogonal_le_re_inner_one_sub_of_le
      (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁) v

/-- The full product frame as a rectangular Hilbert-space isometry.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSitePolarIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ
      (JointMixedFirstBoundaryIndex D₀ D₁ × JointMixedLastBoundaryIndex D₀ D₁) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  matrixLinearIsometry _ (jointMixedTwoSitePolarFrame_isIsometry A₀ A₁ h₀ h₁)

/-- The frame projection is the product of the concrete rectangular
isometry and its adjoint, not an ambient identity.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSiteFrameProjection_eq_isometry_comp_adjoint
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    jointMixedTwoSiteFrameProjection A₀ A₁ =
      (jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁).toLinearMap ∘ₗ
        (jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁).toLinearMap.adjoint :=
  (jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁).starProjection_range_eq_comp_adjoint

/-- Compression of the actual two-site interaction has exactly the
orthogonally projected adjoint image of its actual support as kernel.
Both endpoints belong to this one term; no doubled edge sum occurs.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSitePolar_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    let U := jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁
    let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range
    U.compression (1 - S.starProjection.toLinearMap) =
      1 - (S.map U.toLinearMap.adjoint).starProjection.toLinearMap :=
  (jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁).compression_one_sub_starProjection_of_le_range _
      (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁)

/-- The actual compressed kernel is the adjoint image of the full joint
two-site support, with no kernel-identification hypothesis.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_jointMixedTwoSitePolar_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    let U := jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁
    let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      S.map U.toLinearMap.adjoint :=
  (jointMixedTwoSitePolarIsometry A₀ A₁ h₀ h₁).ker_compression_one_sub_starProjection_of_le_range _
      (range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁)

end

end MPSTensor.MPOSymmetry
