/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointPhysicalCrop

/-!
# Actual joint edge compression to the normalized boundary coordinates

The first edge is restricted by the joint left polar frame and the full
shared physical alphabet at its neighboring site. The last edge uses the
reflected restriction. Their compressed interactions are exactly the
orthogonal-complement projections of the coefficient supports normalized
in `JointMixedEndpointEdgeProjectors`.

The proof first uses the actual phase reduction, then the actual boundary
factorization. It assumes neither the compressed kernel nor containment
of the uncropped support in the physical-00 sector. Interior letters are
unchanged, all cross-label Gram terms remain present, and dimensions may
vanish. These are individual local identities: the two-site chain has one
edge, handled by the full two-boundary frame theorem.

Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1695–1777.
-/

open scoped Matrix Kronecker

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private def edgeMatrixIsometry {ι κ : Type*} [Fintype ι] [Fintype κ]
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

/-- The first polar frame acts only on the boundary coordinate, with the
identity on the neighboring shared physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgePolarIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀) :=
  edgeMatrixIsometry
    (Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
      (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) (by
        change (_ ⊗ₖ _)ᴴ * (_ ⊗ₖ _) = 1
        rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
          Matrix.isIsometry_polarIso_of_injective _
            (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁),
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one])

/-- The reflected last polar frame leaves the adjacent physical site
unchanged, including unused first-alphabet directions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgePolarIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :=
  edgeMatrixIsometry
    ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
      Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)) (by
        change (_ ⊗ₖ _)ᴴ * (_ ⊗ₖ _) = 1
        rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
          Matrix.isIsometry_polarIso_of_injective _
            (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁),
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one])

/-- The first cropped support lies in the actual polar frame range.
This follows from the trace-derived coefficient factorization.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgeCroppedSupport_le_polarRange
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    jointMixedFirstEdgeCroppedSupportES A₀ A₁ ≤
      (jointMixedFirstEdgePolarIsometry A₀ A₁ h₀ h₁).toLinearMap.range := by
  rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
  refine ⟨(WithLp.linearEquiv 2 ℂ _).symm
    ((Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
      (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) *ᵥ
        jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix (Fin.castAdd (D₁ x)) id)), ?_⟩
  apply PiLp.ext
  intro i
  change ((Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
    (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) *ᵥ _) i = jointMixedFirstEdgeBoundaryMap A₀ A₁ X i
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.polarIso_mul_polarPos, jointMixedFirstEdgeBoundaryMap_eq_columns_core]

/-- The reflected cropped support lies in the right polar frame range.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgeCroppedSupport_le_polarRange
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    jointMixedLastEdgeCroppedSupportES A₀ A₁ ≤
      (jointMixedLastEdgePolarIsometry A₀ A₁ h₀ h₁).toLinearMap.range := by
  rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
  refine ⟨(WithLp.linearEquiv 2 ℂ _).symm
    (((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
      Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)) *ᵥ
        jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix id (Fin.castAdd (D₁ x)))), ?_⟩
  apply PiLp.ext
  intro i
  change (((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
    Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)) *ᵥ _) i =
      jointMixedLastEdgeBoundaryMap A₀ A₁ X i
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.polarIso_mul_polarPos, jointMixedLastEdgeBoundaryMap_eq_columns_core]

private theorem map_euclidean_range_mulVec
    {B ι κ : Type*} [AddCommGroup B] [Module ℂ B]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (f : B →ₗ[ℂ] (ι → ℂ)) :
    (f.range.map (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap).map
        (Matrix.toEuclideanLin M) =
      (M.mulVecLin.comp f).range.map
        (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm.toLinearMap := by
  ext v
  constructor
  · rintro ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩

/-- The first polar adjoint maps the cropped support onto precisely the
compressed support already used by boundary normalization.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedFirstCroppedSupport_polarAdjoint
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedFirstEdgeCroppedSupportES A₀ A₁).map
        (jointMixedFirstEdgePolarIsometry A₀ A₁ h₀ h₁).toLinearMap.adjoint =
      jointMixedFirstEdgeCompressedSupportES A₀ A₁ := by
  change (jointMixedFirstEdgeCroppedSupportES A₀ A₁).map
    (Matrix.toEuclideanLin (_ ⊗ₖ _)).adjoint = _
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  exact map_euclidean_range_mulVec _ _

/-- The last polar adjoint has the reflected exact support image.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedLastCroppedSupport_polarAdjoint
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedLastEdgeCroppedSupportES A₀ A₁).map
        (jointMixedLastEdgePolarIsometry A₀ A₁ h₀ h₁).toLinearMap.adjoint =
      jointMixedLastEdgeCompressedSupportES A₀ A₁ := by
  change (jointMixedLastEdgeCroppedSupportES A₀ A₁).map
    (Matrix.toEuclideanLin (_ ⊗ₖ _)).adjoint = _
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  exact map_euclidean_range_mulVec _ _

/-- The actual first-edge inclusion is the joint boundary polar frame
composed with the neighboring physical-00 inclusion.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  jointMixedFirstEdgePhysicalIsometry.comp (jointMixedFirstEdgePolarIsometry A₀ A₁ h₀ h₁)

/-- The reflected actual last-edge inclusion.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    EuclideanSpace ℂ (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  jointMixedLastEdgePhysicalIsometry.comp (jointMixedLastEdgePolarIsometry A₀ A₁ h₀ h₁)

/-- Compression of the actual first interaction is exactly the canonical
parent projection of the actual compressed support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdge_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedFirstEdgeIsometry A₀ A₁ h₀ h₁).compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap) =
      1 - (jointMixedFirstEdgeCompressedSupportES A₀ A₁).starProjection.toLinearMap := by
  rw [jointMixedFirstEdgeIsometry, LinearIsometry.compression_comp,
    jointMixedFirstPhysical_compression_parentInteraction,
    LinearIsometry.compression_one_sub_starProjection_of_le_range _ _
      (jointMixedFirstEdgeCroppedSupport_le_polarRange A₀ A₁ h₀ h₁),
    map_jointMixedFirstCroppedSupport_polarAdjoint]

/-- The actual last interaction has the reflected exact compression.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdge_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedLastEdgeIsometry A₀ A₁ h₀ h₁).compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap) =
      1 - (jointMixedLastEdgeCompressedSupportES A₀ A₁).starProjection.toLinearMap := by
  rw [jointMixedLastEdgeIsometry, LinearIsometry.compression_comp,
    jointMixedLastPhysical_compression_parentInteraction,
    LinearIsometry.compression_one_sub_starProjection_of_le_range _ _
      (jointMixedLastEdgeCroppedSupport_le_polarRange A₀ A₁ h₀ h₁),
    map_jointMixedLastCroppedSupport_polarAdjoint]

/-- The actual first compressed interaction has precisely the support
whose joint boundary normalization was proved earlier.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_jointMixedFirstEdge_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    LinearMap.ker ((jointMixedFirstEdgeIsometry A₀ A₁ h₀ h₁).compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      jointMixedFirstEdgeCompressedSupportES A₀ A₁ := by
  rw [jointMixedFirstEdge_compression_parentInteraction,
    ← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
    ← Submodule.starProjection_orthogonal', Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- The last compressed interaction has exactly the reflected compressed
support; no additional kernel-identification premise is required.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_jointMixedLastEdge_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    LinearMap.ker ((jointMixedLastEdgeIsometry A₀ A₁ h₀ h₁).compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      jointMixedLastEdgeCompressedSupportES A₀ A₁ := by
  rw [jointMixedLastEdge_compression_parentInteraction,
    ← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
    ← Submodule.starProjection_orthogonal', Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- Boundary-only normalization of the actual compressed first
interaction gives the canonical unchanged-tensor core constraint.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdge_normalize_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedFirstEdgeNormalizationEquivES A₀ A₁ h₀ h₁).symm.deformedConstraintProjection
        ((jointMixedFirstEdgeIsometry A₀ A₁ h₀ h₁).compression
          (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
            (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0)
              2).range.starProjection.toLinearMap)) =
      (jointEndpointFirstEdgeCoreSupportES A₀
        (fun x => D₀ x + D₁ x))ᗮ.starProjection.toLinearMap := by
  rw [jointMixedFirstEdge_compression_parentInteraction,
    ← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
    ← Submodule.starProjection_orthogonal']
  exact (jointMixedFirstEdgeNormalization_deformed_constraints A₀ A₁ h₀ h₁).1

/-- The reflected boundary normalization gives the last unchanged-tensor
core constraint from the actual compressed interaction.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdge_normalize_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedLastEdgeNormalizationEquivES A₀ A₁ h₀ h₁).symm.deformedConstraintProjection
        ((jointMixedLastEdgeIsometry A₀ A₁ h₀ h₁).compression
          (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
            (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0)
              2).range.starProjection.toLinearMap)) =
      (jointEndpointLastEdgeCoreSupportES A₀
        (fun x => D₀ x + D₁ x))ᗮ.starProjection.toLinearMap := by
  rw [jointMixedLastEdge_compression_parentInteraction,
    ← ContinuousLinearMap.toLinearMap_one, ← ContinuousLinearMap.toLinearMap_sub,
    ← Submodule.starProjection_orthogonal']
  exact (jointMixedLastEdgeNormalization_deformed_constraints A₀ A₁ h₀ h₁).1

end

end MPSTensor.MPOSymmetry
