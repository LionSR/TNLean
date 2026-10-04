/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.EmbeddedFixedPointTensor
import TNLean.MPS.Symmetry.PolarFrameEmbedding

/-!
# Identifying polar endpoints with normalized matrix-unit tensors

A physical rotation of the normalized matrix-unit tensor has the rotating
matrix as its frame, multiplied by the nonzero normalization. Its covariance
therefore determines the intertwining identity of that frame.

Source context: arXiv:1010.3732, Section II.F.2, the convenient basis before
equation eq:sym:omega-gamma; arXiv:2011.12127, Section III.A, the normalized
matrix-unit construction.

**Scope restriction (one-site injective tensors):** the polar endpoint and
parent identities concern the injective single-block case of Sections II.C
and II.F.2 of arXiv:1010.3732; the several-block case is documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.

**Scope restriction (trivial character):** the two coordinate-frame
intertwining identities use the common fixed-point action with trivial
scalar character; see `docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix Kronecker
namespace MPSTensor

/-- A physical rotation of the normalized matrix-unit tensor has the
rotating matrix as its physical frame, multiplied by the normalization.
Source context: arXiv:1010.3732, Section II.F.2, convenient basis before
equation eq:sym:omega-gamma. -/
theorem rotatePhysical_sptFixedPointTensor_eq_ofPhysicalMatrix {m D : ℕ}
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) :
    rotatePhysical W (sptFixedPointTensor D) =
      ofPhysicalMatrix ((sptScale D) • W.submatrix id finProdFinEquiv) := by
  ext i a b
  simpa only [rotatePhysical_apply, ofPhysicalMatrix, Matrix.smul_apply,
    Matrix.submatrix_apply, id_eq, smul_eq_mul] using
    sum_smul_sptFixedPointTensor_apply (W i) a b

/-- Covariance of a physically embedded normalized matrix-unit tensor
forces its physical frame to intertwine the same virtual pair action.
Source context: arXiv:1010.3732, Section II.F.2, convenient basis before
equation eq:sym:omega-gamma. -/
theorem intertwiner_of_rotatePhysical_sptFixedPointTensor_covariance
    {m D : ℕ} [NeZero D] (W : Matrix (Fin m) (Fin (D * D)) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin D) (Fin D) ℂ)
    (hCov : rotatePhysical U (rotatePhysical W (sptFixedPointTensor D)) =
      fun i => X * rotatePhysical W (sptFixedPointTensor D) i * Y) :
    U * W = W * Matrix.reindex finProdFinEquiv finProdFinEquiv (Xᵀ ⊗ₖ Y) := by
  have h : U * physicalMatrix (rotatePhysical W (sptFixedPointTensor D)) =
      physicalMatrix (rotatePhysical W (sptFixedPointTensor D)) * (Xᵀ ⊗ₖ Y) :=
    physicalMatrix_covariance_of_rotatePhysical _ U X Y hCov
  have h' := congrArg (fun M : Matrix (Fin m) (Fin D × Fin D) ℂ =>
    M.submatrix id (virtualPairEquiv D)) h
  rw [Matrix.submatrix_mul U _ id (Equiv.refl (Fin m)) (virtualPairEquiv D)
      (Equiv.refl (Fin m)).bijective,
    Matrix.submatrix_mul _ (Xᵀ ⊗ₖ Y) id (virtualPairEquiv D) (virtualPairEquiv D)
      (virtualPairEquiv D).bijective] at h'
  simp only [rotatePhysical_sptFixedPointTensor_eq_ofPhysicalMatrix,
    physicalMatrix_ofPhysicalMatrix, Equiv.coe_refl, Matrix.submatrix_id_id,
    Matrix.submatrix_smul, Matrix.submatrix_submatrix, virtualPairEquiv,
    Function.comp_id, Equiv.self_comp_symm, Pi.smul_apply,
    Matrix.mul_smul, Matrix.smul_mul] at h'
  exact smul_right_injective _ (sptScale_ne_zero (D := D)) h'

/-- The polar endpoint, multiplied by the standard normalization, is the
normalized matrix-unit tensor in the prescribed target frame. Source context:
arXiv:1010.3732, Section II.F.2, the convenient basis before equation
eq:sym:omega-gamma. -/
theorem sptScale_smul_polarFrameEmbedding_polar_endpoint {d m D : ℕ}
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) :
    sptScale D • rotatePhysical (polarFrameEmbedding A W) (polarIsometricTensor A) =
      rotatePhysical ((Matrix.fromRows W 0).submatrix finSumFinEquiv.symm id)
        (sptFixedPointTensor D) := by
  rw [polarFrameEmbedding_polar_endpoint hA,
    rotatePhysical_sptFixedPointTensor_eq_ofPhysicalMatrix]
  rfl

/-- The embedded polar endpoint and the normalized target fixed point have
identical canonical parent interactions at every length. Source context:
arXiv:1010.3732, Sections II.C and II.F.2, the isometric parent and the
convenient basis before equation eq:sym:omega-gamma. -/
theorem parentInteraction_polarFrameEmbedding_polar_endpoint
    {d m D : ℕ} [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) (L : ℕ) :
    parentInteraction (rotatePhysical (polarFrameEmbedding A W) (polarIsometricTensor A)) L =
      parentInteraction
        (rotatePhysical ((Matrix.fromRows W 0).submatrix finSumFinEquiv.symm id)
          (sptFixedPointTensor D)) L := by
  apply parentInteraction_eq_of_groundSpace_eq
  rw [← sptScale_smul_polarFrameEmbedding_polar_endpoint hA W,
    groundSpace_smul_eq _ _ sptScale_ne_zero]

/-- The first physical coordinate frame intertwines the common fixed-point
action with its original virtual pair action. Source: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem sptPhysicalEmbedding_left_intertwiner
    {G : Type} [Group G] {D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω) (g : G) :
    sptFixedPointAction (ρ₀.directSum ρ₁) 1 g *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.castAddEmb D₁)) =
      Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.castAddEmb D₁)) *
        Matrix.reindex finProdFinEquiv finProdFinEquiv (sptKron (sptGauge ρ₀ g)) := by
  apply intertwiner_of_rotatePhysical_sptFixedPointTensor_covariance
    _ _ (sptGauge ρ₀ g) (sptGauge ρ₀ g).inv
  funext p
  simpa only [embeddedSptFixedPointLeft_eq_rotatePhysical, twistedTensor, rotatePhysical] using
    twistedTensor_embeddedSptFixedPointLeft ρ₀ ρ₁ g p

/-- The second physical coordinate frame intertwines the common fixed-point
action with its original virtual pair action. Source: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem sptPhysicalEmbedding_right_intertwiner
    {G : Type} [Group G] {D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω) (g : G) :
    sptFixedPointAction (ρ₀.directSum ρ₁) 1 g *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.natAddEmb D₀)) =
      Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.natAddEmb D₀)) *
        Matrix.reindex finProdFinEquiv finProdFinEquiv (sptKron (sptGauge ρ₁ g)) := by
  apply intertwiner_of_rotatePhysical_sptFixedPointTensor_covariance
    _ _ (sptGauge ρ₁ g) (sptGauge ρ₁ g).inv
  funext p
  simpa only [embeddedSptFixedPointRight_eq_rotatePhysical, twistedTensor, rotatePhysical] using
    twistedTensor_embeddedSptFixedPointRight ρ₀ ρ₁ g p

end MPSTensor
