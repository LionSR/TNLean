/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCoordinateInclusion
import TNLean.MPS.Core.IsometricBondCompression
import TNLean.MPS.Symmetry.WeightedMatrixUnitInterpolation
import TNLean.MPS.Symmetry.SPTFixedPointEmbedding
import TNLean.MPS.Symmetry.ProjectiveDirectSumInclusions
import Mathlib.Data.Fin.Embedding

/-!
# Smaller fixed-point tensors in the common physical space

At either endpoint of the direct-sum bond interpolation, restrict the bond
indices to the occupied summand while retaining the common physical
alphabet. This gives the corresponding smaller matrix-unit tensor embedded
physically. Its boundary spaces are contained in those of the weighted
endpoint, and their periodic vectors agree at every positive length.

Source: arXiv:1010.3732, Section II.F.2, equations `eq:sym:omega-gamma`
and `eq:1d-sym:jointsym`.

**Scope restriction (trivial character):** The two endpoint covariance
statements use the on-site action with trivial scalar character; see
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.

**Local fix (second-block range):** The right endpoint restricts to the
second block with indices `D₀+1, …, D₀+D₁`, not the printed upper limit
`D₁`; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- The first fixed point in the common physical alphabet, retaining its
original bond dimension. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, the endpoint at zero. -/
noncomputable def embeddedSptFixedPointLeft (D₀ D₁ : ℕ) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₀ :=
  fun p => (weightedMatrixUnitInterpolation D₀ D₁ 0 p).submatrix
    (Fin.castAdd D₁) (Fin.castAdd D₁)

/-- The second fixed point in the common physical alphabet, retaining its
original bond dimension. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, the endpoint at one. -/
noncomputable def embeddedSptFixedPointRight (D₀ D₁ : ℕ) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) D₁ :=
  fun p => (weightedMatrixUnitInterpolation D₀ D₁ 1 p).submatrix
    (Fin.natAdd D₀) (Fin.natAdd D₀)

/-- The first endpoint is the standard fixed point under the physical
isometry induced by its bond summand. Source: arXiv:1010.3732,
Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem embeddedSptFixedPointLeft_eq_rotatePhysical (D₀ D₁ : ℕ) :
    embeddedSptFixedPointLeft D₀ D₁ =
      rotatePhysical (Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.castAddEmb D₁)))
        (sptFixedPointTensor D₀) := by
  ext p a b
  rw [rotatePhysical_coordinateInclusion_sptFixedPointTensor_apply]
  obtain ⟨⟨x, y⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [embeddedSptFixedPointLeft, weightedMatrixUnitInterpolation_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, Fin.castAddEmb_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [normalizedBondInterpolationMatrix_zero_apply, sptScale]
  · simp

/-- The second endpoint is the standard fixed point under the physical
isometry induced by its bond summand. Source: arXiv:1010.3732,
Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem embeddedSptFixedPointRight_eq_rotatePhysical (D₀ D₁ : ℕ) :
    embeddedSptFixedPointRight D₀ D₁ =
      rotatePhysical (Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.natAddEmb D₀)))
        (sptFixedPointTensor D₁) := by
  ext p a b
  rw [rotatePhysical_coordinateInclusion_sptFixedPointTensor_apply]
  obtain ⟨⟨x, y⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [embeddedSptFixedPointRight, weightedMatrixUnitInterpolation_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, Fin.natAddEmb_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [normalizedBondInterpolationMatrix_one_apply, sptScale]
  · simp

/-- The first embedded endpoint is injective when its bond dimension is
positive. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, the first isometric endpoint. -/
theorem embeddedSptFixedPointLeft_isInjective (D₀ D₁ : ℕ) [NeZero D₀] :
    Kraus.IsInjective (embeddedSptFixedPointLeft D₀ D₁) := by
  simpa only [embeddedSptFixedPointLeft_eq_rotatePhysical] using
    isInjective_rotatePhysical_coordinateInclusion_sptFixedPointTensor (Fin.castAddEmb D₁)

/-- The second embedded endpoint is injective when its bond dimension is
positive. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, the second isometric endpoint. -/
theorem embeddedSptFixedPointRight_isInjective (D₀ D₁ : ℕ) [NeZero D₁] :
    Kraus.IsInjective (embeddedSptFixedPointRight D₀ D₁) := by
  simpa only [embeddedSptFixedPointRight_eq_rotatePhysical] using
    isInjective_rotatePhysical_coordinateInclusion_sptFixedPointTensor (Fin.natAddEmb D₀)

/-- The first endpoint has no rows outside its occupied bond summand.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem weightedMatrixUnitInterpolation_zero_rowSupport
    (D₀ D₁ : ℕ) (p : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (i : Fin (D₀ + D₁)) (hi : i ∉ Set.range (Fin.castAdd D₁ : Fin D₀ → _))
    (j : Fin (D₀ + D₁)) : weightedMatrixUnitInterpolation D₀ D₁ 0 p i j = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · exact (hi ⟨i, rfl⟩).elim
  · rw [weightedMatrixUnitInterpolation_eq_left_mul]
    simp [Matrix.mul_apply, normalizedBondInterpolationMatrix_zero_apply]

/-- The second endpoint has no rows outside its occupied bond summand.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem weightedMatrixUnitInterpolation_one_rowSupport
    (D₀ D₁ : ℕ) (p : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (i : Fin (D₀ + D₁)) (hi : i ∉ Set.range (Fin.natAdd D₀ : Fin D₁ → _))
    (j : Fin (D₀ + D₁)) : weightedMatrixUnitInterpolation D₀ D₁ 1 p i j = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · rw [weightedMatrixUnitInterpolation_eq_left_mul]
    simp [Matrix.mul_apply, normalizedBondInterpolationMatrix_one_apply]
  · exact (hi ⟨i, rfl⟩).elim

/-- The first endpoint intertwines its occupied bond inclusion with the
smaller tensor. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem weightedMatrixUnitInterpolation_zero_intertwine (D₀ D₁ : ℕ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    weightedMatrixUnitInterpolation D₀ D₁ 0 p *
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) * embeddedSptFixedPointLeft D₀ D₁ p :=
  Matrix.coordinateInclusion_intertwine_of_rowSupport (Fin.castAddEmb D₁)
    (weightedMatrixUnitInterpolation D₀ D₁ 0 p)
    (weightedMatrixUnitInterpolation_zero_rowSupport D₀ D₁ p)

/-- The second endpoint intertwines its occupied bond inclusion with the
smaller tensor. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem weightedMatrixUnitInterpolation_one_intertwine (D₀ D₁ : ℕ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    weightedMatrixUnitInterpolation D₀ D₁ 1 p *
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) * embeddedSptFixedPointRight D₀ D₁ p :=
  Matrix.coordinateInclusion_intertwine_of_rowSupport (Fin.natAddEmb D₀)
    (weightedMatrixUnitInterpolation D₀ D₁ 1 p)
    (weightedMatrixUnitInterpolation_one_rowSupport D₀ D₁ p)

/-- The first smaller endpoint has its boundary space contained in that
of the weighted endpoint. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, endpoint parent comparison. -/
theorem groundSpace_embeddedSptFixedPointLeft_le (D₀ D₁ L : ℕ) :
    groundSpace (embeddedSptFixedPointLeft D₀ D₁) L ≤
      groundSpace (weightedMatrixUnitInterpolation D₀ D₁ 0) L :=
  groundSpace_le_of_isometric_bond_intertwiner _ _
    (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
    (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
    (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁) L

/-- The second smaller endpoint has its boundary space contained in that
of the weighted endpoint. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, endpoint parent comparison. -/
theorem groundSpace_embeddedSptFixedPointRight_le (D₀ D₁ L : ℕ) :
    groundSpace (embeddedSptFixedPointRight D₀ D₁) L ≤
      groundSpace (weightedMatrixUnitInterpolation D₀ D₁ 1) L :=
  groundSpace_le_of_isometric_bond_intertwiner _ _
    (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
    (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
    (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁) L

/-- The first embedded endpoint has the same periodic vector as the weighted
endpoint at every positive length. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem mpv_embeddedSptFixedPointLeft {D₀ D₁ N : ℕ} (hN : 0 < N)
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ 0) σ =
      mpv (embeddedSptFixedPointLeft D₀ D₁) σ :=
  mpv_eq_of_supported_isometric_bond_intertwiner _ _
    (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
    (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
    (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁)
    (fun p => Matrix.coordinateInclusion_projection_mul_of_rowSupport _ _
      (weightedMatrixUnitInterpolation_zero_rowSupport D₀ D₁ p)) hN σ

/-- The second embedded endpoint has the same periodic vector as the weighted
endpoint at every positive length. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem mpv_embeddedSptFixedPointRight {D₀ D₁ N : ℕ} (hN : 0 < N)
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    mpv (weightedMatrixUnitInterpolation D₀ D₁ 1) σ =
      mpv (embeddedSptFixedPointRight D₀ D₁) σ :=
  mpv_eq_of_supported_isometric_bond_intertwiner _ _
    (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
    (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
    (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁)
    (fun p => Matrix.coordinateInclusion_projection_mul_of_rowSupport _ _
      (weightedMatrixUnitInterpolation_one_rowSupport D₀ D₁ p)) hN σ

/-- The first embedded endpoint is covariant under the common physical
symmetry, with its original virtual representation. Source:
arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem twistedTensor_embeddedSptFixedPointLeft
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (g : G) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    twistedTensor (embeddedSptFixedPointLeft D₀ D₁)
      (sptFixedPointAction (ρ₀.directSum ρ₁) 1) g p =
      (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) *
        embeddedSptFixedPointLeft D₀ D₁ p * (sptGauge ρ₀ g).inv :=
  rotatePhysical_gauge_covariance_of_isometric_bond_intertwiner
    (weightedMatrixUnitInterpolation D₀ D₁ 0) (embeddedSptFixedPointLeft D₀ D₁)
    (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
    (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
    (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁)
    (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g)
    (sptGauge (ρ₀.directSum ρ₁) g) (sptGauge ρ₀ g)
    (ρ₀.directSum_coordinateInclusion_left ρ₁ g⁻¹)
    (twistedTensor_weightedMatrixUnitInterpolation ρ₀ ρ₁ g 0) p
/-- The second embedded endpoint is covariant under the common physical
symmetry, with its original virtual representation. Source:
arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem twistedTensor_embeddedSptFixedPointRight
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (g : G) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    twistedTensor (embeddedSptFixedPointRight D₀ D₁)
      (sptFixedPointAction (ρ₀.directSum ρ₁) 1) g p =
      (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) *
        embeddedSptFixedPointRight D₀ D₁ p * (sptGauge ρ₁ g).inv :=
  rotatePhysical_gauge_covariance_of_isometric_bond_intertwiner
    (weightedMatrixUnitInterpolation D₀ D₁ 1) (embeddedSptFixedPointRight D₀ D₁)
    (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
    (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
    (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁)
    (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g)
    (sptGauge (ρ₀.directSum ρ₁) g) (sptGauge ρ₁ g)
    (ρ₀.directSum_coordinateInclusion_right ρ₁ g⁻¹)
    (twistedTensor_weightedMatrixUnitInterpolation ρ₀ ρ₁ g 1) p

end MPSTensor
