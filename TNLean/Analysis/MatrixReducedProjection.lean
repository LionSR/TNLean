/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Analysis.MatrixSqrt
import TNLean.Analysis.TraceNormAbs
import TNLean.Analysis.TwoProjectionReducedProjection

/-!
# Matrix coordinates for the reduced projection

This file represents the coordinate-free reduced projection of two endomorphisms on a
standard finite-dimensional complex Euclidean space as a square matrix. For orthogonal
projection matrices, it transfers the projection identities, transversality, and invertible
right factor from `LinearMap.IsSymmetricProjection.reducedProjection`.
-/

open scoped ComplexOrder

namespace Matrix

variable {D : ℕ}

private theorem isSymmetricProjection_toEuclideanLin
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsOrthogonalProjection P) :
    (Matrix.toEuclideanLin P).IsSymmetricProjection := by
  constructor
  · change Matrix.toEuclideanLin P * Matrix.toEuclideanLin P = Matrix.toEuclideanLin P
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, hP.2]
  · exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P)).mpr hP.1

/-- The matrix of the coordinate-free reduced projection in the standard Euclidean basis. -/
noncomputable def reducedProjection (P Q : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.toEuclideanLin.symm
    (LinearMap.IsSymmetricProjection.reducedProjection
      (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin Q))

/-- Converting the matrix reduced projection back to a Euclidean linear map recovers the
coordinate-free reduced projection. -/
@[simp] theorem toEuclideanLin_reducedProjection
    (P Q : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.toEuclideanLin (reducedProjection P Q) =
      LinearMap.IsSymmetricProjection.reducedProjection
        (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin Q) := by
  exact LinearEquiv.apply_symm_apply Matrix.toEuclideanLin _

/-- The matrix reduced projection is an orthogonal projection. -/
theorem reducedProjection_isOrthogonalProjection
    (P Q : Matrix (Fin D) (Fin D) ℂ) :
    IsOrthogonalProjection (reducedProjection P Q) := by
  have hT := LinearMap.IsSymmetricProjection.reducedProjection_isSymmetric
    (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin Q)
  constructor
  · exact (Matrix.isSymmetric_toEuclideanLin_iff
      (A := reducedProjection P Q)).mp (by simpa using hT.isSymmetric)
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul]
    simpa [Module.End.mul_eq_comp] using hT.isIdempotentElem.eq

/-- Matrix form of property (i): `P * reducedProjection P Q = reducedProjection P Q`. -/
theorem mul_reducedProjection {P Q : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) :
    P * reducedProjection P Q = reducedProjection P Q := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul]
  simpa using LinearMap.IsSymmetricProjection.comp_reducedProjection
    (isSymmetricProjection_toEuclideanLin hP)

/-- The reduced projection is also absorbed by `P` on the right. -/
theorem reducedProjection_mul {P Q : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) :
    reducedProjection P Q * P = reducedProjection P Q := by
  have hT := reducedProjection_isOrthogonalProjection P Q
  have h := congrArg Matrix.conjTranspose (mul_reducedProjection (Q := Q) hP)
  simpa [hP.1.eq, hT.1.eq] using h

/-- Matrix form of property (ii): `reducedProjection P Q * Q = P * Q`. -/
theorem reducedProjection_mul_second {P Q : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) :
    reducedProjection P Q * Q = P * Q := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul, toEuclideanLin_mul]
  simpa using LinearMap.IsSymmetricProjection.reducedProjection_comp
    (isSymmetricProjection_toEuclideanLin hP)

/-- Matrix form of property (iii): `Q * P = Q * reducedProjection P Q`. -/
theorem second_mul_reducedProjection {P Q : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q) :
    Q * P = Q * reducedProjection P Q := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul, toEuclideanLin_mul]
  simpa using LinearMap.IsSymmetricProjection.comp_reducedProjection_left
    (isSymmetricProjection_toEuclideanLin hP) (isSymmetricProjection_toEuclideanLin hQ)

/-- Matrix form of the reduced-range transversality statement. -/
theorem disjoint_ker_range_reducedProjection {P Q : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q) :
    Disjoint (LinearMap.ker (Matrix.toEuclideanLin Q))
      (LinearMap.range (Matrix.toEuclideanLin (reducedProjection P Q))) := by
  simpa using LinearMap.IsSymmetricProjection.disjoint_ker_range_reducedProjection
    (isSymmetricProjection_toEuclideanLin hP) (isSymmetricProjection_toEuclideanLin hQ)

/-- Matrix form of the invertible right factor:
`reducedProjection P Q * Q * Y = reducedProjection P Q`. -/
theorem exists_reducedProjection_rightFactor
    {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : IsOrthogonalProjection P) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, IsUnit Y ∧
      reducedProjection P Q * Q * Y = reducedProjection P Q := by
  let T := reducedProjection P Q
  obtain ⟨e, he⟩ :=
    LinearMap.IsSymmetricProjection.exists_reducedProjection_rightFactor
      (P := Matrix.toEuclideanLin P) (Q := Matrix.toEuclideanLin Q)
      (isSymmetricProjection_toEuclideanLin hP)
  let Y : Matrix (Fin D) (Fin D) ℂ := Matrix.toEuclideanLin.symm e.toLinearMap
  let Z : Matrix (Fin D) (Fin D) ℂ := Matrix.toEuclideanLin.symm e.symm.toLinearMap
  refine ⟨Y, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨Z, Matrix.toEuclideanLin.injective ?_⟩
    rw [toEuclideanLin_mul]
    simp [Y, Z]
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_mul]
    simpa [T, Y] using he

/-- Positive-semidefinite matrices supply invertible support-inverse extensions and an
invertible right factor for the reduced projection of their support projections. -/
theorem exists_units_supportInvExtension_reducedProjection_rightFactor
    {L R : Matrix (Fin D) (Fin D) ℂ} (hL : L.PosSemidef) (hR : R.PosSemidef) :
    ∃ X Z Y : Matrix (Fin D) (Fin D) ℂ,
      IsUnit X ∧ IsUnit Z ∧ IsUnit Y ∧
      X * L = hL.supportProj ∧ R * Z = hR.supportProj ∧
      hL.supportProj * hR.supportProj * Y =
        reducedProjection hL.supportProj hR.supportProj := by
  have hP : IsOrthogonalProjection hL.supportProj :=
    hL.isOrthogonalProjection_supportProj
  obtain ⟨Y, hY, hTQY⟩ := exists_reducedProjection_rightFactor
    (P := hL.supportProj) (Q := hR.supportProj) hP
  have hPQY : hL.supportProj * hR.supportProj * Y =
      reducedProjection hL.supportProj hR.supportProj := by
    rw [← reducedProjection_mul_second hP, hTQY]
  exact ⟨hL.supportInvExtension, hR.supportInvExtension, Y,
    hL.isUnit_supportInvExtension, hR.isUnit_supportInvExtension, hY,
    hL.supportInvExtension_mul_self, hR.self_mul_supportInvExtension, hPQY⟩

end Matrix
