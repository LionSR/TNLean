/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EqualRangeRightFactor
import TNLean.Algebra.OrthogonalProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The reduced projection of two orthogonal projections

For symmetric projections `P` and `Q` on a finite-dimensional complex inner-product
space, this file defines the reduced projection canonically as the orthogonal projection
onto `range (P.comp Q)`. It proves properties (i)–(iii) of arXiv:1703.09188,
Proposition IV.5, lines 764–769, together with the required range equality, and obtains
the invertible right factor in property (iv) from equality of ranges.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The reduced projection associated to two symmetric projections `P` and `Q`.

It is the orthogonal projection onto `range (P.comp Q)`. The source instead defines
its projector blockwise in arXiv:1703.09188, Proposition IV.5, line 764. The
identification with that blockwise projector remains part of the global Jordan
decomposition; see `docs/paper-gaps/1703_two_projection_projector_typo.tex`. -/
noncomputable def reducedProjection (P Q : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  (LinearMap.range (P.comp Q)).starProjection

/-- The reduced projection is a symmetric projection. -/
theorem reducedProjection_isSymmetric (P Q : E →ₗ[ℂ] E) :
    (reducedProjection P Q).IsSymmetricProjection := by
  exact Submodule.isSymmetricProjection_starProjection _

/-- The reduced projection has range `range (P.comp Q)`. -/
theorem range_reducedProjection (P Q : E →ₗ[ℂ] E) :
    LinearMap.range (reducedProjection P Q) = LinearMap.range (P.comp Q) := by
  exact Submodule.range_starProjection _

/-- For symmetric projections, `range (P.comp Q)` equals `range (P.comp Q.comp P)`.

This range identity is a coordinate-free consequence of the projection hypotheses. The
source defines its reduced projector blockwise, and identifying that projector with
`reducedProjection P Q` remains part of the global Jordan decomposition; see
`docs/paper-gaps/1703_two_projection_projector_typo.tex`. -/
theorem reducedProjection_range_triple {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    LinearMap.range (P.comp (Q.comp P)) = LinearMap.range (P.comp Q) := by
  let A := Q.comp P
  have hAadj : LinearMap.adjoint A = P.comp Q := by
    simp [A, LinearMap.adjoint_comp, hP.isSymmetric.adjoint_eq,
      hQ.isSymmetric.adjoint_eq]
  have h := LinearMap.range_adjoint_comp_self A
  have hcomp : (LinearMap.adjoint A).comp A = P.comp (Q.comp P) := by
    rw [hAadj]
    ext x
    change P (Q (Q (P x))) = P (Q (P x))
    have hQx := congrArg (fun T : Module.End ℂ E ↦ T (P x)) hQ.isIdempotentElem.eq
    simpa [Module.End.mul_apply] using congrArg P hQx
  rw [hcomp, hAadj] at h
  exact h

/-- Property (i) of arXiv:1703.09188, Proposition IV.5, line 767:
`P.comp (reducedProjection P Q) = reducedProjection P Q`. -/
theorem comp_reducedProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    P.comp (reducedProjection P Q) = reducedProjection P Q := by
  ext x
  apply (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
  have hx : reducedProjection P Q x ∈ LinearMap.range (reducedProjection P Q) := ⟨x, rfl⟩
  rw [range_reducedProjection] at hx
  exact LinearMap.range_comp_le_range Q P hx

/-- Property (ii) of arXiv:1703.09188, Proposition IV.5, line 768:
`(reducedProjection P Q).comp Q = P.comp Q`. -/
theorem reducedProjection_comp {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    (reducedProjection P Q).comp Q = P.comp Q := by
  ext x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨x, rfl⟩
  · rw [Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    change ⟪Q x - P (Q x), P (Q z)⟫_ℂ = 0
    rw [← hP.isSymmetric (Q x - P (Q x)) (Q z)]
    have hPx := congrArg (fun T : Module.End ℂ E ↦ T (Q x)) hP.isIdempotentElem.eq
    simp only [map_sub]
    rw [show P (P (Q x)) = P (Q x) by simpa [Module.End.mul_apply] using hPx,
      sub_self, inner_zero_left]

/-- Property (iii) of arXiv:1703.09188, Proposition IV.5, line 769:
`Q.comp P = Q.comp (reducedProjection P Q)`. -/
theorem comp_reducedProjection_left {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Q.comp P = Q.comp (reducedProjection P Q) := by
  have h := congrArg LinearMap.adjoint (reducedProjection_comp (P := P) (Q := Q) hP)
  simpa [LinearMap.adjoint_comp, hP.isSymmetric.adjoint_eq, hQ.isSymmetric.adjoint_eq,
    (reducedProjection_isSymmetric P Q).isSymmetric.adjoint_eq] using h.symm

/-- The kernel of the second projection is transverse to the range of the reduced
projection.

This is the injectivity property needed to restrict a positive semidefinite matrix with
support projection `Q` to the reduced range. Although the reduced range need not be
contained in `range Q`, no nonzero vector in it is annihilated by `Q`.

Source: arXiv:1703.09188, Proposition IV.5, lines 764–781. -/
theorem disjoint_ker_range_reducedProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Disjoint (LinearMap.ker Q) (LinearMap.range (reducedProjection P Q)) := by
  rw [Submodule.disjoint_def]
  intro x hxQ hxT
  rw [range_reducedProjection] at hxT
  obtain ⟨y, rfl⟩ := hxT
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪P (Q y), P (Q y)⟫_ℂ = 0
  rw [hP.isSymmetric (Q y) (P (Q y))]
  have hPQy := congrArg (fun A : Module.End ℂ E ↦ A (Q y)) hP.isIdempotentElem.eq
  rw [show P (P (Q y)) = P (Q y) by simpa [Module.End.mul_apply] using hPQy]
  rw [hQ.isSymmetric y (P (Q y)),
    show Q (P (Q y)) = 0 from LinearMap.mem_ker.mp hxQ, inner_zero_right]

/-- The reduced product and the reduced projection have the same range.

This derived range equality is the input to the equal-range right-factor theorem; it is
not a separately stated item of arXiv:1703.09188, Proposition IV.5. -/
theorem range_reducedProjection_comp {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    LinearMap.range ((reducedProjection P Q).comp Q) =
      LinearMap.range (reducedProjection P Q) := by
  rw [reducedProjection_comp hP, range_reducedProjection]

/-- The invertible right factor in arXiv:1703.09188, Proposition IV.5, line 770. -/
theorem exists_reducedProjection_rightFactor {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    ∃ Y : E ≃ₗ[ℂ] E,
      ((reducedProjection P Q).comp Q).comp Y.toLinearMap = reducedProjection P Q := by
  exact LinearMap.exists_linearEquiv_comp_eq_of_range_eq _ _
    (range_reducedProjection_comp hP)

end LinearMap.IsSymmetricProjection

namespace Matrix

variable {D : ℕ}

private theorem toEuclideanLin_mul (A B : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  change Matrix.toLin (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis (A * B) = _
  exact Matrix.toLin_mul (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis A B

/-- A matrix orthogonal projection acts as a symmetric projection on Euclidean space. -/
theorem isSymmetricProjection_toEuclideanLin
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

end Matrix
