/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EqualRangeRightFactor
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The reduced projection of two orthogonal projections

For symmetric projections `P` and `Q` on a finite-dimensional complex inner-product
space, this file defines the reduced projection canonically as the orthogonal projection
onto `range (P.comp Q)`. It proves the absorption and range identities used in
arXiv:1703.09188, Proposition IV.5 (`prop:continuity-index`), lines 764–770, and obtains
the invertible right factor from equality of ranges.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The reduced projection associated to two symmetric projections `P` and `Q`.

It is the orthogonal projection onto `range (P.comp Q)`. By
`reducedProjection_range_triple`, this is also the orthogonal projection onto
`range (P.comp (Q.comp P))`, the coordinate-free form of the blockwise projector
from arXiv:1703.09188, Proposition IV.5, lines 764–770. -/
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

Thus `reducedProjection P Q` is exactly the projector onto the triple-product range
specified in arXiv:1703.09188, Proposition IV.5, lines 764–770. -/
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

/-- The first source identity: `P.comp (reducedProjection P Q) = reducedProjection P Q`. -/
theorem comp_reducedProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    P.comp (reducedProjection P Q) = reducedProjection P Q := by
  ext x
  apply (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
  have hx : reducedProjection P Q x ∈ LinearMap.range (reducedProjection P Q) := ⟨x, rfl⟩
  rw [range_reducedProjection] at hx
  exact LinearMap.range_comp_le_range Q P hx

/-- The second source identity: `(reducedProjection P Q).comp Q = P.comp Q`. -/
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

/-- The third source identity: `Q.comp P = Q.comp (reducedProjection P Q)`. -/
theorem comp_reducedProjection_left {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Q.comp P = Q.comp (reducedProjection P Q) := by
  have h := congrArg LinearMap.adjoint (reducedProjection_comp (P := P) (Q := Q) hP)
  simpa [LinearMap.adjoint_comp, hP.isSymmetric.adjoint_eq, hQ.isSymmetric.adjoint_eq,
    (reducedProjection_isSymmetric P Q).isSymmetric.adjoint_eq] using h.symm

/-- The reduced product and the reduced projection have the same range. -/
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

/-- The paper's right factor, expressed as a unit in the endomorphism ring. -/
theorem exists_isUnit_reducedProjection_rightFactor {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    ∃ Y : Module.End ℂ E, IsUnit Y ∧
      ((reducedProjection P Q).comp Q).comp Y = reducedProjection P Q := by
  obtain ⟨Y, hY⟩ := exists_reducedProjection_rightFactor (P := P) (Q := Q) hP
  refine ⟨Y.toLinearMap, ?_, hY⟩
  rw [Module.End.isUnit_iff]
  exact Y.bijective

end LinearMap.IsSymmetricProjection
