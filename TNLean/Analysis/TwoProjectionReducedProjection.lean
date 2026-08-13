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
its projector blockwise in arXiv:1703.09188, Proposition IV.5, line 764. Identifying
that blockwise projector with this canonical construction is recorded in
`docs/paper-gaps/1703_two_projection_projector_typo.tex`. -/
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
source defines its reduced projector blockwise; the identification of that blockwise
projector with `reducedProjection P Q` is recorded in
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
