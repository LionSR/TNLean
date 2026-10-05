/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.IsometricProjectorTransport
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Orthogonal range projectors in finite coordinate spaces

The coordinate matrix of the orthogonal projection onto a subspace of complex
functions is characterized by its range. These are the local range projectors,
whose complements are the canonical parent interactions in SCP10.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {ι : Type*} [Fintype ι]

/-- A coordinate subspace equipped with the standard physical inner product. -/
noncomputable def coordinateSubspaceES (S : Submodule ℂ (ι → ℂ)) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  S.map (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap

/-- Orthogonal projection onto a subspace in the standard coordinate basis. -/
noncomputable def coordinateRangeProjector (S : Submodule ℂ (ι → ℂ)) : Matrix ι ι ℂ := by
  classical
  exact Matrix.toEuclideanLin.symm (coordinateSubspaceES S).starProjection.toLinearMap

/-- The coordinate range projector is an orthogonal projector. -/
theorem coordinateRangeProjector_isStarProjection (S : Submodule ℂ (ι → ℂ)) :
    IsStarProjection (coordinateRangeProjector S) := by
  classical
  have hp := Submodule.isSymmetricProjection_starProjection (coordinateSubspaceES S)
  apply (isStarProjection_iff').mpr
  constructor
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2]
    simp only [coordinateRangeProjector, LinearEquiv.apply_symm_apply]
    exact hp.isIdempotentElem.eq
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    simpa only [coordinateRangeProjector, LinearEquiv.apply_symm_apply] using hp.isSymmetric

/-- A vector is fixed by the coordinate projector exactly when it lies in the subspace. -/
theorem coordinateRangeProjector_mulVec_eq_self_iff (S : Submodule ℂ (ι → ℂ)) (x : ι → ℂ) :
    coordinateRangeProjector S *ᵥ x = x ↔ x ∈ S := by
  classical
  have hact : WithLp.toLp 2 (coordinateRangeProjector S *ᵥ x) =
      (coordinateSubspaceES S).starProjection (WithLp.toLp 2 x) := by
    change Matrix.toEuclideanLin (coordinateRangeProjector S) (WithLp.toLp 2 x) = _
    rw [coordinateRangeProjector, LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · intro h
    have hh := congrArg (WithLp.toLp 2) h
    rw [hact, Submodule.starProjection_eq_self_iff] at hh
    simpa [coordinateSubspaceES] using hh
  · intro hx
    apply (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.injective
    change WithLp.toLp 2 (coordinateRangeProjector S *ᵥ x) = WithLp.toLp 2 x
    rw [hact, Submodule.starProjection_eq_self_iff]
    simpa [coordinateSubspaceES] using hx

/-- The coordinate projector has exactly the prescribed range. -/
theorem range_coordinateRangeProjector (S : Submodule ℂ (ι → ℂ)) :
    (coordinateRangeProjector S).mulVecLin.range = S := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply (coordinateRangeProjector_mulVec_eq_self_iff S _).mp
    change coordinateRangeProjector S *ᵥ (coordinateRangeProjector S *ᵥ y) = _
    rw [Matrix.mulVec_mulVec, (coordinateRangeProjector_isStarProjection S).isIdempotentElem.eq]
    rfl
  · intro h
    exact ⟨x, (coordinateRangeProjector_mulVec_eq_self_iff S x).mpr h⟩

/-- Every orthogonal projector with the prescribed coordinate range equals this one. -/
theorem eq_coordinateRangeProjector_of_range {P : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (S : Submodule ℂ (ι → ℂ))
    (hr : P.mulVecLin.range = S) : P = coordinateRangeProjector S :=
  matrix_eq_of_isStarProjection_range_eq hP (coordinateRangeProjector_isStarProjection S)
    (hr.trans (range_coordinateRangeProjector S).symm)

end TNLean.PEPS
