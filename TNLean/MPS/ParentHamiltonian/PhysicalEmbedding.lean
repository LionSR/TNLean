/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.Algebra.IsometricProjection
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.ParentHamiltonian.MatrixRepresentation

/-!
# Boundary spaces under rectangular physical embeddings

A rectangular physical map carries every boundary vector to its tensor
power applied to the original vector. For an isometry, the canonical
parent projection on the larger space also penalizes the orthogonal
complement of the included physical space. These are the endpoint
embeddings of arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym.
-/

open scoped Matrix

namespace MPSTensor

attribute [local instance] groundSpaceES_hasOrthogonalProjection

/-- A rectangular physical map transports the local boundary map by its
tensor power. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, physical endpoint embeddings. -/
theorem groundSpaceMap_rotatePhysical_rectangular {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) (L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMap (rotatePhysical E A) L X =
      (Matrix.rectKronecker fun _ : Fin L => E).mulVec (groundSpaceMap A L X) := by
  ext σ
  simp [groundSpaceMap_apply, evalWord_rotatePhysical_ofFn, Matrix.mulVec,
    dotProduct, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul, Matrix.rectKronecker_apply]

/-- The boundary space of a rectangularly rotated tensor is the image of
its original boundary space under the tensor power. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem groundSpace_rotatePhysical_rectangular {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) (L : ℕ) :
    groundSpace (rotatePhysical E A) L =
      (groundSpace A L).map (Matrix.toLin' (Matrix.rectKronecker fun _ : Fin L => E)) := by
  have h : groundSpaceMap (rotatePhysical E A) L =
      (Matrix.toLin' (Matrix.rectKronecker fun _ : Fin L => E)).comp (groundSpaceMap A L) :=
    LinearMap.ext (groundSpaceMap_rotatePhysical_rectangular E A L)
  rw [groundSpace, groundSpace, h, LinearMap.range_comp]

/-- Hilbert-space form of the boundary-space image identity for a
rectangular physical map. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem groundSpaceES_rotatePhysical_rectangular {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) (L : ℕ) :
    groundSpaceES (rotatePhysical E A) L =
      (groundSpaceES A L).map (Matrix.toEuclideanLin
        (Matrix.rectKronecker fun _ : Fin L => E)) := by
  rw [groundSpaceES, groundSpaceES, groundSpace_rotatePhysical_rectangular,
    ← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- The canonical parent of a physically embedded tensor is the complement
of the isometric image of its boundary-space projection.
Source context: arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteractionES_rotatePhysical_isometry {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (L : ℕ) :
    let T := Matrix.toEuclideanLin (Matrix.rectKronecker fun _ : Fin L => E)
    parentInteractionES (rotatePhysical E A) L =
      1 - T ∘ₗ (groundSpaceES A L).starProjection.toLinearMap ∘ₗ T.adjoint := by
  let T := Matrix.toEuclideanLin (Matrix.rectKronecker fun _ : Fin L => E)
  have hT : T.adjoint ∘ₗ T = LinearMap.id := by
    simpa only [T, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin (Matrix.rectKronecker_conjTranspose_mul_self (N := L) hE)
  have hinner (x y : EuclideanSpace ℂ (Cfg d L)) :
      inner ℂ (T x) (T y) = inner ℂ x y := by
    rw [← LinearMap.adjoint_inner_right]
    rw [← LinearMap.comp_apply, hT, LinearMap.id_apply]
  let I := T.isometryOfInner hinner
  let : CompleteSpace ((groundSpaceES A L).map I.toLinearMap) :=
    FiniteDimensional.complete ℂ _
  let : ((groundSpaceES A L).map I.toLinearMap).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have hproj := I.starProjection_map_eq_comp_adjoint (groundSpaceES A L)
  have hmap : (groundSpaceES A L).map I.toLinearMap =
      groundSpaceES (rotatePhysical E A) L := by
    simpa only [I, LinearMap.isometryOfInner_toLinearMap] using
      (groundSpaceES_rotatePhysical_rectangular E A L).symm
  simp only [hmap] at hproj
  simp only [I, LinearMap.isometryOfInner_toLinearMap] at hproj
  rw [parentInteractionES, Submodule.starProjection_orthogonal,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id, hproj]
  rfl

/-- The embedded canonical parent consists of the transported parent and
the projection onto unused physical states. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteractionES_rotatePhysical_isometry_decomposition {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (L : ℕ) :
    let T := Matrix.toEuclideanLin (Matrix.rectKronecker fun _ : Fin L => E)
    parentInteractionES (rotatePhysical E A) L =
      T ∘ₗ parentInteractionES A L ∘ₗ T.adjoint + (1 - T ∘ₗ T.adjoint) := by
  rw [parentInteractionES_rotatePhysical_isometry E hE]
  simp only [parentInteractionES, Submodule.starProjection_orthogonal,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id,
    LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.id_comp]
  abel

/-- Matrix form of the canonical-parent decomposition under an isometric
physical embedding. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem parentInteraction_matrix_rotatePhysical_isometry {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (L : ℕ) :
    let T := Matrix.rectKronecker fun _ : Fin L => E
    LinearMap.toMatrix' (parentInteraction (rotatePhysical E A) L) =
      T * LinearMap.toMatrix' (parentInteraction A L) * Tᴴ + (1 - T * Tᴴ) := by
  apply Matrix.toEuclideanLin.injective
  simpa only [parentInteractionES_eq_toEuclideanLin_parentMatrix,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_add, map_sub,
    Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
    Module.End.one_eq_id, LinearMap.comp_assoc] using
    parentInteractionES_rotatePhysical_isometry_decomposition E hE A L

/-- The canonical parent acts as the identity on states orthogonal to
the embedded physical space. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteractionES_rotatePhysical_isometry_apply_of_adjoint_eq_zero
    {d m D : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (L : ℕ) (v : EuclideanSpace ℂ (Cfg m L))
    (hv : (Matrix.toEuclideanLin (Matrix.rectKronecker fun _ : Fin L => E)).adjoint v = 0) :
    parentInteractionES (rotatePhysical E A) L v = v := by
  rw [parentInteractionES_rotatePhysical_isometry E hE]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
    hv, map_zero, sub_zero]

end MPSTensor
