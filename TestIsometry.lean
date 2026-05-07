import Mathlib
open scoped EuclideanSpace

variable {D r : ℕ} (V : Matrix (Fin D × Fin r) (Fin D) ℂ)

example (x y : EuclideanSpace ℂ (Fin D)) : ⟪V.toEuclideanLin x, V.toEuclideanLin y⟫ = ⟪x, y⟫ := by
  calc
    ⟪V.toEuclideanLin x, V.toEuclideanLin y⟫ = ⟪x, (V.toEuclideanLin).adjoint (V.toEuclideanLin y)⟫ := by
      rw [← LinearMap.adjoint_inner_right (V.toEuclideanLin) x (V.toEuclideanLin y)]
    _ = ⟪x, ((V.conjTranspose).toEuclideanLin ∘ₗ V.toEuclideanLin) y⟫ := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint V, LinearMap.comp_apply]
    _ = ⟪x, ((V.conjTranspose * V).toEuclideanLin) y⟫ := by
      rw [← toLpLin_mul_same]
    _ = ⟪x, (1 : Matrix (Fin D) (Fin D) ℂ).toEuclideanLin y⟫ := by
      sorry
    _ = ⟪x, y⟫ := by simp
