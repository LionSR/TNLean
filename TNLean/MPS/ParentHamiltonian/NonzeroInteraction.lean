/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Nonzero canonical parent interactions

The local MPS ground space has dimension at most \(D^2\). When the ambient
dimension \(d^L\) is larger, its complementary orthogonal projection is nonzero,
both as a matrix and in function-space coordinates.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- If \(d^L > D^2\), the matrix of the canonical parent interaction is nonzero. -/
theorem toMatrix'_parentInteraction_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : LinearMap.toMatrix' (parentInteraction A L) ≠ 0 := by
  intro hzero
  apply groundSpace_ne_top A L hDim
  apply top_unique
  intro v _
  have hmem := (toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff A L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)).mp
      (by simp only [hzero, map_zero, LinearMap.zero_apply])
  simpa using (mem_groundSpaceES_iff A L _).mp hmem

/-- If \(d^L > D^2\), the canonical parent interaction is nonzero in the
original function-space coordinates. -/
theorem parentInteraction_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : parentInteraction A L ≠ 0 := fun hzero ↦
  toMatrix'_parentInteraction_ne_zero A L hDim (by rw [hzero, map_zero])

end MPSTensor
