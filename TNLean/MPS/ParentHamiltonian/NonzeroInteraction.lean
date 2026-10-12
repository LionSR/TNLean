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
both in Euclidean and in function-space coordinates.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- If \(d^L > D^2\), the Euclidean canonical parent interaction is nonzero. -/
theorem parentInteractionES_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : parentInteractionES A L ≠ 0 := by
  intro hzero
  apply groundSpace_ne_top A L hDim
  apply top_unique
  intro v _
  have hmem := (parentInteractionES_apply_eq_zero_iff A L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)).mp
      (by simp only [hzero, LinearMap.zero_apply])
  simpa using (mem_groundSpaceES_iff A L _).mp hmem

/-- If \(d^L > D^2\), the canonical parent interaction is nonzero in the
original function-space coordinates. -/
theorem parentInteraction_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : parentInteraction A L ≠ 0 := by
  intro hzero
  apply parentInteractionES_ne_zero A L hDim
  apply LinearMap.ext
  intro v
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  have hv := LinearMap.congr_fun hzero (e v)
  change e (parentInteractionES A L (e.symm (e v))) = 0 at hv
  rw [LinearEquiv.symm_apply_apply] at hv
  apply e.injective
  simpa only [LinearMap.zero_apply, map_zero] using hv

end MPSTensor
