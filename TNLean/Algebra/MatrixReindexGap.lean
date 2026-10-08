/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Kernels and norm gaps under configuration reindexing

Reindexing both indices of a square matrix intertwines its Euclidean action
with the corresponding configuration isometry. Thus the isometry transports
the entire kernel and preserves any norm gap on its orthogonal complement.
These statements require no positivity hypothesis.
-/

open scoped InnerProductSpace
namespace Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Reindexing a square matrix intertwines its Euclidean action with
configuration reindexing. -/
theorem toEuclideanLin_reindex_piLpCongrLeft
    (e : ι ≃ κ) (H : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    toEuclideanLin (reindex e e H) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (toEuclideanLin H v) := by
  ext a
  change (∑ b : κ, H (e.symm a) (e.symm b) * v (e.symm b)) =
    ∑ b : ι, H (e.symm a) b * v b
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- The configuration isometry maps the complete Euclidean kernel onto
the kernel of the reindexed matrix. -/
theorem ker_toEuclideanLin_reindex_map
    (e : ι ≃ κ) (H : Matrix ι ι ℂ) :
    (LinearMap.ker (toEuclideanLin H)).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv.toLinearMap =
      LinearMap.ker (toEuclideanLin (reindex e e H)) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change toEuclideanLin (reindex e e H)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v) = 0
    rw [toEuclideanLin_reindex_piLpCongrLeft, LinearMap.mem_ker.mp hv, map_zero]
  · intro hw
    refine ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm w, ?_,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).apply_symm_apply w⟩
    apply LinearMap.mem_ker.mpr
    apply (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).injective
    rw [← toEuclideanLin_reindex_piLpCongrLeft,
      LinearIsometryEquiv.apply_symm_apply, LinearMap.mem_ker.mp hw, map_zero]

/-- Configuration reindexing preserves a norm gap on the orthogonal
complement of the entire kernel, with the same constant. -/
theorem norm_gap_toEuclideanLin_reindex
    (e : ι ≃ κ) (H : Matrix ι ι ℂ) {γ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ,
      γ * ‖v‖ ≤ ‖toEuclideanLin H v‖) :
    ∀ w ∈ (LinearMap.ker (toEuclideanLin (reindex e e H)))ᗮ,
      γ * ‖w‖ ≤ ‖toEuclideanLin (reindex e e H) w‖ := by
  intro w hw
  rw [← ker_toEuclideanLin_reindex_map e H,
    ← Submodule.map_orthogonal_equiv, Submodule.mem_map_equiv] at hw
  have hOp : toEuclideanLin (reindex e e H) w =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (toEuclideanLin H ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm w)) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      toEuclideanLin_reindex_piLpCongrLeft e H
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm w)
  simpa only [hOp, LinearIsometryEquiv.norm_map] using
    hGap ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm w) hw
end Matrix
