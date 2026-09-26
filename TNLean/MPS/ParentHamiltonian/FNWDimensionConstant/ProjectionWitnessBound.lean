/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A matrix coefficient lower bound for a projection defect

Unit vectors in two subspaces, one orthogonal to a third subspace, give a
lower bound for the norm of the product of the first two projections minus
the third projection. This is the Hilbert-space estimate used to test the
constant in Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`.
-/

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unit witnesses bound a projection defect from below by their inner product. -/
theorem norm_inner_le_norm_projection_defect
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖U.starProjection.comp V.starProjection - W.starProjection‖ := by
  have hinner : inner ℂ y
      ((U.starProjection.comp V.starProjection - W.starProjection) x) = inner ℂ y x := by
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply,
      V.starProjection_eq_self_iff.mpr hx, W.starProjection_apply_eq_zero_iff.mpr hxW,
      sub_zero, ← U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr hy]
  exact (show ‖inner ℂ y x‖ ≤
      ‖(U.starProjection.comp V.starProjection - W.starProjection) x‖ from
    by simpa only [hinner, hny, one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) y
        ((U.starProjection.comp V.starProjection - W.starProjection) x)).trans
      (by simpa only [hnx, mul_one] using
        (U.starProjection.comp V.starProjection - W.starProjection).le_opNorm x)

/-- The same witnesses bound the defect with the two projections reversed. -/
theorem norm_inner_le_norm_projection_defect_reverse [CompleteSpace E]
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖V.starProjection.comp U.starProjection - W.starProjection‖ := by
  have h := norm_inner_le_norm_projection_defect U V W hx hy hxW hnx hny
  simpa only [← ContinuousLinearMap.mul_def, star_sub, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq] using
    h.trans_eq (norm_star (U.starProjection * V.starProjection - W.starProjection)).symm

end Submodule
