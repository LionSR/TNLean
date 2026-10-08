/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Isometric transport of a projection defect

An isometric change of Hilbert-space coordinates conjugates orthogonal
projections and preserves operator norms. Taking the adjoint reverses the
order of the two projections. Consequently, a defect written as
\(P_UP_V-P_W\) in one coordinate system has the same norm as
\(P_W-P_VP_U\) in the original coordinates.

This elementary identity transports the three-window projection estimates
in Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, to the physical interval coordinates. It asserts no
tensor-specific projection estimate.
-/

namespace Submodule
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Isometric transport preserves the norm of a three-projection defect;
taking the adjoint reverses the projection order. Source: the coordinate
transport used in Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. No finite-dimensional hypothesis is required. -/
theorem norm_map_starProjection_comp_sub_eq
    (e : E ≃ₗᵢ[𝕜] F) (U V W : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    ‖(U.map e.toLinearMap).starProjection.comp (V.map e.toLinearMap).starProjection -
      (W.map e.toLinearMap).starProjection‖ =
      ‖W.starProjection - V.starProjection.comp U.starProjection‖ := by
  have hConj :
      (U.map e.toLinearMap).starProjection.comp (V.map e.toLinearMap).starProjection -
        (W.map e.toLinearMap).starProjection =
      (e : E →L[𝕜] F).comp
        ((U.starProjection.comp V.starProjection - W.starProjection).comp
          (e.symm : F →L[𝕜] E)) := by
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply, starProjection_map_apply,
      LinearIsometryEquiv.symm_apply_apply, map_sub]
    rfl
  rw [hConj, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  change ‖U.starProjection * V.starProjection - W.starProjection‖ =
    ‖W.starProjection - V.starProjection * U.starProjection‖
  rw [← norm_star, star_sub, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq,
    norm_sub_rev]

end Submodule
