/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projections under an isometric inclusion

If an isometry sends a subspace into a larger finite-dimensional Hilbert
space, the projection onto its image is obtained by composing the original
projection with the isometry and its adjoint. This is the projection identity
used for physical embeddings in arXiv:1010.3732, Section II.F.2,
equation `eq:1d-sym:jointsym`.
-/

namespace LinearIsometry

/-- Orthogonal projection onto the isometric image of a subspace is the
original projection composed with the isometry and its adjoint.
Source context: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem starProjection_map_eq_comp_adjoint
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) (p : Submodule 𝕜 E)
    [p.HasOrthogonalProjection] [(p.map f.toLinearMap).HasOrthogonalProjection] :
    (p.map f.toLinearMap).starProjection.toLinearMap =
      f.toLinearMap ∘ₗ p.starProjection.toLinearMap ∘ₗ f.toLinearMap.adjoint := by
  ext y
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.mem_map.mpr ⟨p.starProjection (f.toLinearMap.adjoint y),
      p.starProjection_apply_mem _, rfl⟩) ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, inner_sub_left,
    ← LinearMap.adjoint_inner_left]
  change inner 𝕜 (f.toLinearMap.adjoint y) x -
    inner 𝕜 (f (p.starProjection (f.toLinearMap.adjoint y))) (f x) = 0
  rw [f.inner_map_map, ← inner_sub_left]
  exact p.starProjection_inner_eq_zero _ x hx

end LinearIsometry
