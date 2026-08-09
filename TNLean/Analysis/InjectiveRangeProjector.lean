/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Range projectors of injective finite-dimensional maps

For an injective map \(T\) between finite-dimensional Hilbert spaces, this file
packages the standard formula
\[
  P_{\operatorname{ran} T}=T(T^\dagger T)^{-1}T^\dagger.
\]
-/


namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The continuous inverse of the Gram endomorphism of an injective
finite-dimensional continuous linear map. -/
noncomputable def inverseGram (T : E →L[𝕜] F) (hT : Function.Injective T) : E →L[𝕜] E :=
  LinearMap.toContinuousLinearMap <|
    (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
      ((T.adjoint_comp_self_injective_iff).2 hT)).symm.toLinearMap

/-- The continuous range projector written through the inverse Gram operator. -/
noncomputable def injectiveRangeProjector (T : E →L[𝕜] F)
    (hT : Function.Injective T) : F →L[𝕜] F :=
  T.comp ((inverseGram T hT).comp T.adjoint)

/-- The continuous inverse-Gram formula is exactly the orthogonal projector
onto the range of an injective finite-dimensional map. -/
theorem injectiveRangeProjector_eq_starProjection (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    injectiveRangeProjector T hT = T.range.starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨inverseGram T hT (T.adjoint x), rfl⟩
  · rw [Submodule.mem_orthogonal']
    intro _ hy
    obtain ⟨y, rfl⟩ := hy
    change inner 𝕜 (x - injectiveRangeProjector T hT x) (T y) = 0
    rw [← T.adjoint_inner_left y (x - injectiveRangeProjector T hT x)]
    suffices T.adjoint (x - injectiveRangeProjector T hT x) = 0 by rw [this, inner_zero_left]
    rw [map_sub, injectiveRangeProjector, comp_apply, comp_apply]
    change T.adjoint x - (T.adjoint.comp T)
      (inverseGram T hT (T.adjoint x)) = 0
    rw [inverseGram]
    exact sub_eq_zero.mpr
      ((LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
        ((T.adjoint_comp_self_injective_iff).2 hT)).apply_symm_apply (T.adjoint x)).symm

end ContinuousLinearMap
