/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.NeumannInverse

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Range projectors of injective finite-dimensional maps

For an injective map \(T\) with finite-dimensional Hilbert domain and complete
Hilbert codomain, this file records the standard formula
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

/-- The inverse Gram operator is a left inverse of the Gram operator. -/
@[simp]
theorem inverseGram_comp_adjoint_comp_self (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (inverseGram T hT).comp (T.adjoint.comp T) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).symm_apply_apply x

/-- The inverse Gram operator is a right inverse of the Gram operator. -/
@[simp]
theorem adjoint_comp_self_comp_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (T.adjoint.comp T).comp (inverseGram T hT) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).apply_symm_apply x

/-- The inverse Gram operator agrees with the inverse operation on continuous linear maps. -/
theorem inverseGram_eq_inverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = (T.adjoint.comp T).inverse := by
  symm
  exact ContinuousLinearMap.inverse_eq
    (adjoint_comp_self_comp_inverseGram T hT)
    (inverseGram_comp_adjoint_comp_self T hT)

/-- The inverse Gram operator agrees with the ring-theoretic inverse. -/
theorem inverseGram_eq_ringInverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = Ring.inverse (T.adjoint.comp T) := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact inverseGram_eq_inverse T hT

/-- If the Gram operator is within norm `a < 1` of the identity, then its inverse
has norm at most `(1 - a)⁻¹`. The denominator is the Neumann inverse bound. -/
theorem norm_inverseGram_le_of_norm_one_sub_adjoint_comp_self_le
    (T : E →L[𝕜] F) (hT : Function.Injective T) {a : ℝ}
    (ha : ‖1 - T.adjoint.comp T‖ ≤ a) (ha_lt_one : a < 1) :
    ‖inverseGram T hT‖ ≤ (1 - a)⁻¹ := by
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      letI : Subsingleton E := hE
      have hzero : inverseGram T hT = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact inv_nonneg.mpr (sub_nonneg.mpr ha_lt_one.le)
  | inr hE =>
      letI : Nontrivial E := hE
      rw [inverseGram_eq_ringInverse]
      simpa only [sub_sub_cancel] using
        NormedRing.norm_inverse_one_sub_le (1 - T.adjoint.comp T) ha ha_lt_one

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
