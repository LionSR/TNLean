/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Module.Completion

/-!
# C-star structures on norm completions

This file extends the involution of a C-star ring to its norm completion. The extension is
`UniformSpace.Completion.map star`; its algebraic laws and the C-star identity follow from the
density of the original ring.

The generic instances are isolated here because they are global orphan instances. If Mathlib adds
completion instances for star rings, this module should be compared with that implementation before
both are imported together.

## Main definitions

* `UniformSpace.Completion.toComplAlgHom` — the canonical algebra homomorphism into the completion.
* `UniformSpace.Completion.toComplStarAlgHom` — its star-preserving version.

## Main results

* `UniformSpace.Completion.denseRange_toComplStarAlgHom` — the canonical map has dense range.
-/

noncomputable section

namespace UniformSpace.Completion

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The involution on the completion is the uniformly continuous extension of the original
involution. -/
instance instStar : Star (Completion A) where
  star := Completion.map star

/-- The canonical inclusion into the completion preserves the involution. -/
@[simp, norm_cast]
theorem coe_star (a : A) : ((star a : A) : Completion A) = star (a : Completion A) :=
  (Completion.map_coe star_isometry.uniformContinuous a).symm

/-- The extended involution is continuous. -/
instance instContinuousStar : ContinuousStar (Completion A) where
  continuous_star := Completion.continuous_map

/-- The extended involution makes the completion a star ring. -/
instance instStarRing : StarRing (Completion A) where
  star_involutive x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_id
    | ih a => simp only [← coe_star, star_star]
  star_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← coe_mul, ← coe_star, star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← coe_add, ← coe_star, star_add]

/-- The C-star inequality passes from a normed star ring to its completion. -/
instance instCStarRing : CStarRing (Completion A) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a =>
        simpa only [← coe_star, ← coe_mul, norm_coe] using
          (CStarRing.norm_mul_self_le (x := a))

section Complex

variable [NormedAlgebra ℂ A] [StarModule ℂ A]

/-- The completed involution is conjugate-linear over the complex numbers. -/
instance instStarModule : StarModule ℂ (Completion A) where
  star_smul c x := by
    induction x using Completion.induction_on with
    | hp =>
        exact isClosed_eq
          (continuous_star.comp (ContinuousConstSMul.continuous_const_smul c))
          ((ContinuousConstSMul.continuous_const_smul (star c)).comp continuous_star)
    | ih a => simp only [← coe_smul, ← coe_star, star_smul]

/-- The norm completion of a complex normed C-star algebra is a C-star algebra. -/
instance instCStarAlgebra : CStarAlgebra (Completion A) where
  norm_smul_le := norm_smul_le

/-- The canonical complex algebra homomorphism into the norm completion. -/
def toComplAlgHom : A →ₐ[ℂ] Completion A where
  __ := Completion.coeRingHom
  commutes' _ := rfl

/-- The canonical complex star-algebra homomorphism into the norm completion. -/
def toComplStarAlgHom : A →⋆ₐ[ℂ] Completion A where
  __ := toComplAlgHom
  map_star' := coe_star

omit [StarModule ℂ A] in
/-- The canonical star-algebra homomorphism acts by the completion coercion. -/
@[simp]
theorem coe_toComplStarAlgHom : ⇑(toComplStarAlgHom : A →⋆ₐ[ℂ] Completion A) =
    ((↑) : A → Completion A) :=
  rfl

omit [StarModule ℂ A] in
/-- The original algebra is dense in its norm completion. -/
theorem denseRange_toComplStarAlgHom :
    DenseRange (toComplStarAlgHom : A →⋆ₐ[ℂ] Completion A) :=
  Completion.denseRange_coe

end Complex

end UniformSpace.Completion
