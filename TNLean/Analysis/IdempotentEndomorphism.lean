/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Projection

/-!
# Idempotent endomorphisms

Elementary pointwise consequences of idempotence for linear endomorphisms.
-/

namespace LinearMap.IsIdempotentElem

variable {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]

/-- An idempotent linear endomorphism fixes every vector in its image. -/
theorem apply_apply {P : E →ₗ[R] E} (hP : IsIdempotentElem P) (x : E) :
    P (P x) = P x := by
  simpa [Module.End.mul_apply] using congrArg (fun T : E →ₗ[R] E ↦ T x) hP.eq

end LinearMap.IsIdempotentElem
