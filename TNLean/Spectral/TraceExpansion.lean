/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixTracePairing

/-!
# Trace-expansion compatibility wrappers

The generic matrix lemmas now live in `TNLean.Algebra.MatrixTracePairing`.
This module preserves their original `MPSTensor` names for downstream users.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {𝕜 : Type*} [CommRing 𝕜]

/-- Compatibility wrapper for `Matrix.linearMap_trace_eq_sum_apply_single`. -/
lemma linearMap_trace_eq_sum_apply_single
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (T : Matrix (Fin D₁) (Fin D₂) 𝕜 →ₗ[𝕜] Matrix (Fin D₁) (Fin D₂) 𝕜) :
    (LinearMap.trace 𝕜 (Matrix (Fin D₁) (Fin D₂) 𝕜)) T =
      ∑ p : Fin D₁, ∑ q : Fin D₂, (T (Matrix.single p q (1 : 𝕜))) p q :=
  Matrix.linearMap_trace_eq_sum_apply_single T

/-- Compatibility wrapper for `Matrix.entry_mul_single_mul`. -/
lemma entry_mul_single_mul
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (M : Matrix (Fin D₁) (Fin D₁) 𝕜) (N : Matrix (Fin D₂) (Fin D₂) 𝕜)
    (p : Fin D₁) (q : Fin D₂) :
    (M * Matrix.single p q (1 : 𝕜) * N) p q = M p p * N q q :=
  Matrix.entry_mul_single_mul M N p q

end MPSTensor
