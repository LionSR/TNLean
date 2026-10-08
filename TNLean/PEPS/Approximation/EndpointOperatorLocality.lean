/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorWord

/-! # Locality of the actual endpoint operators

The source inventory records the owner and order of each endpoint. The literal
operator word restricted to selected parties depends only on their endpoints.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Word
/-- The literal endpoint operation acts on its actual endpoint factor.
Source: polynomial-PEPS 04-compression.tex, lines 279–309. -/
theorem eval_localEndpoint_tmul (r : Reg P) (A : r.space →L[ℂ] r.space) (tail : Layout P)
    (x : r.space) (y : Mem tail) :
    (localEndpoint r A tail).eval (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] y := by
  simp [localEndpoint, Word.eval, appendIso, isoL_apply,
    LinearIsometryEquiv.symm_lTensor]

/-- An endpoint outside the selected parties has no effect on their residual.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem restrict_localEndpoint_eval_eq_of_agree (f : P → Bool) (r : Reg P)
    (A B : r.space →L[ℂ] r.space) (tail : Layout P)
    (h : f r.owner = true → A = B) :
    ((localEndpoint r A tail).restrict f (sources_localEndpoint _ _ _)).eval =
      ((localEndpoint r B tail).restrict f (sources_localEndpoint _ _ _)).eval := by
  by_cases hr : f r.owner = true
  · cases h hr
    rfl
  · have hr' := Bool.eq_false_iff.mpr hr
    exact eq_of_heq ((restrict_localMap_false_eval_heq f r.owner _ _ _ tail hr').trans
      (restrict_localMap_false_eval_heq f r.owner _ _ _ tail hr').symm)
end Word
end TNLean.PEPS.PairEffect
