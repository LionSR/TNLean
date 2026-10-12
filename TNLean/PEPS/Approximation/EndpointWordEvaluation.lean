/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorWord
import TNLean.PEPS.Approximation.UnitMemoryCoordinates

/-! # Evaluation of the literal source-endpoint word

The endpoint word applies its supplied maps to the two endpoint factors at each
original source slot, in their recorded order. The identity uses arbitrary endpoint
vectors and maps. It is the operator identity needed to connect sampled source
coordinates with the actual word before grouping the registers by their owners.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}

private theorem eval_localEndpoint_tmul (r : Reg P)
    (A : r.space →L[ℂ] r.space) (tail : Layout P) (x : r.space) (y : Mem tail) :
    (Word.localEndpoint r A tail).eval (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] y := by
  simp [Word.localEndpoint, Word.eval, appendIso, isoL_apply,
    LinearIsometryEquiv.symm_lTensor]

namespace SourceInventory
private theorem slotVector_cons_eq (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    slotVector (r :: R) U V η =
      Layout.memCongr (slotLayout_cons r R U V).symm
        (assocL (U 0) (V 0)
          (Mem (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)))
          (η 0 ⊗ₜ slotVector R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
            (fun i ↦ η i.succ))) := rfl

/-- The actual endpoint word acts factor by factor on the original endpoint
vectors. No normalization or nonvanishing assumption is used.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 279–309 and 565–588. -/
theorem eval_endpointWord_slotVector_tmul (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (u : ∀ i, U i) (v : ∀ i, V i) :
    (endpointWord R U V A B).eval (slotVector R U V (fun i ↦ u i ⊗ₜ v i)) =
      slotVector R U V (fun i ↦ A i (u i) ⊗ₜ B i (v i)) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      simp only [endpointWord, Word.eval_castLayouts, comp_apply, isoL_apply,
        slotVector_cons_eq, LinearIsometryEquiv.symm_apply_apply]
      apply congrArg (Layout.memCongr (slotLayout_cons r R U V).symm)
      simp only [assocL_tmul, Word.eval_comp, comp_apply, Word.eval_frame,
        lTensor_tmul, eval_localEndpoint_tmul, ih]

end SourceInventory
end TNLean.PEPS.PairEffect
