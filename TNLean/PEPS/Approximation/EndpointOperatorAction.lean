/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointInventoryLocality

/-! # Actual endpoint coordinates and their sample average

The literal endpoint operator is expressed in the recorded source-slot bases.
The sample assignments are shared between the two endpoints of each slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The actual endpoint word applies the supplied maps to its two leading
endpoint factors and recursively to the remaining slots.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem eval_endpointWord_cons_tmul (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (x : U 0) (y : V 0)
    (z : Mem (slotLayout R (fun i => U i.succ) (fun i => V i.succ))) :
    (endpointWord (r :: R) U V A B).eval
      (Layout.memCongr (slotLayout_cons r R U V).symm (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))) =
      Layout.memCongr (slotLayout_cons r R U V).symm
        (A 0 x ⊗ₜ[ℂ] (B 0 y ⊗ₜ[ℂ]
          (endpointWord R (fun i => U i.succ) (fun i => V i.succ)
            (fun i => A i.succ) (fun i => B i.succ)).eval z)) := by
  simp only [endpointWord, Word.eval_castLayouts, comp_apply, isoL_apply,
    LinearIsometryEquiv.symm_apply_apply, Word.eval_comp,
    Word.eval_frame]
  erw [Word.eval_localEndpoint_tmul]
  erw [lTensor_tmul, comp_apply, Word.eval_localEndpoint_tmul, lTensor_tmul]

/-- Applying the actual endpoint word to an elementary source assignment
applies the actual endpoint maps independently at every original slot.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem eval_endpointWord_slotVector_tmul (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (x : ∀ i, U i) (y : ∀ i, V i) :
    (endpointWord R U V A B).eval (slotVector R U V (fun i => x i ⊗ₜ[ℂ] y i)) =
      slotVector R U V (fun i => A i (x i) ⊗ₜ[ℂ] B i (y i)) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      change (endpointWord (r :: R) U V A B).eval
        (Layout.memCongr (slotLayout_cons r R U V).symm
          (x 0 ⊗ₜ[ℂ] (y 0 ⊗ₜ[ℂ]
            slotVector R (fun i => U i.succ) (fun i => V i.succ)
              (fun i => x i.succ ⊗ₜ[ℂ] y i.succ)))) =
        Layout.memCongr (slotLayout_cons r R U V).symm
          (A 0 (x 0) ⊗ₜ[ℂ] (B 0 (y 0) ⊗ₜ[ℂ]
            slotVector R (fun i => U i.succ) (fun i => V i.succ)
              (fun i => A i.succ (x i.succ) ⊗ₜ[ℂ] B i.succ (y i.succ))))
      rw [eval_endpointWord_cons_tmul, ih]

end TNLean.PEPS.PairEffect.SourceInventory
