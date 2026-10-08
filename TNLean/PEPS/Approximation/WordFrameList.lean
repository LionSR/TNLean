/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-! # Evaluation with spectator registers

Retaining a list of registers tensors the actual word evaluation with the
identity on their memory. This formula applies to arbitrary spectator vectors.
Source: polynomial-PEPS, `04-compression.tex`, lines 246–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-sourceprivatepreparation-03
TNLean.PEPS.PairEffect.Word.eval_frameList_tmul
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Word
variable {P : Type}

/-- A framed word acts on the second factor of an actual memory tensor.
Source: polynomial-PEPS 04-compression.tex, lines 246–251. -/
theorem eval_frameList_tmul {a b : Layout P} (w : Word a b)
    (rs : Layout P) (x : Mem rs) (y : Mem a) :
    (Word.frameList rs w).eval ((appendIso rs a).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso rs b).symm (x ⊗ₜ[ℂ] w.eval y) := by
  induction rs with
  | nil => exact map_smul w.eval x y
  | cons r rs ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z => u ⊗ₜ[ℂ] z) (ih v)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]

end TNLean.PEPS.PairEffect.Word
