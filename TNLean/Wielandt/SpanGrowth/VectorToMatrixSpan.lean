/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.MPS.Core.Blocking

/-!
# Vector-to-matrix span results for MPS tensors

This file preserves the established `MPSTensor` interface to the channel-generic
vector-to-matrix span results in `Kraus`. The blocking results remain here because
they use the tensor-network blocking operation.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Blocking transfer: word spans for blocked tensors -/

/-- A blocked word product of length `n` is an ordinary word product of length `n*L`. -/
theorem wordSpan_blockTensor_le (A : MPSTensor d D) (L n : ℕ) :
    Kraus.wordSpan (blockTensor (d := d) (D := D) A L) n ≤ Kraus.wordSpan A (n * L) := by
  classical
  apply Submodule.span_le.mpr
  rintro M ⟨σ, rfl⟩
  have hblock :
      Kraus.evalWord (blockTensor (d := d) (D := D) A L) (List.ofFn σ) =
        Kraus.evalWord A (flattenBlockedWord d L (List.ofFn σ)) :=
    evalWord_blockTensor (A := A) (L := L) (List.ofFn σ)
  have hlen : (flattenBlockedWord d L (List.ofFn σ)).length = n * L := by
    simpa [List.length_ofFn] using
      (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  simpa [hblock, hlen] using (Kraus.evalWord_mem_wordSpan A (flattenBlockedWord d L (List.ofFn σ)))

/-- If the blocked tensor has full word span at level `n`, then the original tensor
has full word span at level `n*L`. -/
theorem wordSpan_eq_top_of_blockTensor_wordSpan_eq_top
    (A : MPSTensor d D) (L n : ℕ)
    (h : Kraus.wordSpan (blockTensor (d := d) (D := D) A L) n = ⊤) :
    Kraus.wordSpan A (n * L) = ⊤ := by
  refine eq_top_iff.mpr ?_
  simpa [h] using (wordSpan_blockTensor_le (A := A) (L := L) (n := n))

end MPSTensor
