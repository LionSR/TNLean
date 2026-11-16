/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.DirectSumBlockRetraction
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank comparisons under reindexing

Simultaneous permutation of rows and columns preserves positivity and rank.
A rank inequality for a conjugated endomorphism therefore gives the same
inequality before reindexing. This is used for the finite-index versions of
the positive-map rank comparisons.
-/

namespace Matrix

/-- A rank comparison on positive semidefinite inputs is invariant under
simultaneous reindexing of rows and columns. -/
theorem rank_le_rank_map_of_reindexEndomorphism
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (T : Module.End ℂ (Matrix α α ℂ))
    (hRank : ∀ Y : Matrix β β ℂ, Y.PosSemidef →
      Y.rank ≤ (reindexEndomorphism e T Y).rank)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) : X.rank ≤ (T X).rank := by
  let E := Matrix.reindexLinearEquiv ℂ ℂ e e
  have h := hRank (E X) (hX.submatrix e.symm)
  have hApply : reindexEndomorphism e T (E X) = E (T X) := by
    simp [E, reindexEndomorphism_apply, Matrix.reindex_apply]
  rw [hApply] at h
  change (Matrix.reindex e e X).rank ≤ (Matrix.reindex e e (T X)).rank at h
  simpa only [Matrix.rank_reindex] using h

end Matrix
