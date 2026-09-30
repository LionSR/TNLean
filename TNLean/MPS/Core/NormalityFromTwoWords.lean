/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Defs

/-!
# Normality from matrix units built out of two words of length two

A tensor is normal once its words of one positive length span the full matrix algebra. For
the small worked examples it is enough that every matrix unit `E_{ij}` is a linear combination
of two words of length two. This module packages that certificate, so that each example only
supplies the table of words and coefficients.

## Main results

* `MPSTensor.isNormal_of_single_eq_two_words`: normality from a table expressing every matrix
  unit as a combination of two words of length two.
-/

namespace MPSTensor

/-- **Normality from two-word matrix units.** A tensor is normal when every matrix unit is a
linear combination of two words of length two: the length-two words then span the full matrix
algebra. -/
theorem isNormal_of_single_eq_two_words {d D : ℕ} (A : MPSTensor d D)
    (h : ∀ i j : Fin D, ∃ a b c e : Fin d, ∃ u v : ℂ,
      Matrix.single i j (1 : ℂ) = u • (A a * A b) + v • (A c * A e)) :
    Kraus.IsNormal A := by
  refine ⟨2, two_pos, ?_⟩
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun σ : Fin 2 → Fin d => Kraus.evalWord A (List.ofFn σ)) with hT
  have hword : ∀ a b : Fin d, A a * A b ∈ T := by
    intro a b
    refine Submodule.subset_span ⟨![a, b], ?_⟩
    simp [Kraus.evalWord, List.ofFn_succ]
  refine T.eq_top_of_forall_single_mem fun i j => ?_
  obtain ⟨a, b, c, e, u, v, hX⟩ := h i j
  rw [hX]
  exact T.add_mem (T.smul_mem _ (hword a b)) (T.smul_mem _ (hword c e))

end MPSTensor
