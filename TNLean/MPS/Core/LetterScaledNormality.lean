/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ScaledNormality

/-!
# Rescaling each letter of a tensor by its own scalar

Multiplying the letter `A^i` of a matrix product state tensor by a nonzero scalar `c i`
multiplies every word by the product of the scalars of its letters, which is nonzero. The span
of the length-`N` words is therefore unchanged, and block injectivity and normality are
invariant under such a rescaling. With a constant `c` this is `MPSTensor.isNormal_smul_iff`.

## Main results

* `MPSTensor.evalWord_letterSmul`: the word of the rescaled tensor.
* `MPSTensor.wordSpan_letterSmul_eq`: the span of the length-`N` words is invariant.
* `MPSTensor.isNBlkInjective_letterSmul_iff`, `MPSTensor.isNormal_letterSmul_iff`: block
  injectivity and normality are invariant.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Rescaling each letter `i` by a scalar `c i` multiplies a word by the product of the scalars
of its letters. -/
theorem evalWord_letterSmul (c : Fin d → ℂ) (A : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (fun i ↦ c i • A i) w = (w.map c).prod • Kraus.evalWord A w := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ih, Kraus.evalWord_cons, List.map_cons, List.prod_cons,
        smul_mul_smul_comm]

/-- Rescaling each letter by a scalar does not enlarge the span of the length-`N` words. -/
theorem wordSpan_letterSmul_le (c : Fin d → ℂ) (A : MPSTensor d D) (N : ℕ) :
    Kraus.wordSpan (fun i ↦ c i • A i) N ≤ Kraus.wordSpan A N := by
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun σ ↦ ?_)
  rw [evalWord_letterSmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

/-- Rescaling each letter by its own nonzero scalar preserves the span of the length-`N`
words. -/
theorem wordSpan_letterSmul_eq {c : Fin d → ℂ} (hc : ∀ i, c i ≠ 0) (A : MPSTensor d D)
    (N : ℕ) : Kraus.wordSpan (fun i ↦ c i • A i) N = Kraus.wordSpan A N := by
  refine le_antisymm (wordSpan_letterSmul_le c A N) ?_
  have h := wordSpan_letterSmul_le (fun i ↦ (c i)⁻¹) (fun i ↦ c i • A i) N
  simp only [inv_smul_smul₀ (hc _)] at h
  exact h

/-- Rescaling each letter by its own nonzero scalar preserves block injectivity at every
blocking length. -/
theorem isNBlkInjective_letterSmul_iff {c : Fin d → ℂ} (hc : ∀ i, c i ≠ 0)
    (A : MPSTensor d D) (N : ℕ) :
    Kraus.IsNBlkInjective (fun i ↦ c i • A i) N ↔ Kraus.IsNBlkInjective A N := by
  simp only [Kraus.IsNBlkInjective, wordSpan_letterSmul_eq hc A N]

/-- Rescaling each letter by its own nonzero scalar preserves normality. -/
theorem isNormal_letterSmul_iff {c : Fin d → ℂ} (hc : ∀ i, c i ≠ 0) (A : MPSTensor d D) :
    Kraus.IsNormal (fun i ↦ c i • A i) ↔ Kraus.IsNormal A := by
  simp only [Kraus.isNormal_iff, isNBlkInjective_letterSmul_iff hc A]

end MPSTensor
