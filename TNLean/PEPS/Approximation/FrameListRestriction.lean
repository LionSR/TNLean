/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Restricting unselected spectator registers

Adjoining registers excluded by a selector does not change the selected
operator of a source-free word. The retained input and output registers
need not be empty.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 233–267 and 351–381.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word

/-- Framing registers excluded by the selector preserves the selected operator.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 233–267 and 351–381. -/
theorem restrict_frameList_eval_heq_of_eq_nil {Q : Type} (f : Q → Bool)
    (rs : Layout Q) (hrs : Layout.restrict f rs = []) {a b : Layout Q}
    (w : Word a b) (hs : w.sources = []) :
    HEq (((Word.frameList rs w).restrict f ((Word.sources_frameList _ _).trans hs)).eval)
      ((w.restrict f hs).eval) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases hr : f r.owner = true
      · simp [Layout.restrict_cons, hr] at hrs
      · have hr' := Bool.eq_false_iff.mpr hr
        exact (Word.restrict_frame_false_eval_heq f r _ _ hr').trans
          (ih (by simpa only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte] using hrs))

end TNLean.PEPS.PairEffect.Word
