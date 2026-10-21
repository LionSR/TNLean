/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordRestriction
import TNLean.Lattice.PartyCircuit.WordEvaluationTransport

/-!
# Restricting spectator registers

Restricting a source-free word framed by spectator registers retains precisely
the selected spectators beside the selected word. Registers excluded by the
selector do not change its operator. The retained memories may be arbitrary.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 233–267 and 351–381.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word

variable {P : Type}

/-- Restriction of a source-free word framed by arbitrary spectators is the
restricted word framed by precisely the retained spectators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_frameList_eval_heq (f : P → Bool) (rs : Layout P)
    {a b : Layout P} (w : Word a b) (hs : w.sources = []) :
    HEq ((frameList rs w).restrict f ((sources_frameList w rs).trans hs)).eval
      (frameList (Layout.restrict f rs) (w.restrict f hs)).eval := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases hr : f r.owner = true
      · have h := (restrict_frame_true_eval_heq f r (frameList rs w)
          ((sources_frameList w rs).trans hs) hr).trans
            (eval_frame_heq r
              ((frameList rs w).restrict f ((sources_frameList w rs).trans hs))
              (frameList (Layout.restrict f rs) (w.restrict f hs))
              (Layout.restrict_append f rs a) (Layout.restrict_append f rs b) ih)
        have hprefix : Layout.restrict f (r :: rs) = r :: Layout.restrict f rs := by
          simp only [Layout.restrict_cons, hr, ↓reduceIte]
        exact h.trans (eval_frameList_heq (w.restrict f hs) (w.restrict f hs)
          rfl rfl HEq.rfl _ _ hprefix.symm)
      · have hr' := Bool.eq_false_iff.mpr hr
        have h := (restrict_frame_false_eval_heq f r (frameList rs w)
          ((sources_frameList w rs).trans hs) hr').trans ih
        have hprefix : Layout.restrict f (r :: rs) = Layout.restrict f rs := by
          simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte]
        exact h.trans (eval_frameList_heq (w.restrict f hs) (w.restrict f hs)
          rfl rfl HEq.rfl _ _ hprefix.symm)

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
