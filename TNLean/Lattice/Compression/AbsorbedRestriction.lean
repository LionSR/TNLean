/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PartySelector
import TNLean.Lattice.Compression.WordStructuralCongruence
/-! # Successive restrictions of source-free words

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 351–381.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

private theorem restrict_restrict_eq_of_implies (f g : P → Bool)
    (h : ∀ p, g p = true → f p = true) (a : Layout P) :
    Layout.restrict g (Layout.restrict f a) = Layout.restrict g a := by
  simp only [Layout.restrict, List.filter_filter]
  apply List.filter_congr
  intro r hr
  by_cases hg : g r.owner = true
  · simp only [hg, h r.owner hg, Bool.true_and]
  · have hg' := Bool.eq_false_iff.mpr hg
    simp only [hg', Bool.false_and]

private theorem restrict_castLayouts_word_heq (f : P → Bool) {a b a' b' : Layout P}
    (w : Word a b) (ha : a = a') (hb : b = b') (hs : w.sources = []) :
    HEq ((w.castLayouts ha hb).restrict f ((Word.sources_castLayouts _ _ _).trans hs))
      (w.restrict f hs) := by
  rw [Word.restrict_castLayouts f w ha hb hs]
  exact Word.castLayouts_heq _ _ _

private theorem localMap_word_heq {p : P} {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (A : Mem a →L[ℂ] Mem b) {t u : Layout P} (h : t = u) :
    HEq (Word.localMap p ha hb A t) (Word.localMap p ha hb A u) := by
  cases h
  rfl

/-- A second restriction to a subset of the first selection is the actual
single restriction. This is an identity of words, including zero local maps.
Source: polynomial-PEPS 04-compression.tex, lines 233–267 and 351–381. -/
theorem Word.restrict_restrict_heq_of_implies {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (f g : P → Bool)
    (h : ∀ p, g p = true → f p = true) :
    HEq ((w.restrict f hs).restrict g (w.sources_restrict f hs)) (w.restrict g hs) := by
  induction w with
  | id a => exact Word.id_heq (restrict_restrict_eq_of_implies f g h a)
  | comp w v ihw ihv =>
      exact Word.comp_heq (restrict_restrict_eq_of_implies f g h _)
        (restrict_restrict_eq_of_implies f g h _) (restrict_restrict_eq_of_implies f g h _)
        (ihw (List.append_eq_nil_iff.mp hs).2) (ihv (List.append_eq_nil_iff.mp hs).1)
  | localMap p ha hb A tail =>
      by_cases hgp : g p = true
      · have hfp := h p hgp
        simp only [Word.restrict, dite_eq_left hfp, dite_eq_left hgp]
        refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
        simp only [Word.restrict, dite_eq_left hgp]
        exact (Word.castLayouts_heq _ _ _).trans
          ((localMap_word_heq ha hb A (restrict_restrict_eq_of_implies f g h tail)).trans
            (Word.castLayouts_heq _ _ _).symm)
      · by_cases hfp : f p = true
        · simp only [Word.restrict, dite_eq_left hfp, dite_eq_right hgp]
          refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
          simp only [Word.restrict, dite_eq_right hgp]
          exact (Word.castLayouts_heq _ _ _).trans
            ((Word.id_heq (restrict_restrict_eq_of_implies f g h tail)).trans
              (Word.castLayouts_heq _ _ _).symm)
        · simp only [Word.restrict, dite_eq_right hfp, dite_eq_right hgp]
          refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
          exact (Word.id_heq (restrict_restrict_eq_of_implies f g h tail)).trans
            (Word.castLayouts_heq _ _ _).symm
  | source => cases hs
  | swap r s tail =>
      have ht := restrict_restrict_eq_of_implies f g h tail
      by_cases hgr : g r.owner = true
      · have hfr := h r.owner hgr
        by_cases hgs : g s.owner = true
        · have hfs := h s.owner hgs
          simp only [Word.restrict, dite_eq_left hfr, dite_eq_left hfs,
            dite_eq_left hgr, dite_eq_left hgs]
          refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
          simp only [Word.restrict, dite_eq_left hgr, dite_eq_left hgs]
          exact (Word.castLayouts_heq _ _ _).trans
            ((Word.swap_heq r s ht).trans (Word.castLayouts_heq _ _ _).symm)
        · by_cases hfs : f s.owner = true
          · simp only [Word.restrict, dite_eq_left hfr, dite_eq_left hfs,
              dite_eq_left hgr, dite_eq_right hgs]
            refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
            simp only [Word.restrict, dite_eq_left hgr, dite_eq_right hgs]
            exact (Word.castLayouts_heq _ _ _).trans
              ((Word.id_heq (congrArg (r :: ·) ht)).trans (Word.castLayouts_heq _ _ _).symm)
          · simp only [Word.restrict, dite_eq_left hfr, dite_eq_right hfs,
              dite_eq_left hgr, dite_eq_right hgs]
            refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
            simp only [Word.restrict]
            exact (Word.id_heq (by rw [Layout.restrict_cons, ite_eq_left hgr, ht])).trans
              (Word.castLayouts_heq _ _ _).symm
      · by_cases hgs : g s.owner = true
        · have hfs := h s.owner hgs
          by_cases hfr : f r.owner = true
          · simp only [Word.restrict, dite_eq_left hfr, dite_eq_left hfs,
              dite_eq_right hgr, dite_eq_left hgs]
            refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
            simp only [Word.restrict, dite_eq_right hgr, dite_eq_left hgs]
            exact (Word.castLayouts_heq _ _ _).trans
              ((Word.id_heq (congrArg (s :: ·) ht)).trans (Word.castLayouts_heq _ _ _).symm)
          · simp only [Word.restrict, dite_eq_right hfr, dite_eq_left hfs,
              dite_eq_right hgr, dite_eq_left hgs]
            refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
            simp only [Word.restrict]
            exact (Word.id_heq (by rw [Layout.restrict_cons, ite_eq_left hgs, ht])).trans
              (Word.castLayouts_heq _ _ _).symm
        · by_cases hfr : f r.owner = true
          · by_cases hfs : f s.owner = true
            · simp only [Word.restrict, dite_eq_left hfr, dite_eq_left hfs,
                dite_eq_right hgr, dite_eq_right hgs]
              refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
              simp only [Word.restrict, dite_eq_right hgr, dite_eq_right hgs]
              exact (Word.castLayouts_heq _ _ _).trans
                ((Word.id_heq ht).trans (Word.castLayouts_heq _ _ _).symm)
            · simp only [Word.restrict, dite_eq_left hfr, dite_eq_right hfs,
                dite_eq_right hgr, dite_eq_right hgs]
              refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
              simp only [Word.restrict]
              exact (Word.id_heq (by rw [Layout.restrict_cons, ite_eq_right hgr, ht])).trans
                (Word.castLayouts_heq _ _ _).symm
          · by_cases hfs : f s.owner = true
            · simp only [Word.restrict, dite_eq_right hfr, dite_eq_left hfs,
                dite_eq_right hgr, dite_eq_right hgs]
              refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
              simp only [Word.restrict]
              exact (Word.id_heq (by rw [Layout.restrict_cons, ite_eq_right hgs, ht])).trans
                (Word.castLayouts_heq _ _ _).symm
            · simp only [Word.restrict, dite_eq_right hfr, dite_eq_right hfs,
                dite_eq_right hgr, dite_eq_right hgs]
              refine (restrict_castLayouts_word_heq g _ _ _ rfl).trans ?_
              exact (Word.id_heq ht).trans (Word.castLayouts_heq _ _ _).symm
  | frame r w ih =>
      by_cases hgr : g r.owner = true
      · have hfr := h r.owner hgr
        simp only [Word.restrict, dite_eq_left hfr, dite_eq_left hgr]
        refine (restrict_castLayouts_word_heq g (Word.frame r (w.restrict f hs)) _ _
          (w.sources_restrict f hs)).trans ?_
        simp only [Word.restrict, dite_eq_left hgr]
        exact (Word.castLayouts_heq _ _ _).trans
          ((Word.frame_heq r (restrict_restrict_eq_of_implies f g h _)
            (restrict_restrict_eq_of_implies f g h _) (ih hs)).trans
              (Word.castLayouts_heq _ _ _).symm)
      · by_cases hfr : f r.owner = true
        · simp only [Word.restrict, dite_eq_left hfr, dite_eq_right hgr]
          refine (restrict_castLayouts_word_heq g (Word.frame r (w.restrict f hs)) _ _
          (w.sources_restrict f hs)).trans ?_
          simp only [Word.restrict, dite_eq_right hgr]
          exact (Word.castLayouts_heq _ _ _).trans ((ih hs).trans
            (Word.castLayouts_heq _ _ _).symm)
        · simp only [Word.restrict, dite_eq_right hfr, dite_eq_right hgr]
          exact (restrict_castLayouts_word_heq g _ _ _ (w.sources_restrict f hs)).trans
            ((ih hs).trans (Word.castLayouts_heq _ _ _).symm)

/-- The actual twice-restricted operator is the singly restricted operator
under the canonical identification of register lists.
Source: polynomial-PEPS 04-compression.tex, lines 233–267 and 351–381. -/
theorem Word.restrict_restrict_eval_heq_of_implies {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (f g : P → Bool)
    (h : ∀ p, g p = true → f p = true) :
    HEq ((w.restrict f hs).restrict g (w.sources_restrict f hs)).eval
      (w.restrict g hs).eval :=
  Word.eval_heq (restrict_restrict_eq_of_implies f g h a)
    (restrict_restrict_eq_of_implies f g h b) (w.restrict_restrict_heq_of_implies hs f g h)

/-- Removing another party does not change the actual local operator at a
specified party. This follows from the words themselves and does not cancel
an operator on the complementary parties.
Source: polynomial-PEPS 04-compression.tex, lines 233–267 and 351–381. -/
theorem Word.restrict_withoutParty_atParty_eval_heq {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (p q : P) (hqp : q ≠ p) :
    HEq (((w.restrict (fun r => !partySelector p r) hs).restrict
      (partySelector q) (w.sources_restrict _ hs)).eval)
      ((w.restrict (partySelector q) hs).eval) := by
  apply w.restrict_restrict_eval_heq_of_implies
  intro r hr
  have he : r = q := by simpa only [partySelector, decide_eq_true_eq] using hr
  subst r
  simp only [partySelector, hqp, decide_false, Bool.not_false]
end TNLean.PEPS.PairEffect
