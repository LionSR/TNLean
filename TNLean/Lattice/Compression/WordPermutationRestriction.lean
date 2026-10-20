/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordRestriction
import TNLean.Lattice.PartyCircuit.WordEvaluationTransport

/-!
# Restriction of register exchanges

Selecting owners commutes with exchanging successive lists of registers, at
the level of their operators. An erased moving register contributes the identity
on the retained memory. The retained tail is arbitrary throughout.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P : Type}

private theorem swap_eval_heq (r s : Reg P) {a b : Layout P} (h : a = b) :
    HEq (Word.swap r s a).eval (Word.swap r s b).eval := by
  cases h
  rfl

private theorem frame_id_eval (r : Reg P) (a : Layout P) :
    (Word.frame r (Word.id a)).eval = (Word.id (r :: a)).eval := by
  exact ContinuousLinearMap.lTensor_id _

private theorem moveHead_eval_heq_of_layouts_eq (r : Reg P) {a b t t' : Layout P}
    (ha : a = b) (ht : t = t') :
    HEq (moveHead r a t).eval (moveHead r b t').eval := by
  cases ha
  cases ht
  rfl

private theorem exchangeBlocks_eval_heq_of_layouts_eq {a a' b b' t t' : Layout P}
    (ha : a = a') (hb : b = b') (ht : t = t') :
    HEq (exchangeBlocks a b t).eval (exchangeBlocks a' b' t').eval := by
  cases ha
  cases hb
  cases ht
  rfl

/-- Moving a retained register through a prefix restricts to the same move through
the retained prefix and tail. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 233–267 and 409–434. -/
theorem restrict_moveHead_true_eval_heq (f : P → Bool) (r : Reg P)
    (rs tail : Layout P) (hr : f r.owner = true) :
    HEq ((moveHead r rs tail).restrict f (sources_moveHead r rs tail)).eval
      (moveHead r (Layout.restrict f rs) (Layout.restrict f tail)).eval := by
  induction rs with
  | nil =>
      change HEq (Word.id (Layout.restrict f (r :: tail))).eval
        (Word.id (r :: Layout.restrict f tail)).eval
      exact eval_id_heq (by simp only [Layout.restrict_cons, hr, ↓reduceIte])
  | cons s rs ih =>
      let u := (Word.frame s (moveHead r rs tail)).restrict f
        (sources_moveHead r rs tail)
      let v := (Word.swap s r (rs ++ tail)).restrict f rfl
      by_cases hs : f s.owner = true
      · have hu : HEq u.eval
            (Word.frame s (moveHead r (Layout.restrict f rs)
              (Layout.restrict f tail))).eval :=
          (restrict_frame_true_eval_heq f s (moveHead r rs tail)
            (sources_moveHead r rs tail) hs).trans
            (eval_frame_heq s
              ((moveHead r rs tail).restrict f (sources_moveHead r rs tail))
              (moveHead r (Layout.restrict f rs) (Layout.restrict f tail))
              (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, ↓reduceIte])
              (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, ↓reduceIte])
              ih)
        have hv : HEq v.eval
            (Word.swap s r (Layout.restrict f rs ++ Layout.restrict f tail)).eval :=
          (restrict_swap_true_true_eval_heq f s r (rs ++ tail) hs hr).trans
            (swap_eval_heq s r (Layout.restrict_append f rs tail))
        have hcomp := eval_comp_heq
          u v (Word.frame s (moveHead r (Layout.restrict f rs) (Layout.restrict f tail)))
          (Word.swap s r (Layout.restrict f rs ++ Layout.restrict f tail))
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs, hr, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append, hs, hr, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append, hs, hr, ↓reduceIte])
          hu hv
        change HEq (u.comp v).eval
          (moveHead r (Layout.restrict f (s :: rs)) (Layout.restrict f tail)).eval
        exact hcomp.trans (moveHead_eval_heq_of_layouts_eq r
          (a := s :: Layout.restrict f rs) (b := Layout.restrict f (s :: rs))
          (by simp only [Layout.restrict_cons, hs, ↓reduceIte])
          (rfl : Layout.restrict f tail = Layout.restrict f tail))
      · have hs' := Bool.eq_false_iff.mpr hs
        have hu : HEq u.eval
            (moveHead r (Layout.restrict f rs) (Layout.restrict f tail)).eval :=
          (restrict_frame_false_eval_heq f s (moveHead r rs tail)
            (sources_moveHead r rs tail) hs').trans ih
        have hv : HEq v.eval
            (Word.id (r :: (Layout.restrict f rs ++ Layout.restrict f tail))).eval :=
          (restrict_swap_false_true_eval_heq f s r (rs ++ tail) hs' hr).trans
            (eval_id_heq (congrArg (r :: ·) (Layout.restrict_append f rs tail)))
        have hcomp := eval_comp_heq
          u v (moveHead r (Layout.restrict f rs) (Layout.restrict f tail))
          (Word.id (r :: (Layout.restrict f rs ++ Layout.restrict f tail)))
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          hu hv
        change HEq (u.comp v).eval
          (moveHead r (Layout.restrict f (s :: rs)) (Layout.restrict f tail)).eval
        exact (hcomp.trans (heq_of_eq (ContinuousLinearMap.id_comp
          (moveHead r (Layout.restrict f rs) (Layout.restrict f tail)).eval))).trans
            (moveHead_eval_heq_of_layouts_eq r
              (a := Layout.restrict f rs) (b := Layout.restrict f (s :: rs))
              (by simp only [Layout.restrict_cons, hs', Bool.false_eq_true, ↓reduceIte])
              (rfl : Layout.restrict f tail = Layout.restrict f tail))

/-- Moving an erased register through any prefix restricts to the identity on
the retained prefix followed by the retained tail. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 233–267 and 409–434. -/
theorem restrict_moveHead_false_eval_heq (f : P → Bool) (r : Reg P)
    (rs tail : Layout P) (hr : f r.owner = false) :
    HEq ((moveHead r rs tail).restrict f (sources_moveHead r rs tail)).eval
      (Word.id (Layout.restrict f rs ++ Layout.restrict f tail)).eval := by
  induction rs with
  | nil =>
      change HEq (Word.id (Layout.restrict f (r :: tail))).eval
        (Word.id (Layout.restrict f tail)).eval
      exact eval_id_heq
        (by simp only [Layout.restrict_cons, hr, Bool.false_eq_true, ↓reduceIte])
  | cons s rs ih =>
      let u := (Word.frame s (moveHead r rs tail)).restrict f
        (sources_moveHead r rs tail)
      let v := (Word.swap s r (rs ++ tail)).restrict f rfl
      by_cases hs : f s.owner = true
      · have hu : HEq u.eval
            (Word.id (s :: (Layout.restrict f rs ++ Layout.restrict f tail))).eval :=
          ((restrict_frame_true_eval_heq f s (moveHead r rs tail)
            (sources_moveHead r rs tail) hs).trans
            (eval_frame_heq s
              ((moveHead r rs tail).restrict f (sources_moveHead r rs tail))
              (Word.id (Layout.restrict f rs ++ Layout.restrict f tail))
              (by simp only [Layout.restrict_append, Layout.restrict_cons,
                hr, Bool.false_eq_true, ↓reduceIte])
              (by simp only [Layout.restrict_append, Layout.restrict_cons,
                hr, Bool.false_eq_true, ↓reduceIte])
              ih)).trans
                (heq_of_eq (frame_id_eval s (Layout.restrict f rs ++ Layout.restrict f tail)))
        have hv : HEq v.eval
            (Word.id (s :: (Layout.restrict f rs ++ Layout.restrict f tail))).eval :=
          (restrict_swap_true_false_eval_heq f s r (rs ++ tail) hs hr).trans
            (eval_id_heq (congrArg (s :: ·) (Layout.restrict_append f rs tail)))
        have hcomp := eval_comp_heq
          u v (Word.id (s :: (Layout.restrict f rs ++ Layout.restrict f tail)))
          (Word.id (s :: (Layout.restrict f rs ++ Layout.restrict f tail)))
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs, hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs, hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs, hr, Bool.false_eq_true, ↓reduceIte])
          hu hv
        change HEq (u.comp v).eval
          (Word.id (Layout.restrict f (s :: rs) ++ Layout.restrict f tail)).eval
        exact (hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id
          (Word.id (s :: (Layout.restrict f rs ++ Layout.restrict f tail))).eval))).trans
            (eval_id_heq (a := s :: (Layout.restrict f rs ++ Layout.restrict f tail))
              (b := Layout.restrict f (s :: rs) ++ Layout.restrict f tail)
              (by simp only [Layout.restrict_cons, hs, ↓reduceIte, List.cons_append]))
      · have hs' := Bool.eq_false_iff.mpr hs
        have hu : HEq u.eval
            (Word.id (Layout.restrict f rs ++ Layout.restrict f tail)).eval :=
          (restrict_frame_false_eval_heq f s (moveHead r rs tail)
            (sources_moveHead r rs tail) hs').trans ih
        have hv : HEq v.eval
            (Word.id (Layout.restrict f rs ++ Layout.restrict f tail)).eval :=
          (restrict_swap_false_false_eval_heq f s r (rs ++ tail) hs' hr).trans
            (eval_id_heq (Layout.restrict_append f rs tail))
        have hcomp := eval_comp_heq
          u v (Word.id (Layout.restrict f rs ++ Layout.restrict f tail))
          (Word.id (Layout.restrict f rs ++ Layout.restrict f tail))
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_cons, Layout.restrict_append,
            hs', hr, Bool.false_eq_true, ↓reduceIte])
          hu hv
        change HEq (u.comp v).eval
          (Word.id (Layout.restrict f (s :: rs) ++ Layout.restrict f tail)).eval
        exact (hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id
          (Word.id (Layout.restrict f rs ++ Layout.restrict f tail)).eval))).trans
            (eval_id_heq (a := Layout.restrict f rs ++ Layout.restrict f tail)
              (b := Layout.restrict f (s :: rs) ++ Layout.restrict f tail)
              (by simp only [Layout.restrict_cons, hs', Bool.false_eq_true, ↓reduceIte]))

/-- Restricting a register exchange depends only on its selected prefix and
selected tail. The source prefix may contain arbitrary retained registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381 and 409–434. -/
theorem restrict_moveHead_eval_heq_of_restrict_eq (f : P → Bool) (r : Reg P)
    (s s' a a' : Layout P)
    (hs : Layout.restrict f s = Layout.restrict f s')
    (ha : Layout.restrict f a = Layout.restrict f a') :
    HEq ((moveHead r s a).restrict f (sources_moveHead r s a)).eval
      ((moveHead r s' a').restrict f (sources_moveHead r s' a')).eval := by
  by_cases hr : f r.owner = true
  · exact (restrict_moveHead_true_eval_heq f r s a hr).trans
      ((moveHead_eval_heq_of_layouts_eq r hs ha).trans
        (restrict_moveHead_true_eval_heq f r s' a' hr).symm)
  · have hr' := Bool.eq_false_iff.mpr hr
    exact (restrict_moveHead_false_eval_heq f r s a hr').trans
      ((eval_id_heq (congrArg₂ List.append hs ha)).trans
        (restrict_moveHead_false_eval_heq f r s' a' hr').symm)

/-- Moving a register through an erased prefix leaves its retained register
and the retained tail unchanged. The retained tail may be arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_moveHead_eval_heq_id_of_prefix_eq_nil (f : P → Bool) (r : Reg P)
    (rs tail : Layout P) (hrs : Layout.restrict f rs = []) :
    HEq ((moveHead r rs tail).restrict f (sources_moveHead r rs tail)).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict f (r :: tail)))) := by
  by_cases hr : f r.owner = true
  · have h := restrict_moveHead_true_eval_heq f r rs tail hr
    rw [hrs] at h
    exact h.trans (eval_id_heq (a := Layout.restrict f (r :: tail))
      (b := r :: Layout.restrict f tail)
      (by simp only [Layout.restrict_cons, hr, ↓reduceIte])).symm
  · have hr' := Bool.eq_false_iff.mpr hr
    have h := restrict_moveHead_false_eval_heq f r rs tail hr'
    rw [hrs, List.nil_append] at h
    exact h.trans (eval_id_heq (a := Layout.restrict f (r :: tail))
      (b := Layout.restrict f tail)
      (by simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte])).symm

/-- Restricting a block exchange gives the exchange of the retained blocks and
the retained tail. No part of the retained memory is required to be empty.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
409–434 and 565–588. -/
theorem restrict_exchangeBlocks_eval_heq (f : P → Bool) (a b tail : Layout P) :
    HEq ((exchangeBlocks a b tail).restrict f (sources_exchangeBlocks a b tail)).eval
      (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b)
        (Layout.restrict f tail)).eval := by
  induction b with
  | nil =>
      change HEq (Word.id (Layout.restrict f (a ++ tail))).eval
        (Word.id (Layout.restrict f a ++ Layout.restrict f tail)).eval
      exact eval_id_heq (Layout.restrict_append f a tail)
  | cons r b ih =>
      let u := (moveHead r a (b ++ tail)).restrict f
        (sources_moveHead r a (b ++ tail))
      let v := (Word.frame r (exchangeBlocks a b tail)).restrict f
        (sources_exchangeBlocks a b tail)
      by_cases hr : f r.owner = true
      · have hu : HEq u.eval
            (moveHead r (Layout.restrict f a)
              (Layout.restrict f b ++ Layout.restrict f tail)).eval := by
          exact (restrict_moveHead_true_eval_heq f r a (b ++ tail) hr).trans
            (moveHead_eval_heq_of_layouts_eq r
              (rfl : Layout.restrict f a = Layout.restrict f a)
              (Layout.restrict_append f b tail))
        have hv : HEq v.eval
            (Word.frame r (exchangeBlocks (Layout.restrict f a)
              (Layout.restrict f b) (Layout.restrict f tail))).eval :=
          (restrict_frame_true_eval_heq f r (exchangeBlocks a b tail)
            (sources_exchangeBlocks a b tail) hr).trans
            (eval_frame_heq r
              ((exchangeBlocks a b tail).restrict f (sources_exchangeBlocks a b tail))
              (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b)
                (Layout.restrict f tail))
              (by simp only [Layout.restrict_append])
              (by simp only [Layout.restrict_append]) ih)
        have hcomp := eval_comp_heq
          u v (moveHead r (Layout.restrict f a)
            (Layout.restrict f b ++ Layout.restrict f tail))
          (Word.frame r (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b)
            (Layout.restrict f tail)))
          (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, ↓reduceIte])
          (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, ↓reduceIte])
          (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, ↓reduceIte])
          hu hv
        change HEq (u.comp v).eval
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f (r :: b))
            (Layout.restrict f tail)).eval
        exact hcomp.trans (exchangeBlocks_eval_heq_of_layouts_eq
          (rfl : Layout.restrict f a = Layout.restrict f a)
          (b := r :: Layout.restrict f b) (b' := Layout.restrict f (r :: b))
          (by simp only [Layout.restrict_cons, hr, ↓reduceIte])
          (rfl : Layout.restrict f tail = Layout.restrict f tail))
      · have hr' := Bool.eq_false_iff.mpr hr
        have hu : HEq u.eval
            (Word.id (Layout.restrict f a ++
              (Layout.restrict f b ++ Layout.restrict f tail))).eval := by
          exact (restrict_moveHead_false_eval_heq f r a (b ++ tail) hr').trans
            (eval_id_heq (congrArg (Layout.restrict f a ++ ·)
              (Layout.restrict_append f b tail)))
        have hv : HEq v.eval
            (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b)
              (Layout.restrict f tail)).eval :=
          (restrict_frame_false_eval_heq f r (exchangeBlocks a b tail)
            (sources_exchangeBlocks a b tail) hr').trans ih
        have hcomp := eval_comp_heq
          u v (Word.id (Layout.restrict f a ++
            (Layout.restrict f b ++ Layout.restrict f tail)))
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b) (Layout.restrict f tail))
          (by simp only [Layout.restrict_append, Layout.restrict_cons,
            hr', Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_append, Layout.restrict_cons,
            hr', Bool.false_eq_true, ↓reduceIte])
          (by simp only [Layout.restrict_append, Layout.restrict_cons,
            hr', Bool.false_eq_true, ↓reduceIte]) hu hv
        change HEq (u.comp v).eval
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f (r :: b))
            (Layout.restrict f tail)).eval
        exact (hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b)
            (Layout.restrict f tail)).eval))).trans
              (exchangeBlocks_eval_heq_of_layouts_eq
                (rfl : Layout.restrict f a = Layout.restrict f a)
                (b := Layout.restrict f b) (b' := Layout.restrict f (r :: b))
                (by simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte])
                (rfl : Layout.restrict f tail = Layout.restrict f tail))

end TNLean.PEPS.PairEffect.Word
