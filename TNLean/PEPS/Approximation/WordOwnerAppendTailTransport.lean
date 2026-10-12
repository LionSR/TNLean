/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordAppendTail
import TNLean.PEPS.Approximation.WordOwnerMap

/-!
# Relabelling a composition beside spectator registers

Relabelling owners commutes with adjoining spectator registers as an identity
of the constructed words, under the canonical identifications of concatenated
register lists. Pair sources are permitted, including sources whose endpoints
acquire the same owner. Both constructions use the same relabelled core word.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
variable {P Q : Type}

private theorem comp_word_heq {a b c a' b' c' : Layout Q}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {u : Word a b} {u' : Word a' b'} {v : Word b c} {v' : Word b' c'}
    (hu : HEq u u') (hv : HEq v v') : HEq (u.comp v) (u'.comp v') := by
  cases ha
  cases hb
  cases hc
  cases hu
  cases hv
  rfl

private theorem frame_word_heq (r : Reg Q) {a b a' b' : Layout Q}
    (ha : a = a') (hb : b = b') {u : Word a b} {v : Word a' b'}
    (h : HEq u v) : HEq (Word.frame r u) (Word.frame r v) := by
  cases ha
  cases hb
  cases h
  rfl

private theorem id_word_heq {a b : Layout Q} (h : a = b) :
    HEq (Word.id a) (Word.id b) := by
  cases h
  rfl

private theorem swap_word_heq (r s : Reg Q) {a b : Layout Q} (h : a = b) :
    HEq (Word.swap r s a) (Word.swap r s b) := by
  cases h
  rfl

private theorem castLayouts_word_heq {a b a' b' : Layout Q}
    (w : Word a b) (ha : a = a') (hb : b = b') : HEq (w.castLayouts ha hb) w := by
  cases ha
  cases hb
  rfl

private theorem mapOwner_castLayouts_word_heq (g : P → Q) {a b a' b' : Layout P}
    (w : Word a b) (ha : a = a') (hb : b = b') :
    HEq ((w.castLayouts ha hb).mapOwner g) (w.mapOwner g) := by
  cases ha
  cases hb
  rfl

private theorem mapOwner_frameList_word_heq (g : P → Q) (tail : Layout P)
    {a b : Layout P} (w : Word a b) :
    HEq ((frameList tail w).mapOwner g)
      (frameList (Layout.mapOwner g tail) (w.mapOwner g)) := by
  induction tail with
  | nil => rfl
  | cons r tail ih =>
      exact frame_word_heq ⟨g r.owner, r.space⟩
        (Layout.mapOwner_append g tail a) (Layout.mapOwner_append g tail b) ih

private theorem mapOwner_moveHead_word_heq (g : P → Q) (r : Reg P)
    (rs tail : Layout P) :
    HEq ((moveHead r rs tail).mapOwner g)
      (moveHead ⟨g r.owner, r.space⟩ (Layout.mapOwner g rs) (Layout.mapOwner g tail)) := by
  induction rs with
  | nil => rfl
  | cons s rs ih =>
      let r' : Reg Q := ⟨g r.owner, r.space⟩
      let s' : Reg Q := ⟨g s.owner, s.space⟩
      have hm := frame_word_heq s'
        (Layout.mapOwner_append g rs (r :: tail))
        (congrArg (r' :: ·) (Layout.mapOwner_append g rs tail)) ih
      have hs := swap_word_heq s' r' (Layout.mapOwner_append g rs tail)
      exact comp_word_heq
        (congrArg (s' :: ·) (Layout.mapOwner_append g rs (r :: tail)))
        (congrArg (s' :: ·) (congrArg (r' :: ·) (Layout.mapOwner_append g rs tail)))
        (congrArg (r' :: ·) (congrArg (s' :: ·) (Layout.mapOwner_append g rs tail))) hm hs

private theorem moveHead_tail_word_heq (r : Reg Q) (a : Layout Q)
    {b b' : Layout Q} (h : b = b') : HEq (moveHead r a b) (moveHead r a b') := by
  cases h
  rfl

private theorem mapOwner_exchangeBlocks_word_heq (g : P → Q) (a b tail : Layout P) :
    HEq ((exchangeBlocks a b tail).mapOwner g)
      (exchangeBlocks (Layout.mapOwner g a) (Layout.mapOwner g b)
        (Layout.mapOwner g tail)) := by
  induction b with
  | nil => exact id_word_heq (Layout.mapOwner_append g a tail)
  | cons r b ih =>
      let r' : Reg Q := ⟨g r.owner, r.space⟩
      have hbt := Layout.mapOwner_append g b tail
      have hat := Layout.mapOwner_append g a tail
      have hi := (Layout.mapOwner_append g a (b ++ tail)).trans
        (congrArg (Layout.mapOwner g a ++ ·) hbt)
      have ho := (Layout.mapOwner_append g b (a ++ tail)).trans
        (congrArg (Layout.mapOwner g b ++ ·) hat)
      have hm := (mapOwner_moveHead_word_heq g r a (b ++ tail)).trans
        (moveHead_tail_word_heq r' (Layout.mapOwner g a) hbt)
      have hf := frame_word_heq r' hi ho ih
      exact comp_word_heq
        ((Layout.mapOwner_append g a (r :: (b ++ tail))).trans
          (congrArg (Layout.mapOwner g a ++ ·) (congrArg (r' :: ·) hbt)))
        (congrArg (r' :: ·) hi) (congrArg (r' :: ·) ho) hm hf

private def twoBlockExchange (a b : Layout Q) : Word (a ++ b) (b ++ a) :=
  (exchangeBlocks a b []).castLayouts (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a))

private theorem mapOwner_twoBlockExchange_word_heq (g : P → Q) (a b : Layout P) :
    HEq ((twoBlockExchange a b).mapOwner g)
      (twoBlockExchange (Layout.mapOwner g a) (Layout.mapOwner g b)) := by
  unfold twoBlockExchange
  exact (mapOwner_castLayouts_word_heq g (exchangeBlocks a b []) _ _).trans
    ((mapOwner_exchangeBlocks_word_heq g a b []).trans
      (castLayouts_word_heq (exchangeBlocks (Layout.mapOwner g a) (Layout.mapOwner g b) [])
        (congrArg (Layout.mapOwner g a ++ ·) (List.append_nil (Layout.mapOwner g b)))
        (congrArg (Layout.mapOwner g b ++ ·) (List.append_nil (Layout.mapOwner g a)))).symm)

/-- Relabelling a word extended by spectator registers gives the relabelled
word extended by the relabelled spectators, as an identity of the constructed
words under the canonical concatenation identifications. The owner map and the
pair sources are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
409–434 and 565–588. -/
theorem mapOwner_appendTail_heq (g : P → Q) {a b : Layout P}
    (w : Word a b) (tail : Layout P) :
    HEq ((w.appendTail tail).mapOwner g)
      ((w.mapOwner g).appendTail (Layout.mapOwner g tail)) := by
  have hinner := comp_word_heq
    (Layout.mapOwner_append g tail a) (Layout.mapOwner_append g tail b)
    (Layout.mapOwner_append g b tail)
    (mapOwner_frameList_word_heq g tail w) (mapOwner_twoBlockExchange_word_heq g tail b)
  have houter := comp_word_heq
    (Layout.mapOwner_append g a tail) (Layout.mapOwner_append g tail a)
    (Layout.mapOwner_append g b tail)
    (mapOwner_twoBlockExchange_word_heq g a tail) hinner
  change HEq (((twoBlockExchange a tail).mapOwner g).comp
    (((frameList tail w).mapOwner g).comp ((twoBlockExchange tail b).mapOwner g)))
      ((twoBlockExchange (Layout.mapOwner g a) (Layout.mapOwner g tail)).comp
        ((frameList (Layout.mapOwner g tail) (w.mapOwner g)).comp
          (twoBlockExchange (Layout.mapOwner g tail) (Layout.mapOwner g b))))
  exact houter

end TNLean.PEPS.PairEffect.Word
