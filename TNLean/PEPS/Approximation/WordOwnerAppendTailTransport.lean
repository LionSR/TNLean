/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordAppendTail
import TNLean.Lattice.PartyCircuit.WordOwnerMap
import TNLean.PEPS.Approximation.WordStructuralCongruence

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

private theorem mapOwner_castLayouts_word_heq (g : P → Q) {a b a' b' : Layout P}
    (w : Word a b) (ha : a = a') (hb : b = b') :
    HEq ((w.castLayouts ha hb).mapOwner g) (w.mapOwner g) := by
  rw [mapOwner_castLayouts]
  exact castLayouts_heq _ _ _

private theorem mapOwner_moveHead_word_heq (g : P → Q) (r : Reg P)
    (rs tail : Layout P) :
    HEq ((moveHead r rs tail).mapOwner g)
      (moveHead ⟨g r.owner, r.space⟩ (Layout.mapOwner g rs) (Layout.mapOwner g tail)) := by
  induction rs with
  | nil => rfl
  | cons s rs ih =>
      let r' : Reg Q := ⟨g r.owner, r.space⟩
      let s' : Reg Q := ⟨g s.owner, s.space⟩
      have hm := frame_heq s'
        (Layout.mapOwner_append g rs (r :: tail))
        (congrArg (r' :: ·) (Layout.mapOwner_append g rs tail)) ih
      have hs := swap_heq s' r' (Layout.mapOwner_append g rs tail)
      exact comp_heq
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
  | nil => exact id_heq (Layout.mapOwner_append g a tail)
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
      have hf := frame_heq r' hi ho ih
      exact comp_heq
        ((Layout.mapOwner_append g a (r :: (b ++ tail))).trans
          (congrArg (Layout.mapOwner g a ++ ·) (congrArg (r' :: ·) hbt)))
        (congrArg (r' :: ·) hi) (congrArg (r' :: ·) ho) hm hf

private theorem mapOwner_exchangeTwo_word_heq (g : P → Q) (a b : Layout P) :
    HEq ((exchangeTwo a b).mapOwner g)
      (exchangeTwo (Layout.mapOwner g a) (Layout.mapOwner g b)) := by
  unfold exchangeTwo
  exact (mapOwner_castLayouts_word_heq g (exchangeBlocks a b []) _ _).trans
    ((mapOwner_exchangeBlocks_word_heq g a b []).trans
      (castLayouts_heq (exchangeBlocks (Layout.mapOwner g a) (Layout.mapOwner g b) [])
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
  have hinner := comp_heq
    (Layout.mapOwner_append g tail a) (Layout.mapOwner_append g tail b)
    (Layout.mapOwner_append g b tail)
    (mapOwner_frameList_heq g tail w) (mapOwner_exchangeTwo_word_heq g tail b)
  have houter := comp_heq
    (Layout.mapOwner_append g a tail) (Layout.mapOwner_append g tail a)
    (Layout.mapOwner_append g b tail)
    (mapOwner_exchangeTwo_word_heq g a tail) hinner
  change HEq (((exchangeTwo a tail).mapOwner g).comp
    (((frameList tail w).mapOwner g).comp ((exchangeTwo tail b).mapOwner g)))
      ((exchangeTwo (Layout.mapOwner g a) (Layout.mapOwner g tail)).comp
        ((frameList (Layout.mapOwner g tail) (w.mapOwner g)).comp
          (exchangeTwo (Layout.mapOwner g tail) (Layout.mapOwner g b))))
  exact houter

end TNLean.PEPS.PairEffect.Word
