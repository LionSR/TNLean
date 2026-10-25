/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordRestriction
import TNLean.Lattice.PartyCircuit.WordOwnerMap

/-! # Structural congruences for chronological words

Composition, framing and register exchanges respect the canonical identifications
of equal register lists. These are identities of the constructed words; pair
sources and arbitrary local operators are permitted.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267 and 351–381.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.Word
variable {P : Type}

/-- Composition respects heterogeneous equality of words and equality of their three layouts. -/
theorem comp_heq {a b d a' b' d' : Layout P}
    (ha : a = a') (hb : b = b') (hd : d = d')
    {w : Word a b} {w' : Word a' b'} {v : Word b d} {v' : Word b' d'}
    (hw : HEq w w') (hv : HEq v v') : HEq (Word.comp w v) (Word.comp w' v') := by
  cases ha
  cases hb
  cases hd
  cases hw
  cases hv
  rfl

/-- Framing the same register respects heterogeneous equality of words and their layouts. -/
theorem frame_heq (r : Reg P) {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') {w : Word a b} {w' : Word a' b'}
    (hw : HEq w w') : HEq (Word.frame r w) (Word.frame r w') := by
  cases ha
  cases hb
  cases hw
  rfl

/-- Identity words on equal layouts are heterogeneously equal. -/
theorem id_heq {a b : Layout P} (h : a = b) :
    HEq (Word.id a) (Word.id b) := by
  cases h
  rfl

/-- Exchanging the same two registers beside equal tails gives heterogeneously equal words. -/
theorem swap_heq (r s : Reg P) {t u : Layout P} (h : t = u) :
    HEq (Word.swap r s t) (Word.swap r s u) := by
  cases h
  rfl

/-- Identifying equal input and output layouts preserves the constructed word. -/
theorem castLayouts_heq {a b a' b' : Layout P}
    (w : Word a b) (ha : a = a') (hb : b = b') :
    HEq (w.castLayouts ha hb) w := by
  cases ha
  cases hb
  rfl

/-- Equal constructed words on canonically identified input and output lists
have equal evaluations under these same identifications. This implication
does not pass an equality of complete operators through a restriction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
409–434 and 565–588. -/
theorem eval_heq {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') {w : Word a b} {v : Word a' b'}
    (h : HEq w v) : HEq w.eval v.eval := by
  cases ha
  cases hb
  cases h
  rfl

/-- Relabelling owners commutes with framing by a list of spectator registers,
as an identity of constructed words under the canonical concatenation
identifications. Pair sources and noninjective owner maps are permitted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
409–434 and 565–588. -/
theorem mapOwner_frameList_heq {Q : Type} (f : P → Q) (rs : Layout P)
    {a b : Layout P} (w : Word a b) :
    HEq ((frameList rs w).mapOwner f)
      (frameList (Layout.mapOwner f rs) (w.mapOwner f)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      exact frame_heq ⟨f r.owner, r.space⟩
        (Layout.mapOwner_append f rs a) (Layout.mapOwner_append f rs b) ih

end TNLean.Lattice.PartyCircuit.Word
