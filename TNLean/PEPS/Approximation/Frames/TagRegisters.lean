/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.SystemUpdate
import TNLean.PEPS.Approximation.EncodedFrame

/-!
# Tag registers of holes

The source has one tag register for every hole of an encoded frame, held by the tag owner of
the hole (`05-frames.tex`, Definition 6.1). This file reads the tags of a list of holes as a
system of the parties: at every party the product of the tag bases of the holes it holds, one
point for every other hole.

* `holeTag h` is the basis of the tag of the hole `h` at its tag owner, and a point at every
  other party; its configurations are the tags of `h` (`holeTagConfigEquiv`).
* `tagSystem l` is the product of the systems `holeTag h` over the holes of `l`; its
  configurations are the tag configurations `TagSpace l` of the encoding
  (`tagConfigEquiv`), and the tags of a concatenation of two lists are the pairs of tags of the
  two lists at every party (`tagSystemAppendEquiv`).

## Main definitions

* `EncodedFrame.holeTag`, `EncodedFrame.tagSystem`.
* `EncodedFrame.holeTagConfigEquiv`, `EncodedFrame.tagConfigEquiv`,
  `EncodedFrame.tagSystemAppendEquiv`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Definition 6.1 `def:frame`,
  `05-frames.tex`, lines 71–82.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody

variable {ι : Type} {q : ℕ} {Party : Type} [DecidableEq Party]

/-! ### Tag registers -/

section Tags

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The tag basis of a hole at every party: the tags of the hole at its tag owner and a single
point elsewhere. Polynomial-PEPS manuscript, Definition 6.1 `def:frame`, `05-frames.tex`,
lines 71–82 (a specified party holds each hole's tag). -/
abbrev holeTag (h : Hole pos q Party) : Party → Type :=
  updateOn (fun _ ↦ Unit) {h.tagOwner} fun _ ↦ h.patch.Tag

instance (h : Hole pos q Party) : Unique {p // p ∈ ({h.tagOwner} : Finset Party)} where
  default := ⟨h.tagOwner, Finset.mem_singleton_self _⟩
  uniq p := Subtype.ext (Finset.mem_singleton.mp p.2)

/-- The configurations of the tag of one hole are its tags. -/
def holeTagConfigEquiv (h : Hole pos q Party) : Config (holeTag h) ≃ h.patch.Tag :=
  (updateOnConfigEquiv _ _ _).trans
    ((Equiv.funUnique _ _).prodCongr (Equiv.ofUnique _ Unit) |>.trans (Equiv.prodPUnit _))

/-- The tag registers of a list of holes: at every party, the product of the tag bases of the
holes of the list in their order. -/
def tagSystem : List (Hole pos q Party) → Party → Type
  | [], _ => Unit
  | h :: l, p => holeTag h p × tagSystem l p

instance instFintypeTagSystem : (l : List (Hole pos q Party)) → (p : Party) →
    Fintype (tagSystem l p)
  | [], _ => inferInstanceAs (Fintype Unit)
  | h :: l, p =>
    haveI := instFintypeTagSystem l p
    inferInstanceAs (Fintype (holeTag h p × tagSystem l p))

instance instDecidableEqTagSystem : (l : List (Hole pos q Party)) → (p : Party) →
    DecidableEq (tagSystem l p)
  | [], _ => inferInstanceAs (DecidableEq Unit)
  | h :: l, p =>
    haveI := instDecidableEqTagSystem l p
    inferInstanceAs (DecidableEq (holeTag h p × tagSystem l p))

/-- **The tags in canonical coordinates.** A configuration of the tag registers of a list of
holes is a tag configuration of the encoding, one tag per hole in the order of the list. -/
def tagConfigEquiv : (l : List (Hole pos q Party)) → Config (tagSystem l) ≃ TagSpace l
  | [] => (Equiv.ofUnique (Party → Unit) Unit :)
  | h :: l => (Equiv.arrowProdEquivProdArrow Party (holeTag h) (tagSystem l)).trans
      ((holeTagConfigEquiv h).prodCongr (tagConfigEquiv l))

/-- The tag registers of a concatenation of two lists of holes are, at every party, the pairs
of tag registers of the two lists. -/
def tagSystemAppendEquiv : (l₁ l₂ : List (Hole pos q Party)) → (p : Party) →
    tagSystem (l₁ ++ l₂) p ≃ tagSystem l₁ p × tagSystem l₂ p
  | [], l₂, p => (Equiv.punitProd (tagSystem l₂ p)).symm
  | h :: l₁, l₂, p =>
    ((Equiv.refl (holeTag h p)).prodCongr (tagSystemAppendEquiv l₁ l₂ p)).trans
      (Equiv.prodAssoc (holeTag h p) (tagSystem l₁ p) (tagSystem l₂ p)).symm

/-- The splitting of the tag registers of a concatenation agrees with that of the tag
configurations. -/
theorem tagAppendEquiv_tagConfigEquiv : (l₁ l₂ : List (Hole pos q Party)) →
    (z : Config (tagSystem (l₁ ++ l₂))) →
      tagAppendEquiv l₁ l₂ (tagConfigEquiv (l₁ ++ l₂) z) =
        (tagConfigEquiv l₁ fun p ↦ (tagSystemAppendEquiv l₁ l₂ p (z p)).1,
          tagConfigEquiv l₂ fun p ↦ (tagSystemAppendEquiv l₁ l₂ p (z p)).2)
  | [], l₂, z => rfl
  | h :: l₁, l₂, z => by
      have ih := tagAppendEquiv_tagConfigEquiv l₁ l₂ fun p ↦ (z p).2
      change ((holeTagConfigEquiv h fun p ↦ (z p).1,
          (tagAppendEquiv l₁ l₂ (tagConfigEquiv (l₁ ++ l₂) fun p ↦ (z p).2)).1),
        (tagAppendEquiv l₁ l₂ (tagConfigEquiv (l₁ ++ l₂) fun p ↦ (z p).2)).2) = _
      rw [ih]
      rfl

end Tags

end TNLean.PEPS.EncodedFrame
