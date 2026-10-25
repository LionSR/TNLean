/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordOwnerMap
import TNLean.Lattice.Compression.OwnerMemoryTransport
import TNLean.Lattice.Compression.WordStructuralCongruence

/-!
# Restriction after changing owners

Changing owner labels and restricting a source-free composition commute as
identities of the constructed words. Selection before changing owners is by
the inverse image of the new selection. The owner map may merge parties;
local operations retain the same conjugated operator on both constructions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.Word
open ContinuousLinearMap
variable {P Q : Type}

private theorem restrict_castLayouts_word_heq (g : Q → Bool)
    {a b a' b' : Layout Q} (w : Word a b) (ha : a = a') (hb : b = b')
    (hs : w.sources = []) :
    HEq ((w.castLayouts ha hb).restrict g ((sources_castLayouts w ha hb).trans hs))
      (w.restrict g hs) := by
  cases ha
  cases hb
  rfl

private theorem localMap_tail_heq {q : Q} {a b : Layout Q}
    (ha : ∀ r ∈ a, r.owner = q) (hb : ∀ r ∈ b, r.owner = q)
    (A : Mem a →L[ℂ] Mem b) {t t' : Layout Q} (h : t = t') :
    HEq (Word.localMap q ha hb A t) (Word.localMap q ha hb A t') := by
  cases h
  rfl

/-- Restriction after changing owners is the relabelled restriction to the
inverse-image selection, as an identity of source-free chronological words.
No injectivity or finiteness assumption on the owner map is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588. -/
theorem restrict_mapOwner_heq (f : P → Q) (g : Q → Bool) {a b : Layout P}
    (u : Word a b) (hs : u.sources = []) :
    HEq ((u.mapOwner f).restrict g
      (by simp only [sources_mapOwner, hs, SourceInventory.mapOwner_nil]))
      ((u.restrict (fun p ↦ g (f p)) hs).mapOwner f) := by
  induction u with
  | id a => exact id_heq (Layout.restrict_mapOwner f g a)
  | @comp a b c w v ihw ihv =>
      exact comp_heq (Layout.restrict_mapOwner f g a)
        (Layout.restrict_mapOwner f g b) (Layout.restrict_mapOwner f g c)
        (ihw (List.append_eq_nil_iff.mp hs).2) (ihv (List.append_eq_nil_iff.mp hs).1)
  | @localMap p a b ha hb A tail =>
      have hlocal {r : P} {L : Layout P} (hL : ∀ z ∈ L, z.owner = r) :
          ∀ z ∈ Layout.mapOwner f L, z.owner = f r := by
        rintro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        exact congrArg f (hL y hy)
      let hfa := hlocal ha
      let hfb := hlocal hb
      let B := isoL (Layout.mapOwnerIso f b) ∘L A ∘L
        isoL (Layout.mapOwnerIso f a).symm
      let V := Word.localMap (f p) hfa hfb B (Layout.mapOwner f tail)
      have ht := Layout.restrict_mapOwner f g tail
      by_cases hp : g (f p) = true
      · let M := Word.localMap (f p) hfa hfb B
          (Layout.restrict g (Layout.mapOwner f tail))
        let M' := Word.localMap (f p) hfa hfb B
          (Layout.mapOwner f (Layout.restrict (fun r ↦ g (f r)) tail))
        have hleft : HEq
            (((Word.localMap p ha hb A tail).mapOwner f).restrict g
              (by simp only [sources_mapOwner, sources, SourceInventory.mapOwner_nil])) M := by
          change HEq ((V.castLayouts (Layout.mapOwner_append f a tail).symm
            (Layout.mapOwner_append f b tail).symm).restrict g _) M
          refine (restrict_castLayouts_word_heq g V _ _ rfl).trans ?_
          simp only [V, restrict, dite_eq_left hp]
          exact castLayouts_heq _ _ _
        have hright : HEq
            (((Word.localMap p ha hb A tail).restrict (fun r ↦ g (f r)) rfl).mapOwner f)
            M' := by
          simp only [restrict, dite_eq_left hp, mapOwner_castLayouts]
          exact (castLayouts_heq _ _ _).trans (castLayouts_heq _ _ _)
        exact hleft.trans ((localMap_tail_heq hfa hfb B ht).trans hright.symm)
      · have hleft : HEq
            (((Word.localMap p ha hb A tail).mapOwner f).restrict g
              (by simp only [sources_mapOwner, sources, SourceInventory.mapOwner_nil]))
            (Word.id (Layout.restrict g (Layout.mapOwner f tail))) := by
          change HEq ((V.castLayouts (Layout.mapOwner_append f a tail).symm
            (Layout.mapOwner_append f b tail).symm).restrict g _) _
          refine (restrict_castLayouts_word_heq g V _ _ rfl).trans ?_
          simp only [V, restrict, dite_eq_right hp]
          exact castLayouts_heq _ _ _
        have hright : HEq
            (((Word.localMap p ha hb A tail).restrict (fun r ↦ g (f r)) rfl).mapOwner f)
            (Word.id (Layout.mapOwner f (Layout.restrict (fun r ↦ g (f r)) tail))) := by
          simp only [restrict, dite_eq_right hp, mapOwner_castLayouts, mapOwner]
          exact castLayouts_heq _ _ _
        exact hleft.trans ((id_heq ht).trans hright.symm)
  | source => cases hs
  | swap r s tail =>
      let r' : Reg Q := ⟨f r.owner, r.space⟩
      let s' : Reg Q := ⟨f s.owner, s.space⟩
      have ht := Layout.restrict_mapOwner f g tail
      by_cases hr : g (f r.owner) = true
      · by_cases hs' : g (f s.owner) = true
        · simp only [mapOwner, restrict, dite_eq_left hr, dite_eq_left hs',
            mapOwner_castLayouts]
          exact (castLayouts_heq _ _ _).trans
            ((swap_heq r' s' ht).trans (castLayouts_heq _ _ _).symm)
        · simp only [mapOwner, restrict, dite_eq_left hr, dite_eq_right hs',
            mapOwner_castLayouts, Layout.mapOwner_cons]
          exact (castLayouts_heq _ _ _).trans
            ((id_heq (congrArg (r' :: ·) ht)).trans (castLayouts_heq _ _ _).symm)
      · by_cases hs' : g (f s.owner) = true
        · simp only [mapOwner, restrict, dite_eq_right hr, dite_eq_left hs',
            mapOwner_castLayouts, Layout.mapOwner_cons]
          exact (castLayouts_heq _ _ _).trans
            ((id_heq (congrArg (s' :: ·) ht)).trans (castLayouts_heq _ _ _).symm)
        · simp only [mapOwner, restrict, dite_eq_right hr, dite_eq_right hs',
            mapOwner_castLayouts]
          exact (castLayouts_heq _ _ _).trans
            ((id_heq ht).trans (castLayouts_heq _ _ _).symm)
  | @frame r a b w ih =>
      by_cases hr : g (f r.owner) = true
      · simp only [mapOwner, restrict, dite_eq_left hr, mapOwner_castLayouts]
        exact (castLayouts_heq _ _ _).trans
          ((frame_heq ⟨f r.owner, r.space⟩ (Layout.restrict_mapOwner f g a)
            (Layout.restrict_mapOwner f g b) (ih hs)).trans (castLayouts_heq _ _ _).symm)
      · simp only [mapOwner, restrict, dite_eq_right hr, mapOwner_castLayouts]
        exact (castLayouts_heq _ _ _).trans ((ih hs).trans (castLayouts_heq _ _ _).symm)

end TNLean.Lattice.PartyCircuit.Word
