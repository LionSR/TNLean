/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordOwnerMap
import TNLean.Lattice.Compression.PartySelector

/-! # Participating parties after pair preparations have been moved to the beginning

Moving pair preparations to the beginning preserves the participating parties of
the remaining word. Relabelling parties sends their finite set to its image,
including when the two endpoints of a pair acquire the same owner. Named scalar
local operations retain their owners in both identities.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–251 and 409–417.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.Word
open TNLean.Lattice.PartyCircuit
variable {P Q : Type}

private theorem parties_castInput {a b c : Layout P} (w : Word a b) (h : a = c) :
    (w.castInput h).parties = w.parties := by
  cases h
  rfl

open Classical in
private theorem owners_subset {a : Layout P} {s : Finset P}
    (h : ∀ r ∈ a, r.owner ∈ s) : (a.map Reg.owner).toFinset ⊆ s := by
  classical
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact h r hr

private theorem owners_sources_mem_parties {a b : Layout P} (w : Word a b) :
    ∀ r ∈ w.sources.layout, r.owner ∈ w.parties := by
  classical
  induction w with
  | id => simp [sources, SourceInventory.layout]
  | comp w v ihw ihv =>
      intro r hr
      rcases List.mem_append.mp (by simpa only [sources,
        SourceInventory.layout_append] using hr) with hr | hr
      · exact Finset.mem_union_right _ (ihv r hr)
      · exact Finset.mem_union_left _ (ihw r hr)
  | localMap => simp [sources, SourceInventory.layout]
  | source hpq U V η tail =>
      intro r hr
      simp only [sources, SourceInventory.layout_cons, SourceInventory.layout_nil,
        List.append_nil, PairSource.layout, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [parties]
  | swap => simp [sources, SourceInventory.layout]
  | frame r w ih => exact fun s hs => Finset.mem_insert_of_mem (ih s hs)

open Classical in
private theorem parties_frameList {a b : Layout P} (w : Word a b) (c : Layout P) :
    (frameList c w).parties = (c.map Reg.owner).toFinset ∪ w.parties := by
  classical
  induction c with
  | nil => simp [frameList]
  | cons r c ih => simp [frameList, parties, ih]

open Classical in
private theorem parties_moveHead (r : Reg P) (c a : Layout P) :
    (moveHead r c a).parties =
      insert r.owner ((c.map Reg.owner).toFinset ∪ (a.map Reg.owner).toFinset) := by
  classical
  induction c with
  | nil => simp [moveHead, parties]
  | cons s c ih =>
      simp [moveHead, parties, ih, List.map_append, Finset.union_comm, Finset.insert_comm]

/-- Moving all original pair preparations to the beginning preserves exactly
the parties of the remaining operations, without a nonvanishing hypothesis.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–251. -/
theorem parties_localPart {a b : Layout P} (w : Word a b) :
    w.localPart.parties = w.parties := by
  classical
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [localPart, parties_castInput, parties, parties_frameList, ihw, ihv]
      rw [Finset.union_assoc, Finset.union_eq_right.mpr ?_]
      exact (owners_subset (owners_sources_mem_parties v)).trans
        Finset.subset_union_right
  | localMap => rfl
  | source hpq U V η tail => simp [localPart, parties, sources, PairSource.layout]
  | swap => rfl
  | @frame r a b w ih =>
      change (moveHead r w.sources.layout a).parties ∪
        insert r.owner w.localPart.parties = insert r.owner w.parties
      rw [parties_moveHead, ih]
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      rw [Finset.union_eq_right.mpr ?_]
      exact Finset.union_subset_iff.mpr
        ⟨owners_subset (owners_sources_mem_parties w),
          owners_subset w.owners_mem_parties.1⟩

open Classical in
/-- An arbitrary relabelling sends the participating parties to their image.
A pair whose endpoints become equal remains a preparation at that named party.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem parties_mapOwner (f : P → Q) {a b : Layout P} (w : Word a b) :
    (w.mapOwner f).parties = w.parties.image f := by
  classical
  induction w with
  | id => exact Layout.owners_mapOwner_image f _
  | comp w v ihw ihv => simp only [mapOwner, parties, ihw, ihv, Finset.image_union]
  | localMap => simp only [mapOwner, parties_castLayouts, parties, Layout.owners_mapOwner_image,
      Finset.image_insert]
  | @source p q hpq U V η tail =>
      by_cases h : f p = f q
      · simp only [mapOwner, dite_true, parties_castLayouts, localPairSource, parties,
          Layout.owners_mapOwner_image, Finset.image_insert, h, Finset.insert_idem]
      · simp only [mapOwner, dite_eq_right h, parties, Layout.owners_mapOwner_image,
          Finset.image_insert]
  | swap => simp only [mapOwner, parties, Layout.owners_mapOwner_image, Finset.image_insert]
  | frame r w ih => simp only [mapOwner, parties, ih, Finset.image_insert]

/-- A party outside the image of the owner map is absent from the remaining
operations after the relabelled pair preparations have been moved to the
beginning. Its restriction acts as the identity on the empty memory.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem restrict_localPart_mapOwner_eval_heq_id_of_disjoint (f : P → Q) (q : Q)
    {a b : Layout P} (w : Word a b) (hf : ∀ p, f p ≠ q) :
    HEq (((w.mapOwner f).localPart.restrict (partySelector q)
      (w.mapOwner f).sources_localPart).eval) (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  have hp : ((w.mapOwner f).localPart.restrict (partySelector q)
      (w.mapOwner f).sources_localPart).parties = ∅ := by
    rw [parties_restrict, parties_localPart, parties_mapOwner]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx, hsel⟩ := Finset.mem_filter.mp hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact hf p (by simpa only [partySelector, decide_eq_true_eq] using hsel)
  exact (eq_nil_and_eval_eq_id_of_parties_eq_empty _ hp).2.2

end TNLean.Lattice.PartyCircuit.Word
