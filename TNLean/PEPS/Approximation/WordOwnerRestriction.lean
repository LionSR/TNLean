/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartySelector
import TNLean.PEPS.Approximation.WordOwnerMap

/-! # Party restrictions of relabelled source-free words

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P Q : Type}

open Classical in
private theorem owners_mapOwner_image (f : P → Q) (a : Layout P) :
    ((Layout.mapOwner f a).map Reg.owner).toFinset =
      (a.map Reg.owner).toFinset.image f := by
  classical
  ext q
  simp [Layout.mapOwner, List.map_map, Function.comp_def]

open Classical in
/-- Relabelling the owners of a source-free word relabels precisely its
participating parties, including named scalar local maps.
Source: polynomial-PEPS 04-compression.tex, lines 233–251. -/
theorem Word.parties_mapOwner_of_sources_nil (f : P → Q) {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) :
    (w.mapOwner f).parties = w.parties.image f := by
  classical
  induction w with
  | id => exact owners_mapOwner_image f _
  | comp w v ihw ihv =>
      simp only [mapOwner, parties, ihw (List.append_eq_nil_iff.mp hs).2,
        ihv (List.append_eq_nil_iff.mp hs).1, Finset.image_union]
  | localMap =>
      simp only [mapOwner, parties_castLayouts, parties, owners_mapOwner_image,
        Finset.image_insert]
  | source => cases hs
  | swap =>
      simp only [mapOwner, parties, owners_mapOwner_image, Finset.image_insert]
  | frame r w ih =>
      simp only [mapOwner, parties, ih hs, Finset.image_insert]

/-- The actual residual of a gate not incident to a selected party acts as
identity on that party's empty gate memory. No choice of monomial can affect it.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem Word.restrict_mapOwner_eval_eq_id_of_disjoint (f : P → Q) (q : Q)
    {a b : Layout P} (w : Word a b) (hs : w.sources = [])
    (hf : ∀ p, f p ≠ q) :
    let v := (w.mapOwner f).restrict (SourceCircuit.partySelector q)
      (by simp [Word.sources_mapOwner, hs])
    v.parties = ∅ ∧ HEq v.eval (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  dsimp only
  have hp : ((w.mapOwner f).restrict (SourceCircuit.partySelector q)
      (by simp [Word.sources_mapOwner, hs])).parties = ∅ := by
    rw [Word.parties_restrict, Word.parties_mapOwner_of_sources_nil f w hs]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx, hsel⟩ := Finset.mem_filter.mp hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact hf p (by simpa only [SourceCircuit.partySelector, decide_eq_true_eq] using hsel)
  exact ⟨hp, (Word.eq_nil_and_eval_eq_id_of_parties_eq_empty _ hp).2.2⟩

end TNLean.PEPS.PairEffect
