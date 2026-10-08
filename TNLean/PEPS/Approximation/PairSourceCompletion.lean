/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.UnitPairSource

/-!
# Completing the set of pair sources

A normalized inventory with distinct unordered pairs can be completed to include
every pair of distinct parties. Each new source has one-dimensional endpoint
spaces. The original inventory is retained as a suffix, and allowed local
operations recover its preparation exactly, uniformly over spectator registers.

Source: polynomial-PEPS manuscript (September 24, 2026),
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251, especially
the one-dimensional sources for unused pairs at lines 243–245.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- Insert scalar sources for the missing non-diagonal pairs in a finite list,
retaining the original inventory as a suffix. Source: polynomial-PEPS manuscript,
`eq:compression-source-gate`, `04-compression.tex`, lines 243–245. -/
private theorem exists_extension_covering (K : List (Sym2 P)) (S : SourceInventory P)
    (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup)
    (hUnit : ∀ k : Sym2 P, ¬ k.IsDiag → ∃ s : PairSource P,
      ‖s.vector‖ = 1 ∧
      (Module.finrank ℂ s.leftSpace = 1 ∧ Module.finrank ℂ s.rightSpace = 1) ∧
      s.partyPair = k ∧ ∀ T : SourceInventory P, Expands (s :: T) T) :
    ∃ U : SourceInventory P,
      (∀ s ∈ U, Module.finrank ℂ s.leftSpace = 1 ∧ Module.finrank ℂ s.rightSpace = 1) ∧
      (U ++ S).IsNormalized ∧ ((U ++ S).map PairSource.partyPair).Nodup ∧
      (∀ k ∈ K, ¬ k.IsDiag → k ∈ (U ++ S).map PairSource.partyPair) ∧
      (U ++ S).Expands S := by
  classical
  induction K with
  | nil => exact ⟨[], by simp, hS, hN, by simp, Expands.refl S⟩
  | cons k K ih =>
      obtain ⟨U, hU, hUS, hUN, hUK, hUE⟩ := ih
      by_cases hk : k.IsDiag ∨ k ∈ (U ++ S).map PairSource.partyPair
      · refine ⟨U, hU, hUS, hUN, ?_, hUE⟩
        exact List.forall_mem_cons.mpr ⟨fun h ↦ hk.resolve_left h, hUK⟩
      · obtain ⟨s, hs, hd, hsk, hE⟩ := hUnit k (fun h ↦ hk (Or.inl h))
        refine ⟨s :: U, List.forall_mem_cons.mpr ⟨hd, hU⟩,
          (isNormalized_cons _ _).mpr ⟨hs, hUS⟩,
          List.nodup_cons.mpr ⟨fun h ↦ hk (Or.inr (hsk ▸ h)), hUN⟩,
          ?_, (hE (U ++ S)).trans hUE⟩
        intro j hj hjd
        exact List.mem_cons.mpr ((List.mem_cons.mp hj).imp
          (fun h ↦ h.trans hsk.symm) (fun h ↦ hUK j h hjd))

/-- Complete a grouped inventory by prepending one-dimensional sources only on
missing pairs. The original source records remain unchanged as the final suffix.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
theorem exists_complete_extension [Finite P] (S : SourceInventory P)
    (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ U : SourceInventory P,
      (∀ s ∈ U, Module.finrank ℂ s.leftSpace = 1 ∧
        Module.finrank ℂ s.rightSpace = 1 ∧ s.partyPair ∉ S.map PairSource.partyPair) ∧
      (U ++ S).IsNormalized ∧ ((U ++ S).map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ (U ++ S).map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (U ++ S).Expands S := by
  classical
  let := Fintype.ofFinite P
  have hUnit : ∀ k : Sym2 P, ¬ k.IsDiag → ∃ s : PairSource P,
      ‖s.vector‖ = 1 ∧
      (Module.finrank ℂ s.leftSpace = 1 ∧ Module.finrank ℂ s.rightSpace = 1) ∧
      s.partyPair = k ∧ ∀ T : SourceInventory P, Expands (s :: T) T := by
    intro k
    induction k using Sym2.inductionOn with
    | hf p q =>
        intro h
        exact ⟨PairSource.unit p q (fun he ↦ h (Sym2.mk_isDiag_iff.mpr he)),
          PairSource.norm_unit_vector _ _ _, PairSource.finrank_unit_spaces _ _ _, rfl,
          Expands.unit_cons _ _ _⟩
  obtain ⟨U, hU, hUS, hUN, hUK, hUE⟩ :=
    exists_extension_covering (Finset.univ : Finset (Sym2 P)).toList S hS hN hUnit
  refine ⟨U, ?_, hUS, hUN, ?_, hUE⟩
  · intro s hs
    exact ⟨(hU s hs).1, (hU s hs).2,
      List.disjoint_left.mp (List.disjoint_of_nodup_append
        (by simpa only [List.map_append] using hUN)) (List.mem_map.mpr ⟨s, hs, rfl⟩)⟩
  · intro k
    refine ⟨?_, hUK k (by simp)⟩
    intro hk h
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hk
    exact s.distinct (Sym2.mk_isDiag_iff.mp h)

/-- Every grouped normalized inventory on finitely many parties admits normalized
sources on exactly all unordered pairs of distinct parties. Allowed source-free
operations recover its original preparation for every spectator layout.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 243–245. -/
theorem exists_complete [Finite P] (S : SourceInventory P)
    (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ T : SourceInventory P, T.IsNormalized ∧ (T.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ T.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧ T.Expands S := by
  obtain ⟨U, _, hUS, hUN, hUK, hUE⟩ := exists_complete_extension S hS hN
  exact ⟨U ++ S, hUS, hUN, hUK, hUE⟩

end TNLean.PEPS.PairEffect.SourceInventory
