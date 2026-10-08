/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceCompletion
import TNLean.PEPS.Approximation.PreparedPartyMaps

/-!
# A prepared source on every pair of gate parties

An allowed monomial on a prescribed finite set of gate parties can be written as
a preparation with exactly one normalized source on each unordered pair of distinct
parties, followed by one contraction at each party. Unused pairs are supplied with
one-dimensional sources. Local contractions remove these additional registers, so
the resulting operator is unchanged.

The finite party type is the prescribed participating set of this gate. Common source
spaces across different monomials are a subsequent construction.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, equation `eq:compression-source-gate`, lines 233–251.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-- Prepare exactly one normalized source on every unordered pair of distinct gate
parties, with one-dimensional halves on pairs absent from the monomial, then recover it
by local contractions and exchanges with no sources.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
theorem Word.exists_complete_source_preparation [Finite P] {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (∀ s ∈ S, s.partyPair ∉ w.sources.map PairSource.partyPair →
        Module.finrank ℂ s.leftSpace = 1 ∧ Module.finrank ℂ s.rightSpace = 1) ∧
      ∃ v : Word (S.layout ++ ℓ) ℓ',
        v.IsAllowed ∧ v.sources = [] ∧ w.eval = v.eval ∘L (S.prepare ℓ).eval := by
  obtain ⟨S, hS, hN, hK, v, hv, hvs, he⟩ := w.exists_grouped_source_preparation hw
  obtain ⟨U, hU, hT, hTN, hTK, hE⟩ := SourceInventory.exists_complete_extension S hS hN
  obtain ⟨d, hd, hds, hde⟩ := hE ℓ
  refine ⟨U ++ S, hT, hTN, hTK, ?_, .comp d v, ⟨hd, hv⟩, ?_, ?_⟩
  · intro s hs hks
    rcases List.mem_append.mp hs with hs | hs
    · exact ⟨(hU s hs).1, (hU s hs).2.1⟩
    · exact (hks ((hK s.partyPair).mp (List.mem_map_of_mem hs))).elim
  · simp only [Word.sources, hds, hvs, List.nil_append]
  · rw [Word.eval_comp, comp_assoc, hde, he]

/-- Factor an allowed monomial into normalized preparations on every pair of distinct
gate parties and a tensor product of local contractions in the same party order.
Sources on pairs absent from the monomial have one-dimensional halves.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
theorem Word.exists_complete_prepared_tensorPartyMaps [Fintype P] {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hw : w.IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (∀ s ∈ S, s.partyPair ∉ w.sources.map PairSource.partyPair →
        Module.finrank ℂ s.leftSpace = 1 ∧ Module.finrank ℂ s.rightSpace = 1) ∧
      ∃ B : ∀ p, Mem (Layout.atParty p (S.layout ++ ℓ)) →L[ℂ] Mem (Layout.atParty p ℓ'),
        (∀ p, ‖B p‖ ≤ 1) ∧
        isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L w.eval =
          tensorPartyMaps (S.layout ++ ℓ) ℓ' B ps ∘L
            isoL (groupByPartyIso ps (S.layout ++ ℓ)
              (Finset.nodup_toList _) (by simp [ps])) ∘L (S.prepare ℓ).eval := by
  classical
  dsimp only
  obtain ⟨S, hS, hN, hK, hD, v, hv, hvs, he⟩ := w.exists_complete_source_preparation hw
  obtain ⟨B, hB, hF⟩ := v.exists_tensorPartyMaps hvs hv
    (Finset.univ : Finset P).toList (Finset.nodup_toList _) (by simp)
  refine ⟨S, hS, hN, hK, hD, B, hB, ?_⟩
  rw [he, ← comp_assoc, hF, comp_assoc]

end TNLean.PEPS.PairEffect
