/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairEffectSourcePreparation
import TNLean.PEPS.Approximation.PartyLocalMaps

/-!
# Pair preparations followed by one contraction at each party

For an allowed monomial on a prescribed finite set of gate parties, prepare one normalized
source for each unordered pair occurring among its sources, then apply a tensor product
of local contractions. This factorization uses canonical isometries that group registers
by party. Each source vector and each local map is constructed from the monomial.

Here the finite type of parties is the gate's prescribed participating set. It need not
be the set of all parties in a larger construction. A bound on its cardinality can
therefore be supplied separately for each gate. Common source spaces across different
monomials and one-dimensional sources on unused pairs are subsequent constructions.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, equation `eq:compression-source-gate`, lines 233–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
lem:effects and eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type} [Fintype P]

/-- Prepare and combine the actual pair sources of an allowed monomial on a prescribed
finite party set, then apply one contraction at each party. The set of source pairs is unchanged.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
theorem Word.exists_prepared_tensorPartyMaps {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hw : w.IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ w.sources.map PairSource.partyPair) ∧
      ∃ B : ∀ p, Mem (Layout.atParty p (S.layout ++ ℓ)) →L[ℂ] Mem (Layout.atParty p ℓ'),
        (∀ p, ‖B p‖ ≤ 1) ∧
        isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L w.eval =
          tensorPartyMaps (S.layout ++ ℓ) ℓ' B ps ∘L
            isoL (groupByPartyIso ps (S.layout ++ ℓ)
              (Finset.nodup_toList _) (by simp [ps])) ∘L (S.prepare ℓ).eval := by
  classical
  dsimp only
  obtain ⟨S, hS, hN, hK, v, hv, hvs, he⟩ := w.exists_grouped_source_preparation hw
  obtain ⟨B, hB, hF⟩ := v.exists_tensorPartyMaps hvs hv
    (Finset.univ : Finset P).toList (Finset.nodup_toList _) (by simp)
  refine ⟨S, hS, hN, hK, B, hB, ?_⟩
  rw [he, ← comp_assoc, hF, comp_assoc]

end TNLean.PEPS.PairEffect
