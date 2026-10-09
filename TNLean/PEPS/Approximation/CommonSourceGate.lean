/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonPartyMaps

/-!
# The source expansion of a gate in common private spaces

A finite linear combination of allowed source-only words has an exact source
expansion with one common halfspace at each endpoint of every pair of parties.
Each branch source is normalized and each party map is a contraction. The
coefficients are precisely those of the original expansion; the gate itself
need not be a contraction for this identity.

Source: polynomial-PEPS manuscript, September 24, 2026,
`04-compression.tex`, equation `eq:compression-source-gate`, lines 233–267.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

/-- The actual weighted gate has a source expansion in fixed private spaces,
with its original coefficients and with normalized sources and local contractions.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–267. -/
theorem Word.exists_common_source_gate {P ι : Type} [Fintype P] [Fintype ι]
    {ℓ ℓ' : Layout P} (c : ι → ℂ) (w : ι → Word ℓ ℓ')
    (hw : ∀ ξ, (w ξ).IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ U V : Fin R.length → HSpace, ∃ η : ι → ∀ i, U i ⊗[ℂ] V i,
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ B : ι → ∀ p,
          Mem (Layout.atParty p (SourceInventory.slotLayout R U V ++ ℓ)) →L[ℂ]
            Mem (Layout.atParty p ℓ'),
          (∀ ξ p, ‖B ξ p‖ ≤ 1) ∧
          isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L
              (∑ ξ, c ξ • (w ξ).eval) =
            ∑ ξ, c ξ • (tensorPartyMaps (SourceInventory.slotLayout R U V ++ ℓ) ℓ'
              (B ξ) ps ∘L
                isoL (groupByPartyIso ps (SourceInventory.slotLayout R U V ++ ℓ)
                  (Finset.nodup_toList _) (by simp [ps])) ∘L
                (SourceInventory.prepareSlots R U V (η ξ) ℓ).eval) := by
  classical
  dsimp only
  obtain ⟨R, hR, hRK, U, V, η, hη, B, hB, he⟩ :=
    Word.exists_common_prepared_tensorPartyMaps w hw
  refine ⟨R, hR, hRK, U, V, η, hη, B, hB, ?_⟩
  simp only [comp_finsetSum, comp_smul, he]

end TNLean.PEPS.PairEffect
