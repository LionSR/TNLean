/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Source.PartyMaps

/-!
# The source expansion of a gate in common private spaces

A finite linear combination of allowed source-only words has an exact source
expansion with one common slot basis at each endpoint of every pair of parties.
Each branch source is normalized and each party map is a contraction. The
coefficients are precisely those of the original expansion; the gate itself
need not be a contraction for this identity.

Source: polynomial-PEPS manuscript, September 24, 2026,
`04-compression.tex`, equation `eq:compression-source-gate`, lines 233–267.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

/-- The actual weighted gate has a source expansion in fixed slot bases,
with its original coefficients and with normalized sources and local contractions.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–267. -/
theorem exists_common_source_gate {P ι : Type} [Fintype P] [DecidableEq P] [Fintype ι]
    {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    (c : ι → ℂ) (w : ι → Word X Y) (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ A : ι → ∀ p, Matrix (Y p) (SourceInventory.slotSystem R B X p) ℂ,
          (∀ ξ p, ‖A ξ p‖ ≤ 1) ∧
          ∑ ξ, c ξ • (w ξ).op =
            ∑ ξ, c ξ • (piKronecker (A ξ) * (SourceInventory.prepareSlots R B (η ξ) X).op) := by
  obtain ⟨R, hR, hRK, B, η, hη, A, hA, he⟩ := exists_common_prepared_localOps w hw
  exact ⟨R, hR, hRK, B, η, hη, A, hA, Finset.sum_congr rfl fun ξ _ ↦ by rw [he ξ]⟩

end QuantumCircuit.Party.Word
