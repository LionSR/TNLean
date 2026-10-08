/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceGrouping
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Source slots indexed by unordered party pairs

A source inventory with distinct pair labels and complete pair coverage indexes
the unordered pairs of distinct parties exactly once. Consequently, on a finite
party set its length is the binomial coefficient choosing two parties. The
identification retains the actual pair of each source, independent of its vector
or private halfspaces.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, pair slots at lines 233–245 and sample positions at
lines 565–585.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate and thm:compression.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- The actual source-slot index is equivalent to an unordered pair of distinct
parties. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245
and 565–585. -/
def pairIndexEquiv (R : SourceInventory P) (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    Fin R.length ≃ {k : Sym2 P // ¬k.IsDiag} := by
  classical
  exact (finCongr (by simp : R.length = (R.map PairSource.partyPair).length)).trans
    ((List.Nodup.getEquiv _ hN).trans (Equiv.subtypeEquivRight hK))

/-- The equivalence sends each slot to the pair of its actual source.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245. -/
@[simp] theorem pairIndexEquiv_apply (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) (i : Fin R.length) :
    (pairIndexEquiv R hN hK i).val = (R.get i).partyPair := by
  classical
  simp [pairIndexEquiv, List.Nodup.getEquiv]

/-- A complete source inventory has exactly one slot for each choice of two
distinct parties. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 233–245 and 581–585. -/
theorem length_eq_choose [Fintype P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    R.length = (Fintype.card P).choose 2 := by
  classical
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (pairIndexEquiv R hN hK)).trans
      (Sym2.card_subtype_not_diag (α := P))

/-- The number of pair-source slots is at most the square of the number of parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 581–585. -/
theorem length_le_card_sq [Fintype P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    R.length ≤ (Fintype.card P) ^ 2 := by
  rw [length_eq_choose R hN hK]
  exact Nat.choose_le_pow _ _

end TNLean.PEPS.PairEffect.SourceInventory
