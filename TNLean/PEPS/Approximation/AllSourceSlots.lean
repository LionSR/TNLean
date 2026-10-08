/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialSourcePreparation
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Reindexing the complete source expansion by original occurrences

When all parties are affected, every original source occurrence is retained.
The fixed slot enumeration therefore identifies the nonempty corrected subsets
with the nonempty subsets of original occurrences, including when there are no
sources. No finiteness assumption on the set of parties is needed.

Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-allsourceslots-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.allSourceSlotEquiv

Provenance-ID: 8769-source-corrections-allsourceslots-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.allSourceSlotEquiv_apply

Provenance-ID: 8769-source-corrections-allsourceslots-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sum_nonempty_allSourceSlots

-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- With every party affected, the canonical source slots enumerate all original
source occurrences. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 338–355. -/
def allSourceSlotEquiv {a b : Layout P} (w : SourceCircuit a b) :
    Fin (partialSlots (fun _ : P ↦ true) w).length ≃ sourceLocations w :=
  (partialSlotEquiv (fun _ : P ↦ true) w).trans
    (Equiv.subtypeUnivEquiv (fun _ ↦ Or.inl rfl))

/-- The complete enumeration agrees with the ordered partial-slot enumeration.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
theorem allSourceSlotEquiv_apply {a b : Layout P} (w : SourceCircuit a b)
    (i : Fin (partialSlots (fun _ : P ↦ true) w).length) :
    allSourceSlotEquiv w i = (partialSlotEquiv (fun _ : P ↦ true) w i).1 := rfl

open Classical in
/-- The nonempty-subset correction sum can be indexed by the original source
occurrences instead of the common finite coordinate slots.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–355. -/
theorem sum_nonempty_allSourceSlots {M : Type*} [AddCommMonoid M]
    {a b : Layout P} (w : SourceCircuit a b) (F : Finset (sourceLocations w) → M) :
    (∑ S ∈ (Finset.univ : Finset (Finset
        (Fin (partialSlots (fun _ : P ↦ true) w).length))).erase ∅,
      F (S.map (allSourceSlotEquiv w).toEmbedding)) =
        ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅, F S := by
  apply Finset.sum_equiv (allSourceSlotEquiv w).finsetCongr
  · intro S
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Equiv.finsetCongr_apply]
    exact (not_congr Finset.map_eq_empty).symm
  · intro S hS
    rfl

end TNLean.PEPS.PairEffect.SourceCircuit
