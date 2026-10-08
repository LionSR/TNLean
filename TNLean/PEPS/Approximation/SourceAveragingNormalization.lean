/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NonemptyGateLabels
import TNLean.PEPS.Approximation.AllSourceSlots

/-! # Averaging weights of original gate occurrences

Empty-participant occurrences have no source slots. Thus the product of the
averaging weights at the nonempty original occurrences counts exactly the actual
source slots, without requiring a label or a root at an empty occurrence.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 565–588.
-/
noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- An occurrence with no participating party has no source slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 565–588. -/
theorem slotCount_eq_zero_of_not_nonempty {a b : Layout P} (w : SourceCircuit a b)
    (g : w.gateLocations) (h : ¬ (w.participants g).Nonempty) : w.slotCount g = 0 := by
  exact Nat.eq_zero_of_not_pos (fun hn => h
    ⟨(w.endpoints ⟨g, ⟨0, hn⟩⟩).1, (w.endpoints_mem_participants ⟨g, ⟨0, hn⟩⟩).1⟩)
/-- The actual all-party source inventory contains the sum of the original
occurrence slot counts. Source: polynomial-PEPS, `04-compression.tex`, lines 342–355. -/
theorem length_partialSlots_all_eq_sum_slotCount {a b : Layout P}
    (w : SourceCircuit a b) :
    (partialSlots (fun _ : P => true) w).length = ∑ g, w.slotCount g := by
  calc
    _ = Fintype.card w.sourceLocations := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (allSourceSlotEquiv w)
    _ = Fintype.card (Σ g : w.gateLocations, Fin (w.slotCount g)) :=
      Fintype.card_congr (Equiv.refl _)
    _ = _ := by simp only [Fintype.card_sigma, Fintype.card_fin]
/-- Retaining the actual slot index, every source occurrence belongs to a
nonempty original gate. The witness is its recorded left endpoint.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 565–588. -/
def sourceLocationsNonemptyEquiv {a b : Layout P} (w : SourceCircuit a b) :
    w.sourceLocations ≃ Σ g : w.nonemptyGateLocations, Fin (w.slotCount g.1) where
  toFun e := ⟨⟨e.1, ⟨(w.endpoints e).1, (w.endpoints_mem_participants e).1⟩⟩, e.2⟩
  invFun e := ⟨e.1.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Nonempty original occurrences count all the actual source slots; an empty
occurrence contributes no slot. Source: polynomial-PEPS, `04-compression.tex`,
lines 342–355 and 565–588. -/
theorem length_partialSlots_all_eq_sum_nonempty_slotCount {a b : Layout P}
    (w : SourceCircuit a b) :
    (partialSlots (fun _ : P => true) w).length =
      ∑ g : w.nonemptyGateLocations, w.slotCount g.1 := by
  calc
    _ = Fintype.card w.sourceLocations := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (allSourceSlotEquiv w)
    _ = Fintype.card (Σ g : w.nonemptyGateLocations, Fin (w.slotCount g.1)) :=
      Fintype.card_congr (sourceLocationsNonemptyEquiv w)
    _ = _ := by simp only [Fintype.card_sigma, Fintype.card_fin]

/-- Per-gate weights count exactly the actual all-party source slots. This
identity includes zero weights and empty source inventories.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 565–588. -/
theorem prod_sourceSlotWeight_eq {a b : Layout P} (w : SourceCircuit a b) (z : ℂ) :
    (∏ g : w.nonemptyGateLocations, z ^ w.slotCount g.1) =
      z ^ (partialSlots (fun _ : P => true) w).length := by
  classical
  rw [Finset.prod_pow_eq_pow_sum, ← length_partialSlots_all_eq_sum_nonempty_slotCount]
end TNLean.PEPS.PairEffect.SourceCircuit
