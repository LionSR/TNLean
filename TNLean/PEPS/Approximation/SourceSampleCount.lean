/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceSampleIndices
import TNLean.PEPS.Approximation.AllSourceSlots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The number of original pair samples and their averaging factor

Each original source occurrence contributes one shared sample index. These
indices are counted by summing the numbers of unordered participant pairs
at the original nonempty gate occurrences. Repeated uses of a gate remain
distinct occurrences. The operations with empty participant sets contribute
only to the separate exterior scalar.

The reciprocal sample power is consequently the product of the reciprocal
powers for these occurrences. No cancellation is used, and both zero sample
size and an empty family of gates are permitted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type}

open Classical in
/-- The original ordered source slots are counted by the pair samples at each
original nonempty gate occurrence. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417 and 568–588. -/
theorem length_allSourceSlots_eq_sum_pairSampleLabels {a b : Layout P}
    (w : SourceCircuit a b) :
    (partialSlots (fun _ : P ↦ true) w).length =
      ∑ g : w.nonemptyGateLocations, (pairSampleLabels (w.participants g.1)).card := by
  have hCard := Fintype.card_congr ((allSourceSlotEquiv w).trans (sourceSampleEquiv w))
  rw [Fintype.card_fin] at hCard
  refine hCard.trans ?_
  change Fintype.card (Σ g : {g : w.nonemptyGateLocations // g ∈ Finset.univ},
    {pair // pair ∈ pairSampleLabels (w.participants g.1.1)}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact (Equiv.subtypeUnivEquiv (fun g : w.nonemptyGateLocations ↦
    Finset.mem_univ g)).sum_comp (fun g ↦ (pairSampleLabels (w.participants g.1)).card)

open Classical in
/-- The common sample averaging factor is the product of the averaging factors
at the original nonempty gate occurrences. This includes zero sample size.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–588. -/
theorem inv_sampleSize_pow_allSourceSlots_eq_prod {a b : Layout P}
    (w : SourceCircuit a b) (k : ℕ) :
    (k : ℂ)⁻¹ ^ (partialSlots (fun _ : P ↦ true) w).length =
      ∏ g : w.nonemptyGateLocations,
        (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card := by
  rw [length_allSourceSlots_eq_sum_pairSampleLabels]
  exact (Finset.prod_pow_eq_pow_sum Finset.univ
    (fun g : w.nonemptyGateLocations ↦ (pairSampleLabels (w.participants g.1)).card)
    (k : ℂ)⁻¹).symm

end TNLean.PEPS.PairEffect.SourceCircuit
