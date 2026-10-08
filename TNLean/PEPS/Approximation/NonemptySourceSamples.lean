/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceAveragingNormalization
import TNLean.PEPS.Approximation.SampledSourceNetwork

/-! # Actual source samples on nonempty original gates

Every source slot has two recorded participating endpoints. It therefore lies
at a nonempty original gate, and its unordered endpoint pair is exactly the
corresponding sample edge. No sample or branch label is introduced at an empty
gate occurrence.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 565–588.
-/
noncomputable section
open TNLean.PEPS.Approximation
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} [DecidableEq P] {a b : Layout P}
variable (w : SourceCircuit a b)
local instance : DecidableEq w.nonemptyGateLocations := Classical.decEq _

/-- The exact source-to-sample equivalence on nonempty original occurrences.
Source: polynomial-PEPS, `04-compression.tex`, lines 342–355 and 568–573. -/
def sourceSampleNonemptyEquiv : w.sourceLocations ≃
    DistributedOperatorContraction.Sample (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g => w.participants g.1) where
  toFun e := ⟨⟨⟨e.1, ⟨(w.endpoints e).1, (w.endpoints_mem_participants e).1⟩⟩,
    Finset.mem_univ _⟩, w.sourceSlotPairEquiv e.1 e.2⟩
  invFun s := ⟨s.1.1.1, (w.sourceSlotPairEquiv s.1.1.1).symm s.2⟩
  left_inv := by
    rintro ⟨g, i⟩
    simp only [Equiv.symm_apply_apply]
    rfl
  right_inv := by
    rintro ⟨⟨⟨g, hg⟩, hactive⟩, pair⟩
    simp only [Equiv.apply_symm_apply]

/-- The actual original gate occurrence is unchanged by the sample equivalence.
Source: polynomial-PEPS, `04-compression.tex`, lines 568–573. -/
theorem sourceSampleNonemptyEquiv_gate (e : w.sourceLocations) :
    (w.sourceSampleNonemptyEquiv e).1.1.1 = e.1 := rfl

/-- The endpoint set of the sample edge is exactly the recorded endpoint set.
Source: polynomial-PEPS, `04-compression.tex`, lines 568–573 and 581–588. -/
theorem sourceSampleNonemptyEquiv_parties (e : w.sourceLocations) :
    (w.sourceSampleNonemptyEquiv e).2.val.toFinset =
      {(w.endpoints e).1, (w.endpoints e).2} := by
  exact Sym2.toFinset_mk_eq
end TNLean.PEPS.PairEffect.SourceCircuit
