/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.IncidentGateLabels
/-! # Incident labels after reindexing all-party choices

The original labels visible at a party agree with restriction of the supplied
label function on nonempty gate occurrences. This identity applies separately
to the ket and bra label functions and retains the original occurrence tags.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–579.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceCircuit

open TNLean.PEPS.Approximation

variable {P : Type}

open Classical in
/-- Recovering an all-party choice from its original gate-label function and
then taking its incident labels gives the restriction of that same function.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–579. -/
theorem originalGateLabelsAtOfAllChoices_eq_restrictGates
    {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (η : (g : w.nonemptyGateLocations) → w.branchLabels g.1) :
    originalGateLabelsAtOfAllChoices w p ((allChoicesNonemptyLabelsEquiv w).symm η) =
      DistributedOperatorContraction.restrictGates
        (Finset.univ : Finset w.nonemptyGateLocations)
        (fun g ↦ w.participants g.1) (fun g ↦ w.branchLabels g.1)
        (fun g : DistributedOperatorContraction.ActiveGate
          (Finset.univ : Finset w.nonemptyGateLocations) ↦ η g.1) p := by
  funext g
  change allChoicesNonemptyLabelsEquiv w
      ((allChoicesNonemptyLabelsEquiv w).symm η) g.1.1 = η g.1.1
  exact congrFun ((allChoicesNonemptyLabelsEquiv w).apply_symm_apply η) g.1.1

end TNLean.PEPS.PairEffect.SourceCircuit
