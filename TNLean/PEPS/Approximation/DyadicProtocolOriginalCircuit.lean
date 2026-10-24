/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolCompression

/-!
# The chronological operator of a dyadic protocol

Compose the actual changes of a supplied dyadic protocol, then identify its
input and final layouts by the equalities already recorded in the protocol.
At every stage the composite evaluates to the actual trajectory from the
original product input. In particular the final operator gives the actual
final vector, including the retained private registers.

Source: polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`,
lines 25–32 and 48–51, and `07-assembly.tex`, lines 29–36; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation.DyadicProtocol

open TNLean.PEPS.PairEffect

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- The actual chronological composite of the protocol with its original input
and final physical-plus-private layouts.
Source: polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`,
lines 25–32 and 48–51, and `07-assembly.tex`, lines 29–36. -/
noncomputable def originalCircuit : OriginalCircuit
    (ProductInput.wholePartyLayout D.initialSpace)
    (familyPhysicalOutputLayout D.physicalDimension D.physicalOrder D.privateOutput) :=
  (D.chain D.changes).castLayouts D.layout_zero D.layout_changes

/-- The complete original circuit retains the actual final protocol vector;
only the recorded equality of the final register layout is used.
Source: polynomial-PEPS manuscript, `07-assembly.tex`, lines 29–36. -/
theorem eval_originalCircuit :
    D.originalCircuit.eval D.input.vector =
      Layout.memCongr D.layout_changes (D.trajectory D.changes) := by
  have h := D.eval_chain_trajectory D.changes
  rw [show D.trajectory 0 = Layout.memCongr D.layout_zero.symm D.input.vector from rfl] at h
  rw [originalCircuit, OriginalCircuit.eval_castLayouts]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.isoL_apply,
    ← Layout.memCongr_symm] using
    congrArg (Layout.memCongr D.layout_changes) h

end TNLean.PEPS.Approximation.DyadicProtocol
