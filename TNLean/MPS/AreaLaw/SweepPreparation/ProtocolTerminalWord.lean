/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolTerminalReference

/-!
# Private realization of the terminal block coordinates

The main registers at each terminal owner are packed into the prescribed block
register. All auxiliary registers retain their labels and owners. At every party this
is a relabelling of its basis on the terminal sheets, so the terminal coordinate map is
realized by one local operation at every party and no gate. The construction also
creates the one-dimensional physical factor at parties with an empty main fibre.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
`prop:sweep`, lines 355–360, and the physical trace in lines 575–583.
This result realizes only the terminal coordinate map, not the preceding sweep.

**Local fix (terminal auxiliary registers):** The physical factors comprise only
main registers. Every auxiliary register remains private at its actual retired
owner, including auxiliary registers at parties without a main block. This
distinction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open Matrix QuantumCircuit.Party
open ManyBody (Config)

variable {L w q : ℕ}

/-- The private circuit packing the actual terminal main fibres and leaving every
auxiliary register at its original owner: at every party, the relabelling of its basis
on the terminal sheets into its physical block register and its auxiliary registers.
The empty main fibres give scalar physical factors.
Source: Part II, `prop:sweep`, lines 355–360. -/
def terminalRegroupingCircuit (L w q : ℕ) :
    OriginalCircuit (stackSystem (Sheet.system q) (terminalFrames L w) fun _ ↦ Unit)
      (physicalSystem (physicalDimension L w q) (privateSystem L w q)) :=
  OriginalCircuit.relabel fun p ↦
    ((terminalPartyEquiv L w q p).trans (localConfigurationEquiv L w q p)).symm

/-- Every operation in the terminal regrouping is private: it has no nonprivate gate.
All parties, including those with scalar physical outputs, are retained.
Source: Part II, `prop:sweep`, lines 355–360. -/
theorem nonprivateCount_terminalRegroupingCircuit :
    (terminalRegroupingCircuit L w q).nonprivateCount = 0 :=
  OriginalCircuit.nonprivateCount_relabel _

/-- The constructed private circuit realizes the specified terminal coordinate
isometry on every input vector, with no product or normalization hypothesis.
Source: Part II, `prop:sweep`, lines 355–360, and Theorem B, lines 575–583. -/
theorem toEuclideanLin_op_terminalRegroupingCircuit
    (Ψ : EuclideanSpace ℂ
      (Config (stackSystem (Sheet.system q) (terminalFrames L w) fun _ ↦ Unit))) :
    toEuclideanLin (terminalRegroupingCircuit L w q).op Ψ =
      terminalRegrouping L w q (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.piCongrRight (terminalPartyEquiv L w q)) Ψ) := by
  rw [terminalRegroupingCircuit, OriginalCircuit.toEuclideanLin_op_relabel]
  ext z
  simp only [terminalRegrouping, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]
  rfl

end TNLean.MPS.AreaLaw.ChainSweep
