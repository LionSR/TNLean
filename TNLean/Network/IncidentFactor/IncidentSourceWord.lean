/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Residual
import TNLean.Network.DistributedContraction.IncidentGateLabels

/-!
# The prepared source operation determined by incident labels

The labels at the gates incident to one original party determine the operation of the prepared
source word of the expansion along all parties at that party: the preparation of the product
input followed by the residual of the branch, read at the party. It acts from the bases of the
party in the system of the source slots to the bases of the party in the output system, read on
the blocks of all parties.

The operation is the one of any branch whose labels at the incident gates are the given ones;
`IncidentSourceWordComparison` shows that it does not depend on the labels at the other gates.
Labels at the incident gates that are the restriction of no branch occur only when a gate not
incident to the party has no label; the expansion then has no branch, and the operation is set
to zero.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267, 351–381, 409–434 and 565–588.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The operation at the original party `p` of the prepared source word of the expansion along
all parties, determined by the labels `η` at the gates incident to `p`: the operation of any
branch with these labels, and zero when no branch has them. It acts from the bases of `p` in
the system of the source slots to the bases of `p` in the output system read on the blocks of
all parties. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–381, 409–434 and 565–588. -/
def incidentSourceOp (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (p : P)
    (η : OriginalGateLabelsAt w p) :
    Matrix (blockSystem (affectedOwner fun _ ↦ true) Y (some ⟨p, rfl⟩))
      (allSourceSystem w (some ⟨p, rfl⟩)) ℂ :=
  Function.extend (originalGateLabelsAtOfAllChoices w p)
    (fun ξ ↦ PartyCircuit.partyOp (partialSourceWord w φ ξ) (some ⟨p, rfl⟩)) 0 η

end QuantumCircuit.Party.SourceCircuit
