/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.EndpointWord
import QICLean.Circuit.Party.Compression.SourceSampling.Samples
import TNLean.Network.DistributedContraction.IncidentGateLabels

/-!
# Sampled endpoint operations determined by incident labels

Two independent assignments of the labels at the gates incident to one original party, and one
sample index at each source slot with an endpoint at that party, determine the sampled endpoint
operation at the party. At both endpoints of such a slot the same sample index and the same
Gaussian array, indexed by the ordered pair of incident labels, are used; at a slot with no
endpoint at the party the endpoint matrices are identities. The operation is the one at the
party of the endpoint word of the slots of the expansion along all parties.

The sample indices are indexed by the slots of the expansion along the one party, in their
order; no label or sample index at another gate or slot is chosen.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355, 409–434
and 565–588.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type}

omit [Fintype P] in
/-- A party of the original circuit is affected in the expansion along it alone exactly when it
is that party. -/
theorem partySelector_affectedOwner_all_eq_true_iff (p t : P) :
    partySelector (some (⟨p, rfl⟩ : {_p : P // true = true}))
        (affectedOwner (fun _ ↦ true) t) = true ↔ t = p := by
  rw [partySelector_affectedOwner_all_apply, partySelector_eq_true_iff]

/-- A slot of the expansion along all parties is incident to the original party `p` when `p` is
one of the two endpoints of its source position. -/
abbrev IsIncidentSlot (w : SourceCircuit X Y) (p : P)
    (i : Fin (partialSlots (fun _ ↦ true) w).length) : Prop :=
  (w.endpoints (partialSlotEquiv (fun _ ↦ true) w i).1).1 = p ∨
    (w.endpoints (partialSlotEquiv (fun _ ↦ true) w i).1).2 = p

/-- The slot of the expansion along the party `p` alone that carries a slot of the expansion
along all parties with an endpoint at `p`: both enumerate the same source position. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 383–417. -/
def incidentSlot (w : SourceCircuit X Y) (p : P) (i : Fin (partialSlots (fun _ ↦ true) w).length)
    (h : IsIncidentSlot w p i) :
    Fin (partialSlots (fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ ↦ true) t)) w).length :=
  (partialSlotEquiv _ w).symm ⟨(partialSlotEquiv (fun _ ↦ true) w i).1,
    h.imp (fun h ↦ (partySelector_affectedOwner_all_eq_true_iff p _).mpr h)
      (fun h ↦ (partySelector_affectedOwner_all_eq_true_iff p _).mpr h)⟩

/-- The gate of a slot with an endpoint at `p`, as a gate incident to `p`. -/
def incidentSlotGate (w : SourceCircuit X Y) (p : P)
    (i : Fin (partialSlots (fun _ ↦ true) w).length)
    (h : IsIncidentSlot w p i) :
    TNLean.Network.DistributedOperatorContraction.GateAt
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p :=
  have hp : p ∈ w.participants (partialSlotEquiv (fun _ ↦ true) w i).1.1 := h.elim
    (fun h ↦ h ▸ (w.endpoints_mem_participants _).1)
    (fun h ↦ h ▸ (w.endpoints_mem_participants _).2)
  ⟨⟨⟨(partialSlotEquiv (fun _ ↦ true) w i).1.1, ⟨p, hp⟩⟩, Finset.mem_univ _⟩, hp⟩

variable (w : SourceCircuit X Y) (k : ℕ)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- The sampled endpoint operation at the original party `p`, determined by two independent
assignments `η`, `θ` of the labels at the gates incident to `p` and a sample index `j` at each
slot with an endpoint at `p`: the operation at `p` of the endpoint word of the slots of the
expansion along all parties whose endpoint matrices are, at a slot with an endpoint at `p`, the
sampled endpoint matrices of its source position at the labels of `η`, `θ` and the sample index
of `j`, and identities at the other slots. It acts on the bases of `p` in the system of the
source slots. No label, sample index, positivity or normalization outside `p` is used. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355, 409–434 and
565–588. -/
def incidentSampledEndpointOp (p : P) (η θ : OriginalGateLabelsAt w p)
    (j : Fin (partialSlots (fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ ↦ true) t)) w).length → Fin k)
    (ω : SourceGaussianSamples w k) :
    Matrix (allSourceSystem w (some ⟨p, rfl⟩)) (allSourceSystem w (some ⟨p, rfl⟩)) ℂ :=
  PartyCircuit.partyOp (SourceInventory.endpointWord
    (blockSystem (affectedOwner fun _ ↦ true) fun _ ↦ Unit) (partialSlots (fun _ ↦ true) w)
    (partialSlotBases (fun _ ↦ true) w)
    (fun i ↦ if h : IsIncidentSlot w p i then
        sampledEndpointLeft w k lam E (partialSlotEquiv (fun _ ↦ true) w i).1
          (η (incidentSlotGate w p i h), θ (incidentSlotGate w p i h))
          (j (incidentSlot w p i h)) ω
      else 1)
    (fun i ↦ if h : IsIncidentSlot w p i then
        sampledEndpointRight w k lam F (partialSlotEquiv (fun _ ↦ true) w i).1
          (η (incidentSlotGate w p i h), θ (incidentSlotGate w p i h))
          (j (incidentSlot w p i h)) ω
      else 1)) (some ⟨p, rfl⟩)

end QuantumCircuit.Party.SourceCircuit
