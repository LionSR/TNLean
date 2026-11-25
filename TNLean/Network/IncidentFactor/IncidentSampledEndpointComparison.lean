/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.IncidentFactor.IncidentSampledEndpointWord

/-!
# Comparing the sampled endpoint operation with its incident construction

At one original party, the sampled endpoint word of the expansion along all parties acts as the
operation constructed from the labels at the incident gates and the sample indices at the
incident slots. The operation of an endpoint word at a party reads only the endpoint matrices of
the slots with an endpoint at that party, and there both constructions use the same source
position, the same ket and bra labels, the same sample index and the same Gaussian array.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355, 409–434
and 565–588.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-- A slot whose left endpoint, read on the blocks of all parties, is the block of `p` is
incident to `p`. -/
private theorem isIncidentSlot_of_left (w : SourceCircuit X Y) (p : P)
    (i : Fin (partialSlots (fun _ ↦ true) w).length)
    (h : ((partialSlots (fun _ ↦ true) w).get i).left = some ⟨p, rfl⟩) :
    IsIncidentSlot w p i := by
  rw [(partialSlot_spec _ w i).1, affectedOwner, dite_eq_left rfl] at h
  exact Or.inl (congrArg Subtype.val (Option.some.inj h))

/-- A slot whose right endpoint, read on the blocks of all parties, is the block of `p` is
incident to `p`. -/
private theorem isIncidentSlot_of_right (w : SourceCircuit X Y) (p : P)
    (i : Fin (partialSlots (fun _ ↦ true) w).length)
    (h : ((partialSlots (fun _ ↦ true) w).get i).right = some ⟨p, rfl⟩) :
    IsIncidentSlot w p i := by
  rw [(partialSlot_spec _ w i).2, affectedOwner, dite_eq_left rfl] at h
  exact Or.inr (congrArg Subtype.val (Option.some.inj h))

/-- The slot of the expansion along `p` alone carrying an incident slot enumerates its source
position, so the restricted sample assignment reads the sample index of the slot. -/
private theorem allSourceSlotEquiv_symm_incidentSlot (w : SourceCircuit X Y) (p : P)
    (i : Fin (partialSlots (fun _ ↦ true) w).length) (h : IsIncidentSlot w p i) :
    (allSourceSlotEquiv w).symm (partialSlotEquiv _ w (incidentSlot w p i h)).1 = i := by
  rw [incidentSlot, Equiv.apply_symm_apply, Equiv.symm_apply_eq, allSourceSlotEquiv_apply]

variable [Fintype P] (w : SourceCircuit X Y) (k : ℕ)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- **The sampled endpoint operation at an original party is the operation constructed from its
incident labels and samples.** For two branches `ξ`, `ζ` of the expansion along all parties and
a sample index `a i` at every slot, the endpoint word with the sampled endpoint matrices acts at
`p` as `incidentSampledEndpointOp` at the labels of `ξ`, `ζ` at the gates incident to `p` and
the sample indices at the slots incident to `p`. Empty inventories, sample sets and bases are
included; no positivity, normalization, extension of labels or samples, or factorization is
assumed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355,
409–434 and 565–588. -/
theorem partyOp_sampledEndpointWord_eq_incidentSampledEndpointOp (p : P)
    (ξ ζ : Choices (fun _ ↦ true) w) (a : Fin (partialSlots (fun _ ↦ true) w).length → Fin k)
    (ω : SourceGaussianSamples w k) :
    let s := fun i ↦ (partialSlotEquiv (fun _ ↦ true) w i).1
    let label := fun i ↦
      (partialSlotChoice (fun _ ↦ true) w ξ i, partialSlotChoice (fun _ ↦ true) w ζ i)
    PartyCircuit.partyOp (SourceInventory.endpointWord
        (blockSystem (affectedOwner fun _ ↦ true) fun _ ↦ Unit) (partialSlots (fun _ ↦ true) w)
        (partialSlotBases (fun _ ↦ true) w)
        (fun i ↦ sampledEndpointLeft w k lam E (s i) (label i) (a i) ω)
        (fun i ↦ sampledEndpointRight w k lam F (s i) (label i) (a i) ω)) (some ⟨p, rfl⟩) =
      incidentSampledEndpointOp w k lam E F p (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ a ((allSourceSlotEquiv w).symm (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩) (affectedOwner (fun _ ↦ true) t)) w i).1))
        ω := by
  intro s label
  refine SourceInventory.partyOp_endpointWord_congr _ _ _ _ (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · have h := isIncidentSlot_of_left w p i hi
    refine Eq.trans ?_ (dite_eq_left h).symm
    dsimp only
    rw [allSourceSlotEquiv_symm_incidentSlot w p i h]
    rfl
  · have h := isIncidentSlot_of_right w p i hi
    refine Eq.trans ?_ (dite_eq_left h).symm
    dsimp only
    rw [allSourceSlotEquiv_symm_incidentSlot w p i h]
    rfl

end QuantumCircuit.Party.SourceCircuit
