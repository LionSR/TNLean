/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.EndpointWord
import QICLean.Circuit.Party.Compression.SourceSampling.Samples

/-!
# Local dependence of the actual endpoint samples

Fix independent ket and bra choices. The operation at one party of the sampled endpoint word
uses only the sample indices and Gaussian arrays at sources with an endpoint at that party.
Changing the remaining sample data leaves the operation unchanged. The same sample and ordered
ket–bra array are used at both endpoints of each source throughout this comparison. The
congruence for arbitrary endpoint maps is `SourceInventory.partyOp_endpointWord_congr`.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type}

/-- The operation at one party of the sampled endpoint word depends only on the samples at the
source occurrences with an endpoint at that party. The ket and bra choices are fixed
independently, and no unused sample or branch label is chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and
565–588, pointwise locality of the sampled endpoint factors. -/
theorem partyOp_sampledEndpointWord_eq_of_incident_samples (w : SourceCircuit X Y) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j j' : w.sourceLocations → Fin k) (ω ω' : SourceGaussianSamples w k)
    (p : Option {_p : P // true = true})
    (h : ∀ i : Fin (partialSlots (fun _ : P ↦ true) w).length,
      ((partialSlots (fun _ : P ↦ true) w).get i).left = p ∨
        ((partialSlots (fun _ : P ↦ true) w).get i).right = p →
      j (partialSlotEquiv (fun _ : P ↦ true) w i).1 =
          j' (partialSlotEquiv (fun _ : P ↦ true) w i).1 ∧
        ω (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i) =
          ω' (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i)) :
    let s := fun i ↦ (partialSlotEquiv (fun _ : P ↦ true) w i).1
    let labels := fun i ↦ (partialSlotChoice (fun _ : P ↦ true) w ξ i,
      partialSlotChoice (fun _ : P ↦ true) w ζ i)
    (SourceInventory.endpointWord (blockSystem (affectedOwner fun _ : P ↦ true) fun _ ↦ Unit)
        (partialSlots (fun _ : P ↦ true) w) (partialSlotBases (fun _ : P ↦ true) w)
        (fun i ↦ sampledEndpointLeft w k lam E (s i) (labels i) (j (s i)) ω)
        (fun i ↦ sampledEndpointRight w k lam F (s i) (labels i) (j (s i)) ω)).partyOp p =
      (SourceInventory.endpointWord (blockSystem (affectedOwner fun _ : P ↦ true) fun _ ↦ Unit)
        (partialSlots (fun _ : P ↦ true) w) (partialSlotBases (fun _ : P ↦ true) w)
        (fun i ↦ sampledEndpointLeft w k lam E (s i) (labels i) (j' (s i)) ω')
        (fun i ↦ sampledEndpointRight w k lam F (s i) (labels i) (j' (s i)) ω')).partyOp p := by
  intro s labels
  refine SourceInventory.partyOp_endpointWord_congr _ _ _ p (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · obtain ⟨hj, hω⟩ := h i (Or.inl hi)
    simp only [sampledEndpointLeft, s, labels]
    rw [hj, hω]
  · obtain ⟨hj, hω⟩ := h i (Or.inr hi)
    simp only [sampledEndpointRight, s, labels]
    rw [hj, hω]

end QuantumCircuit.Party.SourceCircuit
