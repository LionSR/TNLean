/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.PhysicalSum
import TNLean.Network.IncidentFactor.IncidentSourceWordComparison
import TNLean.Network.IncidentFactor.IncidentSampledEndpointComparison

/-!
# The sampled physical matrix determined by incident labels

Two independent assignments of the labels at the gates incident to an original party determine a
local physical matrix: the incident prepared source operations at the ket and bra labels on the
two sides of the incident sampled endpoint operation, read through the readout of the party, with
its environment traced out.

For the labels and samples of branches of the expansion along all parties, this matrix is the
sampled physical factor of the party in the physical sum of the sampled circuit. The comparison
uses the same input, readout, source positions, restricted sample assignment and Gaussian arrays;
no extension of incident labels is chosen.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355, 409–434 and
565–588, especially 574–579.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
  {Phys Env : Option {_p : P // true = true} → Type} [∀ q, Fintype (Env q)]
  (K : ∀ q, Matrix (Phys q × Env q) (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ)
  (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (k : ℕ)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- The local physical matrix at the original party `p` constructed from two independent
assignments `η`, `θ` of the labels at its incident gates and the sample indices `j` at its
incident slots: the incident prepared source operations at `η` and `θ` on the two sides of the
incident sampled endpoint operation, read through the readout `K` of `p`, with the environment
of `p` traced out. No full branch, extension of samples, positivity or normalization is used.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 279–355, 409–434 and
574–579. -/
def incidentSampledPhysicalFactor (p : P) (η θ : OriginalGateLabelsAt w p)
    (ω : SourceGaussianSamples w k)
    (j : Fin (partialSlots (fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ ↦ true) t)) w).length → Fin k) :
    Matrix (Phys (some ⟨p, rfl⟩)) (Phys (some ⟨p, rfl⟩)) ℂ :=
  partialTraceRight (K (some ⟨p, rfl⟩) * (incidentSourceOp w φ p η *
    incidentSampledEndpointOp w k lam E F p η θ j ω * (incidentSourceOp w φ p θ)ᴴ) *
      (K (some ⟨p, rfl⟩))ᴴ)

/-- **At the labels and samples of branches of the expansion along all parties, the incident
physical matrix is the sampled physical factor of the party.** The left side is the factor at
the block of `p` in the sampled physical sum
(`physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum`); the right side reads
only the labels of `ξ` and `ζ` at the gates incident to `p` and the sample indices at the slots
incident to `p`. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588,
especially 574–579. -/
theorem sampledPhysicalFactor_eq_incidentSampledPhysicalFactor (p : P)
    (ξ ζ : Choices (fun _ ↦ true) w) (ω : SourceGaussianSamples w k)
    (a : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) :
    let s := fun i ↦ (partialSlotEquiv (fun _ ↦ true) w i).1
    let label := fun i ↦
      (partialSlotChoice (fun _ ↦ true) w ξ i, partialSlotChoice (fun _ ↦ true) w ζ i)
    let L := fun i ↦ sampledEndpointLeft w k lam E (s i) (label i) (a i) ω
    let M := fun i ↦ sampledEndpointRight w k lam F (s i) (label i) (a i) ω
    partialTraceRight (K (some ⟨p, rfl⟩) *
        (PartyCircuit.partyOp (partialSourceWord w φ ξ) (some ⟨p, rfl⟩) *
          PartyCircuit.partyOp (SourceInventory.endpointWord
            (blockSystem (affectedOwner fun _ ↦ true) fun _ ↦ Unit)
            (partialSlots (fun _ ↦ true) w) (partialSlotBases (fun _ ↦ true) w) L M)
            (some ⟨p, rfl⟩) *
          (PartyCircuit.partyOp (partialSourceWord w φ ζ) (some ⟨p, rfl⟩))ᴴ) *
        (K (some ⟨p, rfl⟩))ᴴ) =
      incidentSampledPhysicalFactor K w φ k lam E F p (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ) ω
        (fun i ↦ a ((allSourceSlotEquiv w).symm (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩) (affectedOwner (fun _ ↦ true) t)) w i).1)) := by
  intro s label L M
  rw [partyOp_partialSourceWord_eq_incidentSourceOp, partyOp_partialSourceWord_eq_incidentSourceOp,
    partyOp_sampledEndpointWord_eq_incidentSampledEndpointOp]
  rfl

end QuantumCircuit.Party.SourceCircuit
