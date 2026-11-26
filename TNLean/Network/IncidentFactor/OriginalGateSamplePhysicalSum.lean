/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.DistributedContraction.SourceSampleAssignmentIndices
import TNLean.Network.DistributedContraction.IncidentGateLabels
import QICLean.Circuit.Party.Compression.SourceSampling.ExteriorFactor
import QICLean.Circuit.Party.Compression.SourceSampling.PhysicalSum
import TNLean.Network.IncidentFactor.IncidentSourceWordComparison
import TNLean.Network.IncidentFactor.IncidentSampledEndpointWord

/-! # The actual physical sum in original distributed indices

The density sum is indexed by the two original gate-label functions and one
common assignment on gate-pair sample positions. Each physical matrix uses
only the two restrictions to its incident gates and the restriction to its
incident sample positions. All original source dimensions and sample arrays
are retained; the exterior readout factor and the exterior scalar are kept
without cancellation.

This is an exact identity for the sampled circuit. No approximation estimate
or bound on its virtual dimensions is asserted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–588.

It also contains the following results.

* `exteriorConfigEquiv`,
  `physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum`
  (in `QuantumCircuit.Party.SourceCircuit`): replacing sampled party factors by their incident
  constructions.
* `QuantumCircuit.Party.SourceCircuit.incidentSampledPhysicalFactor`,
  `QuantumCircuit.Party.SourceCircuit.sampledPhysicalFactor_eq_incidentSampledPhysicalFactor`: the
  sampled physical matrix determined by incident labels.
-/

section IncidentSampledPhysicalFactor

/-!
## The sampled physical matrix determined by incident labels

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

end

end IncidentSampledPhysicalFactor

section IncidentPureSampledPhysicalSum

/-!
## Replacing sampled party factors by their incident constructions

In the sampled physical sum of the source-replaced circuit on a product input, each local factor
of an original party is constructed from the two incident gate-label assignments and the
restriction of the common sample assignment to the slots incident to that party. The outer
branch sums and the joint sample sum remain the original sums, and neither incident labels nor
samples are extended to unrelated positions. The exterior party contributes the partial trace of
its readout as a separate tensor factor, and the exterior scalar is retained without
cancellation.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 351–381 and 565–588.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P]

/-- The configurations of a family of bases on the blocks of all parties: the configuration of
the exterior block and the configurations of the blocks of the original parties. -/
def exteriorConfigEquiv (Phys : Option {_p : P // true = true} → Type) :
    (∀ q, Phys q) ≃ Phys none × ∀ p : P, Phys (some ⟨p, rfl⟩) where
  toFun x := (x none, fun p ↦ x (some ⟨p, rfl⟩))
  invFun y q := match q with
    | none => y.1
    | some p => y.2 p.1
  left_inv x := by
    funext q
    rcases q with _ | ⟨p, hp⟩ <;> rfl
  right_inv _ := rfl

/-- A product of local matrices on the blocks of all parties with a prescribed exterior factor is
that factor times the product over the original parties. -/
private theorem piKronecker_update_none_apply {Phys : Option {_p : P // true = true} → Type}
    (f : ∀ q, Matrix (Phys q) (Phys q) ℂ) (C : Matrix (Phys none) (Phys none) ℂ)
    (x y : ∀ q, Phys q) :
    piKronecker (Function.update f none C) x y =
      C (x none) (y none) * ∏ p : P, f (some ⟨p, rfl⟩) (x (some ⟨p, rfl⟩)) (y (some ⟨p, rfl⟩)) := by
  rw [piKronecker_apply, Fintype.prod_option]
  simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne]
  exact congrArg _ (Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun _ ↦ rfl)) _ _ fun _ ↦ rfl)

variable {X Y : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] {Phys Env : Option {_p : P // true = true} → Type}
  [∀ q, Fintype (Env q)]

/-- **The sampled physical density on a product input is the sum of products of the incident
physical matrices.** For each fixed array of Gaussian samples and every product readout `K` on
the blocks of all parties, the density is `(1/k)^n |emptyGateScalar|²` times the partial trace
`partialTraceRight (K none * (K none)ᴴ)` of the exterior readout, tensored with the double branch
sum of the sample sums of the products over the original parties of the matrices constructed
from the incident labels and incident samples. The sampling coefficient and the exterior scalar
are unchanged, including when they vanish or the original party type is empty. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 351–381 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum
    (K : ∀ q, Matrix (Phys q × Env q) (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ)
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) Phys Env
    let b := blockConfigEquiv (affectedOwner fun _ ↦ true) Y
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let M := fun (ξ ζ : Choices (fun _ ↦ true) w)
      (a : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) (p : P) ↦
      incidentSampledPhysicalFactor K w φ k lam E F p (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ) ω
        (fun i ↦ a ((allSourceSlotEquiv w).symm (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩) (affectedOwner (fun _ ↦ true) t)) w i).1))
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
        ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        reindex (exteriorConfigEquiv Phys).symm (exteriorConfigEquiv Phys).symm
          (partialTraceRight (K none * (K none)ᴴ) ⊗ₖ
            ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
              ∑ a, piKronecker (M ξ ζ a)) := by
  intro e b ψ M
  refine (physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum w K φ k lam E F
    ω).trans (congrArg (_ • ·) ?_)
  ext x y
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, piKronecker_update_none_apply,
    Equiv.symm_symm, exteriorConfigEquiv, Equiv.coe_fn_mk]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦
    Finset.sum_congr rfl fun a _ ↦ ?_
  rw [mul_left_comm, piKronecker_apply]
  refine congrArg (_ * ·) (congrArg (_ * ·) (Finset.prod_congr rfl fun p _ ↦ ?_))
  exact congrFun (congrFun (sampledPhysicalFactor_eq_incidentSampledPhysicalFactor K w φ k lam
    E F p ξ ζ ω a) _) _

end QuantumCircuit.Party.SourceCircuit

end

end IncidentPureSampledPhysicalSum

section OriginalGateSamplePhysicalSum

noncomputable section

open Matrix ManyBody
open scoped Kronecker ComplexConjugate
open TNLean.Network

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
  {Phys Env : Option {_p : P // true = true} → Type} [∀ q, Fintype (Env q)]

open Classical in
/-- The actual sampled physical density is its sum over original gate labels
and common gate-pair samples, with each matrix constructed from incident data.
The ket and bra labels remain independent, and the exterior readout factor and
the exterior scalar are unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_originalGateSampleSum
    (K : ∀ q, Matrix (Phys q × Env q) (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ)
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) Phys Env
    let b := blockConfigEquiv (affectedOwner fun _ ↦ true) Y
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let M := fun (η θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1)
      (j : DistributedOperatorContraction.Sample
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k)
      (p : P) ↦
      incidentSampledPhysicalFactor K w φ k lam E F p
        (DistributedOperatorContraction.restrictGates
          (Finset.univ : Finset w.nonemptyGateLocations)
          (fun g ↦ w.participants g.1) (fun g ↦ w.branchLabels g.1) (fun g ↦ η g.1) p)
        (DistributedOperatorContraction.restrictGates
          (Finset.univ : Finset w.nonemptyGateLocations)
          (fun g ↦ w.participants g.1) (fun g ↦ w.branchLabels g.1) (fun g ↦ θ g.1) p)
        ω
        ((DistributedOperatorContraction.restrictSamples
          (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
          k j p) ∘ partialSlotSampleEquiv w p)
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
        ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        reindex (exteriorConfigEquiv Phys).symm (exteriorConfigEquiv Phys).symm
          (partialTraceRight (K none * (K none)ᴴ) ⊗ₖ
            ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
              ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
                (∏ g : w.nonemptyGateLocations,
                  w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
                  ∑ j : DistributedOperatorContraction.Sample
                      (Finset.univ : Finset w.nonemptyGateLocations)
                      (fun g ↦ w.participants g.1) → Fin k,
                    piKronecker (M η θ j)) := by
  intro e b ψ M
  have h := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum
    K w φ k lam E F ω
  dsimp only at h
  rw [sum_choiceSamples_eq_sum_originalGateSamples] at h
  simpa only [M, originalGateLabelsAtOfAllChoices_eq_restrictGates,
    restrict_reindexedSourceSampleAssignment_eq] using h

end QuantumCircuit.Party.SourceCircuit

end

end OriginalGateSamplePhysicalSum
