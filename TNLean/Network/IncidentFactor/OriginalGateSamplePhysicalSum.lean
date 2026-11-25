/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.IncidentFactor.IncidentPureSampledPhysicalSum
import TNLean.Network.DistributedContraction.JointSourceSumReindex
import TNLean.Network.DistributedContraction.LocalGateLabelCompatibility
import TNLean.Network.DistributedContraction.ReindexedLocalSourceSamples

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
-/

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
