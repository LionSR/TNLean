/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentPureSampledPhysicalSum
import TNLean.PEPS.Approximation.JointSourceSumReindex
import TNLean.PEPS.Approximation.LocalGateLabelCompatibility
import TNLean.PEPS.Approximation.ReindexedLocalSourceSamples

/-! # The actual physical sum in original distributed indices

The density sum is indexed by the two original gate-label functions and one
common assignment on gate-pair sample positions. Each physical matrix uses
only the two restrictions to its incident gates and the restriction to its
incident sample positions. All original source dimensions and sample arrays
are retained; the exterior scalar is kept without cancellation.

This is an exact identity for the sampled circuit. No approximation estimate
or bound on its virtual dimensions is asserted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- The actual sampled physical density is its sum over original gate labels
and common gate-pair samples, with each matrix constructed from incident data.
The ket and bra labels remain independent, and the exterior scalar is unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_originalGateSampleSum
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    {n J : Type} [Fintype n] [Fintype J]
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bRef : OrthonormalBasis J ℂ (Mem garbage)) :
    letI : DecidableEq P := Classical.typeDecidableEq P
    let M := fun (η θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1)
      (j : DistributedOperatorContraction.Sample
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k)
      (p : P) ↦
      incidentSampledPhysicalFactor (I := I) (E := E)
        d ps hn hc garbage w ψ k lam L R p
        (DistributedOperatorContraction.restrictGates
          (Finset.univ : Finset w.nonemptyGateLocations)
          (fun g ↦ w.participants g.1) (fun g ↦ w.branchLabels g.1) (fun g ↦ η g.1) p)
        (DistributedOperatorContraction.restrictGates
          (Finset.univ : Finset w.nonemptyGateLocations)
          (fun g ↦ w.participants g.1) (fun g ↦ w.branchLabels g.1) (fun g ↦ θ g.1) p)
        ω B BG
        ((DistributedOperatorContraction.restrictSamples
          (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
          k j p) ∘ (partialSlotSampleEquiv w p).toFun)
    physicalSourceReplacedDensity (familyPhysicalLayout d ps) garbage w
        (fun e ξ ζ ↦ sampledSourceMatrix w k lam L R e ξ ζ ω)
        bIn (familyLabelledPhysicalBasis d ps hn hc) bRef
        (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
          (fun t ↦ conj (bIn.repr ψ.vector t))) =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
          ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
            (∏ g : w.nonemptyGateLocations,
              w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
              ∑ j : DistributedOperatorContraction.Sample
                  (Finset.univ : Finset w.nonemptyGateLocations)
                  (fun g ↦ w.participants g.1) → Fin k,
                dependentPhysicalProductFamilyMatrix (M η θ j) := by
  classical
  intro decEqP M
  have h := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum
    (I := I) (E := E) d ps hn hc garbage w ψ k lam L R ω B BG bIn bRef
  dsimp only at h
  rw [sum_choiceSamples_eq_sum_originalGateSamples] at h
  simpa only [M, originalGateLabelsAtOfAllChoices_eq_restrictGates,
    restrict_reindexedSourceSampleAssignment_eq] using h

end TNLean.PEPS.PairEffect.SourceCircuit
