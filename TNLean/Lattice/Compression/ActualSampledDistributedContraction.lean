/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.OriginalGateSamplePhysicalSum
import TNLean.Lattice.Compression.SourceSampleCount
import TNLean.Lattice.Compression.SourceGateRoot
import TNLean.Lattice.Compression.UnivDensityPairContraction

/-! # The exact distributed contraction of the sampled physical density

At every original nonempty gate occurrence, choose one of its participants
as the root of the shared ordered ket and bra label. The common pair samples
remain attached to their original source occurrences. The physical matrix
at a party is constructed directly from its incident labels and samples.
Each gate's averaging powers appear once in its root coefficient. The squared
modulus of the original empty-gate scalar remains outside the contraction.

This is an exact representation of the sampled circuit. It asserts neither
an approximation error nor a polynomial bound on the virtual dimensions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- The actual sampled physical density is the distributed ordered ket and
bra contraction, with gate-owned averaging weights and the exterior scalar
retained multiplicatively. The root is derived from each gate's recorded
participant set; no ambient nonemptiness or factorization premise is added.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator
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
    let T := fun (p : P)
      (η θ : OriginalGateLabelsAt w p)
      (j : DistributedOperatorContraction.SampleAt
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p → Fin k) ↦
      incidentSampledPhysicalFactor (I := I) (E := E)
        d ps hn hc garbage w ψ k lam L R p η θ ω B BG (j ∘ (partialSlotSampleEquiv w p).toFun)
    physicalSourceReplacedDensity (familyPhysicalLayout d ps) garbage w
        (fun e ξ ζ ↦ sampledSourceMatrix w k lam L R e ξ ζ ω)
        bIn (familyLabelledPhysicalBasis d ps hn hc) bRef
        (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
          (fun t ↦ conj (bIn.repr ψ.vector t))) =
      (w.emptyGateScalar * conj w.emptyGateScalar) •
        DistributedOperatorContraction.contractedOperator
          (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
          (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g)
          (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k
          (DistributedOperatorContraction.densityPairCoefficient
            (Gate := w.nonemptyGateLocations)
            (fun g ↦ w.branchLabels g.1) (fun g ↦ w.branchLabels g.1)
            (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
            (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card))
          (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j) := by
  classical
  intro T
  have hActual := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_originalGateSampleSum
    (I := I) (E := E) d ps hn hc garbage w ψ k lam L R ω B BG bIn bRef
  dsimp only at hActual
  have hNetwork := DistributedOperatorContraction.contractedOperator_densityPair_univ_eq_double_sum
    (fun g : w.nonemptyGateLocations ↦ w.participants g.1)
    (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g) k
    (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
    (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card)
    (w.emptyGateScalar * conj w.emptyGateScalar) T
  rw [← inv_sampleSize_pow_allSourceSlots_eq_prod w k] at hNetwork
  exact hActual.trans hNetwork.symm

end TNLean.Lattice.PartyCircuit.SourceCircuit
