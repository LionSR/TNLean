/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.IncidentFactor.OriginalGateSamplePhysicalSum
import TNLean.Network.DistributedContraction.SourceSampleCount
import TNLean.Network.DistributedContraction.UnivDensityPairContraction

/-! # The exact distributed contraction of the sampled physical density

At every original nonempty gate occurrence, choose one of its participants
as the root of the shared ordered ket and bra label. The common pair samples
remain attached to their original source occurrences. The physical matrix
at a party is constructed directly from its incident labels and samples.
Each gate's averaging powers appear once in its root coefficient. The squared
modulus of the original empty-gate scalar remains outside the contraction,
and the partial trace of the readout of the exterior block stands beside it
as a separate tensor factor.

This is an exact representation of the sampled circuit. It asserts neither
an approximation error nor a polynomial bound on the virtual dimensions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
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
/-- The actual sampled physical density is the distributed ordered ket and
bra contraction, with gate-owned averaging weights and the exterior scalar
retained multiplicatively, beside the partial trace of the exterior readout.
The root is derived from each gate's recorded participant set; no ambient
nonemptiness or factorization premise is added.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator
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
    let T := fun (p : P) (η θ : OriginalGateLabelsAt w p)
      (j : DistributedOperatorContraction.SampleAt
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p → Fin k) ↦
      incidentSampledPhysicalFactor K w φ k lam E F p η θ ω (j ∘ partialSlotSampleEquiv w p)
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
        ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      (w.emptyGateScalar * conj w.emptyGateScalar) •
        reindex (exteriorConfigEquiv Phys).symm (exteriorConfigEquiv Phys).symm
          (partialTraceRight (K none * (K none)ᴴ) ⊗ₖ
            DistributedOperatorContraction.contractedOperator
              (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
              (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g)
              (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k
              (DistributedOperatorContraction.densityPairCoefficient
                (Gate := w.nonemptyGateLocations)
                (fun g ↦ w.branchLabels g.1) (fun g ↦ w.branchLabels g.1)
                (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
                (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card))
              (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j)) := by
  intro e b ψ T
  -- The network identity is stated with the classical equality test on the parties.
  obtain rfl : ‹DecidableEq P› = fun a b ↦ Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  have hActual := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_originalGateSampleSum
    K w φ k lam E F ω
  dsimp only at hActual
  have hNetwork := DistributedOperatorContraction.contractedOperator_densityPair_univ_eq_double_sum
    (fun g : w.nonemptyGateLocations ↦ w.participants g.1)
    (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g) k
    (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
    (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card) 1 T
  rw [one_smul, mul_one, ← inv_sampleSize_pow_allSourceSlots_eq_prod w k] at hNetwork
  rw [hActual, hNetwork, kronecker_smul, reindex_apply, reindex_apply, submatrix_smul, mul_smul,
    smul_comm]
  rfl

end QuantumCircuit.Party.SourceCircuit
