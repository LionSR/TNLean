/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ApproximateSourceSampling
import TNLean.Lattice.Compression.ActualSampledDistributedContraction
import TNLean.Lattice.Compression.SourceNetworkCoordinateBases

/-!
# Sampled distributed approximation from local gate expansions

The original gate operators are approximated by the recorded local monomial
lists at the prescribed accuracy. The existing sampling estimate for their
rescaled contraction circuit supplies normalized Schmidt data and a Gaussian
sample array. The exact distributed contraction represents its sampled
physical operator with the same total error bound. All local source and
discarded-memory coordinates are chosen from the actual finite registers.

The statement concerns monomial lists supplied at this prescribed accuracy
and the physical error of their actual sampled contraction.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19,
137–175, 199–229, 342–381, 565–588 and 590–600.
-/

noncomputable section
open QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal

namespace TNLean.Lattice.PartyCircuit.EffectCircuit
open TNLean.PEPS.PairEffect

open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P]

/-- The coordinates of an arbitrary selected memory are indexed by its dimension.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19 and 409–434. -/
private abbrev partyMemoryCoordinateIndex {Q : Type} (q : Q) (ℓ : Layout Q) : Type :=
  Fin (Module.finrank ℂ (Mem (Layout.atParty q ℓ)))

/-- The incident physical factor in the canonical coordinates of an arbitrary
source circuit and its original finite discarded registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–579. -/
private def canonicalIncidentSampledPhysicalFactor {a : Layout P}
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (hfinite : ∀ t ∈ garbage, FiniteDimensional ℂ t.space)
    (R : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
    (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Matrix (Fin (R.sourceDims s).1) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
    (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Matrix (Fin (R.sourceDims s).2) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
    (p : P) (η θ : SourceCircuit.OriginalGateLabelsAt R p)
    (ω : SourceCircuit.SourceGaussianSamples R k)
    (j : DistributedOperatorContraction.SampleAt
      (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) p → Fin k) :
    Matrix (Fin (d p)) (Fin (d p)) ℂ :=
  SourceCircuit.incidentSampledPhysicalFactor
    (I := fun q ↦ partyMemoryCoordinateIndex q (R.allResidualSourceLayout ++ []))
    (E := fun q ↦ partyMemoryCoordinateIndex q
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))
    d ps hn hc garbage R ψ k lam E F p η θ ω
    (fun q ↦ R.allResidualSourceBasis q)
    (fun q ↦ SourceCircuit.allPartyDiscardBasis garbage hfinite q)
    (j ∘ (SourceCircuit.partialSlotSampleEquiv R p).toFun)

/-- The exact sampled contraction preserves any trace-norm error bound for
its sampled physical density. This comparison is proved for an arbitrary
source circuit before the approximate circuit is substituted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
private theorem contractedOperator_error_le_of_source_error {a : Layout P}
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (hfinite : ∀ t ∈ garbage, FiniteDimensional ℂ t.space)
    (R : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
    (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Matrix (Fin (R.sourceDims s).1) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
    (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
      Matrix (Fin (R.sourceDims s).2) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
    (ω : SourceCircuit.SourceGaussianSamples R k)
    {n C : Type} [Fintype n] [Fintype C]
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bDiscard : OrthonormalBasis C ℂ (Mem garbage))
    (A : Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ) (ε : ℝ)
    (h : Matrix.rectangularTraceNorm
      (SourceCircuit.physicalSourceReplacedDensity (familyPhysicalLayout d ps) garbage R
        (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω)
        bIn (familyLabelledPhysicalBasis d ps hn hc) bDiscard
        (Matrix.euclideanOuterProduct (bIn.repr ψ.vector) (bIn.repr ψ.vector)) - A) ≤ ε) :
    let T := fun (p : P) (η θ : SourceCircuit.OriginalGateLabelsAt R p)
      (j : DistributedOperatorContraction.SampleAt
        (Finset.univ : Finset R.nonemptyGateLocations)
        (fun g ↦ R.participants g.1) p → Fin k) ↦
      canonicalIncidentSampledPhysicalFactor d ps hn hc garbage hfinite
        R ψ k lam E F p η θ ω j
    Matrix.rectangularTraceNorm
      ((R.emptyGateScalar * conj R.emptyGateScalar) •
          DistributedOperatorContraction.contractedOperator
            (Finset.univ : Finset R.nonemptyGateLocations) (fun g ↦ R.participants g.1)
            (SourceCircuit.sourceGateRoot R) (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
            (DistributedOperatorContraction.densityPairCoefficient
              (Gate := R.nonemptyGateLocations)
              (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
              (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
              (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card))
            (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j) - A) ≤ ε := by
  classical
  intro T
  have hNetwork :=
    SourceCircuit.physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator
      (I := fun q ↦ partyMemoryCoordinateIndex q (R.allResidualSourceLayout ++ []))
      (E := fun q ↦ partyMemoryCoordinateIndex q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))
      d ps hn hc garbage R ψ k lam E F ω
      (fun q ↦ R.allResidualSourceBasis q)
      (fun q ↦ SourceCircuit.allPartyDiscardBasis garbage hfinite q) bIn bDiscard
  dsimp only at hNetwork
  change SourceCircuit.physicalSourceReplacedDensity (familyPhysicalLayout d ps)
    garbage R (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω)
    bIn (familyLabelledPhysicalBasis d ps hn hc) bDiscard
    (Matrix.euclideanOuterProduct (bIn.repr ψ.vector) (bIn.repr ψ.vector)) = _ at hNetwork
  rw [hNetwork] at h
  exact h

/-- Local gate expansions at the prescribed approximation budget give an actual
sampled distributed contraction within physical trace-norm error `ε` of the
original gate operators. The original local approximation hypothesis is
retained; the input and local memory bases are constructed from their original
finite registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19,
137–175, 199–229, 342–381, 565–588 and 590–600. -/
theorem exists_sampled_contractedOperator_approximate_error_le
    (H : P → HSpace) (hH : ∀ p, FiniteDimensional ℂ (H p))
    (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1)
    (physicalDim : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    (priv : Layout P)
    (w : EffectCircuit (ProductInput.wholePartyLayout H)
      (familyPhysicalLayout physicalDim ps ++ priv)) (G : w.GateMaps)
    {r M lifetime : ℕ} (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hb : w.IsExpansionBounded r (B : ℝ)) (hcount : w.expandedGateCount ≤ M)
    (hlifetime : ∀ p, Nat.card {g : w.gateLocations // p ∈ w.participants g} ≤ lifetime)
    (hphysical : ∀ p, (physicalDim p : ℝ≥0) ≤ D)
    (hpriv : ∀ t ∈ priv, FiniteDimensional ℂ t.space.carrier)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (happrox : w.IsGateApproximation (sourceGateBudget (ε / 2) M) G) :
    let ψ := ProductInput.ofAllParties H x hx
    let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) M).le G happrox
    letI := ProductInput.finiteDimensional_wholePartyMem H hH
    let δ := sourceGateBudget ε M
    let m := stackLength r (B : ℝ) δ
    letI := Layout.finiteDimensional_mem_of_registers priv hpriv
    letI := W.produce.finiteDimensional_auxiliary m
    let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε M)
      (familyPhysicalLayout physicalDim ps) priv W.isAllowed_produce
      ((W.isExpansionBounded_produce_iff r (B : ℝ)).mpr
        (w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) M).le G happrox hb))
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := sourceSamplingCount (Fintype.card R.sourceLocations) Q ε
    let garbage := W.produce.auxiliary m ++ priv
    let hfinite := W.produce.finiteDimensional_auxiliary_private_registers m priv hpriv
    ∃ (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
      (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (Fin (R.sourceDims s).1) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
      (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (Fin (R.sourceDims s).2) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        ambientSchmidtVector (lam s ξ) (E s ξ) (F s ξ) =
          (SourceCircuit.sourceCoordinates R s ξ).ofLp) ∧
      ∃ ω : SourceCircuit.SourceGaussianSamples R k,
        let T := fun (p : P) (η θ : SourceCircuit.OriginalGateLabelsAt R p)
          (j : DistributedOperatorContraction.SampleAt
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) p → Fin k) ↦
          canonicalIncidentSampledPhysicalFactor physicalDim ps hps hcover garbage hfinite
            R ψ k lam E F p η θ ω j
        Matrix.rectangularTraceNorm
          ((R.emptyGateScalar * conj R.emptyGateScalar) •
              DistributedOperatorContraction.contractedOperator
                (Finset.univ : Finset R.nonemptyGateLocations) (fun g ↦ R.participants g.1)
                (SourceCircuit.sourceGateRoot R) (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
                (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
                (DistributedOperatorContraction.densityPairCoefficient
                  (Gate := R.nonemptyGateLocations)
                  (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                  (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                  (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card))
                (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j) -
            w.physicalDensityWithGateMaps G
              (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) ψ.vector) ≤ ε := by
  classical
  intro ψ W δ m R Q k garbage hfinite
  let := ProductInput.finiteDimensional_wholePartyMem H hH
  let := Layout.finiteDimensional_mem_of_registers priv hpriv
  let := W.produce.finiteDimensional_auxiliary m
  let bIn := stdOrthonormalBasis ℂ (Mem (ProductInput.wholePartyLayout H)).carrier
  let bDiscard := exchangedGarbageBasis (W.produce.auxiliary m) priv
    (stdOrthonormalBasis ℂ (Mem (W.produce.auxiliary m)).carrier)
    (stdOrthonormalBasis ℂ (Mem priv).carrier)
  obtain ⟨lam, E, F, hframes, ω, hω⟩ :=
    exists_sourceSample_approximate_error_le H hH x hx physicalDim ps hps hcover
      priv w G B D hB hD hb hcount hlifetime hphysical hpriv ε hε hεone happrox
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  intro T
  exact contractedOperator_error_le_of_source_error physicalDim ps hps hcover garbage hfinite
    R ψ k lam E F ω bIn bDiscard
    (w.physicalDensityWithGateMaps G
      (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) ψ.vector) ε hω

end TNLean.Lattice.PartyCircuit.EffectCircuit
