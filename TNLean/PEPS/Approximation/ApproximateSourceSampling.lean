/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SampledOriginalCircuit
import TNLean.PEPS.Approximation.ApproximateCircuitResources
import TNLean.PEPS.Approximation.ApproximateCircuitDensity
import TNLean.PEPS.Approximation.FiniteInputMemory

/-!
# An actual sample for approximate original gates

The original gate maps and their approximate monomial lists remain distinct.
Rescaling the latter produces an actual contraction circuit, whose pair effects
are eliminated and whose sources are sampled. The total physical error is the
sum of the proved approximation error and the proved source-replacement error.
The input coordinates are constructed from the original finite party memories.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19,
137–175, 199–229 and 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal
open TNLean.PEPS.Approximation
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P : Type} [Fintype P]

open Classical in
/-- A single actual Gaussian sample approximates the physical density of the
original gate maps. Only their local approximation errors are assumed. The
rescaled gate resources and all Schmidt data are derived, and no bound on any
private dimension is used. -/
theorem exists_sourceSample_approximate_error_le
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
    let bIn := stdOrthonormalBasis ℂ (Mem (ProductInput.wholePartyLayout H)).carrier
    let δ := sourceGateBudget ε M
    let m := stackLength r (B : ℝ) δ
    letI := Layout.finiteDimensional_mem_of_registers priv hpriv
    letI := W.produce.finiteDimensional_auxiliary m
    let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε M)
      (familyPhysicalLayout physicalDim ps) priv W.isAllowed_produce
      ((W.isExpansionBounded_produce_iff r (B : ℝ)).mpr
        (w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) M).le G happrox hb))
    let bPhysical := familyLabelledPhysicalBasis physicalDim ps hps hcover
    let bDiscard := exchangedGarbageBasis (W.produce.auxiliary m) priv
      (stdOrthonormalBasis ℂ (Mem (W.produce.auxiliary m)).carrier)
      (stdOrthonormalBasis ℂ (Mem priv).carrier)
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := sourceSamplingCount (Fintype.card R.sourceLocations) Q ε
    let ρ := Matrix.euclideanOuterProduct (bIn.repr ψ.vector) (bIn.repr ψ.vector)
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
        Matrix.rectangularTraceNorm
          (SourceCircuit.physicalSourceReplacedDensity (familyPhysicalLayout physicalDim ps)
            (W.produce.auxiliary m ++ priv) R
            (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω)
            bIn bPhysical bDiscard ρ -
            w.physicalDensityWithGateMaps G
              (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) ψ.vector) ≤ ε := by
  intro ψ W bIn δ m R bPhysical bDiscard Q k ρ
  have hW :=
    w.isExpansionBounded_rescaledOriginal
      (sourceGateBudget_pos (half_pos hε) M).le G happrox hb
  have hcountW := (w.nonprivateCount_rescaledOriginal
    (sourceGateBudget_pos (half_pos hε) M).le G happrox).trans_le hcount
  have hlifetimeW : ∀ p, W.participationCount p ≤ lifetime := fun p ↦
    (w.participationCount_rescaledOriginal
      (sourceGateBudget_pos (half_pos hε) M).le G happrox p).trans_le (hlifetime p)
  obtain ⟨lam, E, F, hframes, ω, hω⟩ :=
    W.exists_physicalFirst_sourceSample_original_error_le H x hx physicalDim ps hps hcover
      priv B D hB hD hW hcountW hlifetimeW hphysical hpriv ε hε hεone bIn
  let := Layout.finiteDimensional_mem_of_registers priv hpriv
  have hquarter := w.rectangularTraceNorm_rescaledOriginal_density_sub_le_budget G
    (half_pos hε) hcount happrox
    (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) ψ.vector ψ.norm_vector.le
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  let σ₀ := Matrix.partialTraceRight (Matrix.euclideanOuterProduct
    (familyLabelledPhysicalReadout physicalDim ps hps hcover priv (W.eval ψ.vector))
    (familyLabelledPhysicalReadout physicalDim ps hps hcover priv (W.eval ψ.vector)))
  calc
    _ = Matrix.rectangularTraceNorm ((_ - σ₀) + (σ₀ - _)) :=
      congrArg Matrix.rectangularTraceNorm (sub_add_sub_cancel _ _ _).symm
    _ ≤ Matrix.rectangularTraceNorm (_ - σ₀) + Matrix.rectangularTraceNorm (σ₀ - _) :=
      Matrix.rectangularTraceNorm_add_le _ _
    _ ≤ 3 * ε / 4 + ε / 2 / 2 := add_le_add hω hquarter
    _ = ε := by ring

end TNLean.PEPS.PairEffect.EffectCircuit
