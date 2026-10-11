/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianPhysicalIntegrability
import TNLean.PEPS.Approximation.SourceSamplingCount

/-!
# An actual sample at the prescribed source count

An explicit integer sample count turns bounds on the expected corrected-term
norms into a choice of the actual global Gaussian sample. Integrability is
derived from the original source law and its actual source vectors.

This is an intermediate implication: the bound on each nonempty corrected set
is stated explicitly as a hypothesis. The analytic argument for the circuit
must supply that bound before applying this result. No estimate for those terms
is assumed to follow merely from the choice of the sample count.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 540–558.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation

open Classical in
/-- If each actual corrected term obeys the stated integral bound, the explicit
source sample count admits an actual Gaussian sample with physical error at most
one quarter of the prescribed accuracy. Integrability is derived, not assumed. -/
theorem exists_sampledSourceMatrix_error_le_of_integral_bound
    {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P)
    (w : SourceCircuit a (physical ++ garbage))
    (Q ε : ℝ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hεone : ε ≤ 1)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ) :
    let k := sourceSamplingCount (Fintype.card (sourceLocations w)) Q ε
    (∀ S : Finset (sourceLocations w), S ≠ ∅ →
      (∫ ω, Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S
        (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ)
        ∂sourceGaussianLaw w k) ≤ Q ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2)) →
    ∃ ω : SourceGaussianSamples w k,
      Matrix.rectangularTraceNorm
        (physicalSourceReplacedDensity physical garbage w
          (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω)
          bIn bPhysical bGarbage ρ -
            physicalDensity physical garbage w bIn bPhysical bGarbage ρ) ≤ ε / 4 := by
  intro k hbound
  obtain ⟨ω, hω⟩ := exists_sampledSourceMatrix_error_le_sum_integral
    physical garbage w k (sourceSamplingCount_pos _ Q ε) lam hnonneg E F hsource
    bIn bPhysical bGarbage ρ
  refine ⟨ω, hω.trans ?_⟩
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        Q ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro S hS
      exact hbound S (Finset.mem_erase.mp hS).1
    _ ≤ ε / 4 := sum_sourceErrorWeights_sourceSamplingCount_le Q ε hQ hε hεone

end TNLean.PEPS.PairEffect.SourceCircuit
