/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceLifetimeBound
import TNLean.PEPS.Approximation.SourceSampleChoice

/-!
# Gaussian approximation of an actual source-only circuit

Choose the Schmidt data of all original source occurrences and local branch
labels before any corrected set or Gaussian sample. The circuit's own lifetime,
coefficient and physical-dimension bounds then yield one actual global sample
with the prescribed physical trace-norm error. Private register dimensions are
finite but otherwise arbitrary.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
342–381 and 409–558. This proves the sampling approximation for an actual
source-only circuit; the tensor-network representation and the preceding
elimination of pair effects are separate statements.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation

open Classical in
/-- An actual allowed source-only circuit admits original-source Schmidt data
and an actual Gaussian sample giving physical error at most `ε / 4`. The expected
corrected-term estimates are proved from the circuit resources, not assumed. -/
theorem exists_sourceSample_lifetime_error_le
    {P n x g : Type} [Fintype n] [Fintype x] [Fintype g]
    (physicalDim : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    {a discard : Layout P}
    (w : SourceCircuit a (familyPhysicalLayout physicalDim ps ++ discard))
    (hw : w.IsAllowed) (hfinite : ∀ r ∈ discard, FiniteDimensional ℂ r.space)
    (lifetime : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ j : gateLocations w, ∑ ξ : branchLabels w j, ‖branchCoefficient w j ξ‖ ≤ B)
    (hphysical : ∀ p, (physicalDim p : ℝ≥0) ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (p₀ : Word [] a) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem (familyPhysicalLayout physicalDim ps)))
    (bDiscard : OrthonormalBasis g ℂ (Mem discard)) :
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := sourceSamplingCount (Fintype.card (sourceLocations w)) Q ε
    ∃ (lam : ∀ s : sourceLocations w, branchLabels w s.1 →
        Fin (min (sourceDims w s).1 (sourceDims w s).2) → ℝ)
      (E : ∀ s : sourceLocations w, branchLabels w s.1 →
        Matrix (Fin (sourceDims w s).1) (Fin (min (sourceDims w s).1 (sourceDims w s).2)) ℂ)
      (F : ∀ s : sourceLocations w, branchLabels w s.1 →
        Matrix (Fin (sourceDims w s).2) (Fin (min (sourceDims w s).1 (sourceDims w s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        ambientSchmidtVector (lam s ξ) (E s ξ) (F s ξ) =
          (sourceCoordinates w s ξ).ofLp) ∧
      ∃ ω : SourceGaussianSamples w k,
        let ρ := Matrix.vecMulVec (bIn.repr (p₀.eval 1)).ofLp
          (fun j ↦ conj (bIn.repr (p₀.eval 1) j))
        Matrix.rectangularTraceNorm
          (physicalSourceReplacedDensity (familyPhysicalLayout physicalDim ps) discard w
            (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω) bIn bPhysical bDiscard ρ -
            physicalDensity (familyPhysicalLayout physicalDim ps) discard w
              bIn bPhysical bDiscard ρ) ≤ ε / 4 := by
  intro Q k
  obtain ⟨lam, E, F, hframes, _⟩ := exists_local_schmidt_source_frames w
  refine ⟨lam, E, F, hframes, ?_⟩
  apply exists_sampledSourceMatrix_error_le_of_integral_bound
    (familyPhysicalLayout physicalDim ps) discard w Q ε (by positivity) hε hεone
    lam (fun s ξ ↦ (hframes s ξ).1) E F (fun s ξ ↦ (hframes s ξ).2.2.2.2)
    bIn bPhysical bDiscard
  intro S _
  exact integral_actualCorrectedSourceTerm_le_lifetime physicalDim ps hps hcover w hw
    hfinite lifetime B D hB hD hlifetime hcoeff hphysical S k
    (sourceSamplingCount_pos _ Q ε) lam E F
    (fun s ξ ↦ (hframes s ξ).1) (fun s ξ ↦ (hframes s ξ).2.1)
    (fun s ξ ↦ (hframes s ξ).2.2.1) (fun s ξ ↦ (hframes s ξ).2.2.2.1)
    (fun s ξ ↦ (hframes s ξ).2.2.2.2) p₀ hp₀ hp₀s bIn bPhysical bDiscard

end TNLean.PEPS.PairEffect.SourceCircuit
