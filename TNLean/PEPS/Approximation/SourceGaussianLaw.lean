/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitSchmidtSources
import TNLean.PEPS.Approximation.SourceCompressedDensity
import QICLean.Probability.ComplexGaussian.GlobalBranchLaw

/-!
# Gaussian samples attached to original sources and local labels

Each original source occurrence and ordered pair of its gate's local labels
receives independent samples. These choices precede the selection of corrected
positions or any partial expansion of the circuit.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–340.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-random-source.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.SourceGaussianSamples

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sourceGaussianLaw

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sourceGaussianLawIsProbabilityMeasure

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.measurePreserving_sourceGaussian_eval

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.measurePreserving_selected_sourceGaussian

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sampledSourceMatrix

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-07
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integrable_sampledSourceMatrix

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-08
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integral_sampledSourceMatrix

Provenance-ID: 8769-source-gaussian-sourcegaussianlaw-09
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.exists_unbiased_sampledSourceMatrix

-/

noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The Gaussian sample space retains original source positions and local label pairs.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–340. -/
abbrev SourceGaussianSamples (w : SourceCircuit a b) (k : ℕ) :=
  ∀ e : sourceLocations w, (branchLabels w e.1 × branchLabels w e.1) →
    Sample (Fin k × (Fin (min (sourceDims w e).1 (sourceDims w e).2) ×
      Fin (min (sourceDims w e).1 (sourceDims w e).2)))

/-- One law for all original source occurrences and ordered local label pairs.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–340. -/
def sourceGaussianLaw (w : SourceCircuit a b) (k : ℕ) : Measure (SourceGaussianSamples w k) :=
  globalBranchLaw k
    (fun (e : sourceLocations w) (_ : branchLabels w e.1 × branchLabels w e.1) ↦
      Fin (min (sourceDims w e).1 (sourceDims w e).2))
    (fun (e : sourceLocations w) (_ : branchLabels w e.1 × branchLabels w e.1) ↦
      Fin (min (sourceDims w e).1 (sourceDims w e).2))

/-- The original-source Gaussian law has total mass one. -/
instance sourceGaussianLawIsProbabilityMeasure (w : SourceCircuit a b) (k : ℕ) :
    IsProbabilityMeasure (sourceGaussianLaw w k) :=
  inferInstanceAs (IsProbabilityMeasure (globalBranchLaw k _ _))

/-- Selecting one fixed original occurrence and local label pair has the standard
Gaussian law. No branch is chosen as a function of the random sample.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–340. -/
theorem measurePreserving_sourceGaussian_eval (w : SourceCircuit a b) (k : ℕ)
    (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    MeasurePreserving (fun ω : SourceGaussianSamples w k ↦ ω e (ξ, ζ))
      (sourceGaussianLaw w k)
      (law (Fin k × (Fin (min (sourceDims w e).1 (sourceDims w e).2) ×
        Fin (min (sourceDims w e).1 (sourceDims w e).2)))) := by
  exact (measurePreserving_eval (fun _ : branchLabels w e.1 × branchLabels w e.1 ↦
    law (Fin k × (Fin (min (sourceDims w e).1 (sourceDims w e).2) ×
      Fin (min (sourceDims w e).1 (sourceDims w e).2)))) (ξ, ζ)).comp
    (measurePreserving_eval (fun e : sourceLocations w ↦ independentDensityLaw k
      (fun _ : branchLabels w e.1 × branchLabels w e.1 ↦
        Fin (min (sourceDims w e).1 (sourceDims w e).2))
      (fun _ : branchLabels w e.1 × branchLabels w e.1 ↦
        Fin (min (sourceDims w e).1 (sourceDims w e).2))) e)

/-- Fixed local labels at any prescribed set of original source positions select
independent Gaussian samples. Unselected occurrences and all other labels are integrated out.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem measurePreserving_selected_sourceGaussian (w : SourceCircuit a b) (k : ℕ)
    (S : Finset (sourceLocations w))
    (ξ ζ : ∀ e : S, branchLabels w e.1.1) :
    MeasurePreserving (fun (ω : SourceGaussianSamples w k) (e : S) ↦ ω e.1 (ξ e, ζ e))
      (sourceGaussianLaw w k)
      (independentDensityLaw k
        (fun e : S ↦ Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))
        (fun e : S ↦ Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))) := by
  exact measurePreserving_selectedBranchSamples
    (B := fun e : sourceLocations w ↦ branchLabels w e.1 × branchLabels w e.1)
    (A := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
    (C := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
    k S (fun e ↦ (ξ e, ζ e))

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The sampled ambient operator at an original source and local ket–bra labels.
Its factors are the paper's averaged Gaussian operators; no rank-one condition is imposed.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-random-source`,
`04-compression.tex`, lines 279–309. -/
def sampledSourceMatrix (e : sourceLocations w) (ξ ζ : branchLabels w e.1)
    (ω : SourceGaussianSamples w k) :
    Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
      (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ :=
  ambientSampledSource k (lam e ξ) (lam e ζ)
    (E e ξ) (F e ξ) (E e ζ) (F e ζ) (ω e (ξ, ζ))

/-- Each sampled original-source operator is integrable on the one global law.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–340. -/
theorem integrable_sampledSourceMatrix (hk : 0 < k)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    Integrable (sampledSourceMatrix w k lam E F e ξ ζ) (sourceGaussianLaw w k) := by
  exact (measurePreserving_sourceGaussian_eval w k e ξ ζ).integrable_comp_of_integrable
    (integrable_ambientSampledSource k hk (lam e ξ) (lam e ζ)
      (hnonneg e ξ) (hnonneg e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ))

/-- The mean sampled operator is the exact mixed source matrix, provided the
chosen endpoint frames represent the original source vectors.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-random-source`,
`04-compression.tex`, lines 279–309. -/
theorem integral_sampledSourceMatrix (hk : 0 < k)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω ∂sourceGaussianLaw w k) =
      exactSourceMatrix w e ξ ζ := by
  have hmp := measurePreserving_sourceGaussian_eval w k e ξ ζ
  have hi := integrable_ambientSampledSource k hk (lam e ξ) (lam e ζ)
    (hnonneg e ξ) (hnonneg e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ)
  have hm := hi.aestronglyMeasurable
  rw [← hmp.map_eq] at hm
  have heq := (integral_map hmp.measurable.aemeasurable hm).symm
  rw [hmp.map_eq, integral_ambientSampledSource k hk _ _
    (hnonneg e ξ) (hnonneg e ζ), ambientSchmidtSource, hsource, hsource] at heq
  exact heq

/-- The original normalized sources admit fixed Schmidt frames whose sampled
operators are integrable and have the exact original mixed source matrices as means.
The frames are chosen before any corrected subset or partial branch.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–340. -/
theorem exists_unbiased_sampledSourceMatrix (w : SourceCircuit a b) (k : ℕ) (hk : 0 < k) :
    ∃ (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
        Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
      (E : ∀ e : sourceLocations w, branchLabels w e.1 →
        Matrix (Fin (sourceDims w e).1)
          (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
      (F : ∀ e : sourceLocations w, branchLabels w e.1 →
        Matrix (Fin (sourceDims w e).2)
          (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ),
      (∀ e ξ, (∀ j, 0 ≤ lam e ξ j) ∧ ∑ j, lam e ξ j = 1 ∧
        (E e ξ)ᴴ * E e ξ = 1 ∧ (F e ξ)ᴴ * F e ξ = 1 ∧
        ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
          (sourceCoordinates w e ξ).ofLp) ∧
      ∀ e ξ ζ,
        Integrable (sampledSourceMatrix w k lam E F e ξ ζ) (sourceGaussianLaw w k) ∧
        (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω ∂sourceGaussianLaw w k) =
          exactSourceMatrix w e ξ ζ := by
  obtain ⟨lam, E, F, h, _⟩ := exists_local_schmidt_source_frames w
  refine ⟨lam, E, F, h, ?_⟩
  intro e ξ ζ
  exact ⟨integrable_sampledSourceMatrix w k lam E F hk (fun e ξ ↦ (h e ξ).1) e ξ ζ,
    integral_sampledSourceMatrix w k lam E F hk (fun e ξ ↦ (h e ξ).1)
      (fun e ξ ↦ (h e ξ).2.2.2.2) e ξ ζ⟩

end TNLean.PEPS.PairEffect.SourceCircuit
