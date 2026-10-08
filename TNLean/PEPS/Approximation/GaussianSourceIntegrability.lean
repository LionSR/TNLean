/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianCoefficients
import QICLean.Probability.WeightedSourceError
import QICLean.Probability.MatrixTraceNormIntegrability

/-!
# Integrability of actual Gaussian source contractions

Pairwise second moments of the scalar coefficients imply integrability of the
trace norm of every finite matrix combination. Applying this to the original
source occurrences gives the integrability of each corrected partial branch,
also after any fixed physical projection or partial trace of its coefficient
matrices. No covariance value or operator norm bound is needed here.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 434–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-second-moment.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-gaussiansourceintegrability-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integrable_rectangularTraceNorm_sourceCorrectionSum

-/


noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate



namespace TNLean.PEPS.PairEffect.SourceCircuit
open QICLean.ComplexGaussian

open Classical in
/-- Every matrix combination of the actual corrected-source coefficients has
integrable trace norm under the one global Gaussian law. -/
theorem integrable_rectangularTraceNorm_sourceCorrectionSum {P m n : Type}
    [Fintype m] [Fintype n] {a b : Layout P} (w : SourceCircuit a b)
    (k : ℕ) (hk : 0 < k) (S : Finset (sourceLocations w))
    (ξ ζ : ∀ e : S, branchLabels w e.1.1)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (M : ((∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
      Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2)) ×
      (∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
        Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))) → Matrix m n ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (∑ q, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) • M q)) (sourceGaussianLaw w k) := by
  apply ProbabilityTheory.integrable_rectangularTraceNorm_sum
  intro q r
  exact integrable_sourceCorrection_product_mul_conj w k hk S ξ ζ lam hnonneg
    q.1 r.1 q.2 r.2

end TNLean.PEPS.PairEffect.SourceCircuit
