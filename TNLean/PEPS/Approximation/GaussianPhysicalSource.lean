/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianCoefficients
import TNLean.PEPS.Approximation.WeightedPhysicalSource

/-!
# Physical source errors under the actual global Gaussian law

Corrected source coordinates retain both independent endpoints at each original
source position. Products of the actual centered source entries supply the
covariance needed by the separated-word estimate. Their endpoint probability
weights are derived from normalized Schmidt probabilities, and the expected
trace error is at most the inverse square root of the sample count to the
number of corrected occurrences. There is no private-dimension factor.

The input frames remain explicit isometric embeddings and need not span the
private memories. Their identification with the original source registers and
initial product vector is a separate result.

Source: polynomial-PEPS Theorem 5.2, `eq:compression-product-covariance` and
`eq:compression-one-choice`, `04-compression.tex`, lines 383–538.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-one-choice.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-gaussianphysicalsource-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integral_rectangularTraceNorm_gaussianPhysicalSource_le

-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped InnerProductSpace TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- Actual global Gaussian source-entry products give the separated physical
error bound. Neither covariance nor a contraction bound on the Gram matrix is
assumed; both are supplied by the proved source law and the allowed words. -/
theorem integral_rectangularTraceNorm_gaussianPhysicalSource_le
    {P₀ : Type} {a₀ b₀ : Layout P₀} (circuit : SourceCircuit a₀ b₀)
    (k : ℕ) (hk : 0 < k) (S : Finset (sourceLocations circuit))
    (ξ ζ : ∀ e : S, branchLabels circuit e.1.1)
    (lam : ∀ e : sourceLocations circuit, branchLabels circuit e.1 →
      Fin (min (sourceDims circuit e).1 (sourceDims circuit e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (hmass : ∀ e ξ, ∑ j, lam e ξ j = 1)
    {P Q X Y T U d e : Type} [Fintype X] [Fintype Y] [Fintype T] [Fintype U]
    [Fintype d] [Fintype e] {a a' b : Layout P} {c c' f : Layout Q}
    {D D' : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup D'] [InnerProductSpace ℂ D']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (CorrectedSchmidtCoordinates circuit S × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (CorrectedSchmidtCoordinates circuit S × U) →ₗᵢ[ℂ] Mem a')
    (bD : OrthonormalBasis d ℂ D) (hv : v.IsAllowed) (hw : w.IsAllowed)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D')
    (v' : Word c f) (w' : Word c' f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (G' : EuclideanSpace ℂ U →ₗᵢ[ℂ] Mem c')
    (bD' : OrthonormalBasis e ℂ D') (hv' : v'.IsAllowed) (hw' : w'.IsAllowed)
    (tau : T → ℝ) (tau' : U → ℝ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    let O := Word.physicalFrameGramMatrix J x y v w F F' bD
    let K := Word.physicalOutputFrameMatrix J' v' G bD'
    let K' := Word.physicalOutputFrameMatrix J' w' G' bD'
    let z := fun (q : CorrectedSchmidtCoordinates circuit S ×
        CorrectedSchmidtCoordinates circuit S) (ω : SourceGaussianSamples circuit k) ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)
    (∫ ω, Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (K * ProbabilityTheory.weightedSourceError tau tau' O (fun q ↦ z q ω) * K'ᴴ))
      ∂sourceGaussianLaw circuit k) ≤ (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro O K K' z
  let : DecidableEq (CorrectedSchmidtCoordinates circuit S) := Classical.decEq _
  let p := pairedProductProbability (fun e : S ↦ lam e.1 (ξ e))
  let p' := pairedProductProbability (fun e : S ↦ lam e.1 (ζ e))
  have hp : ∀ i, 0 ≤ p i :=
    pairedProductProbability_nonneg _ (fun e ↦ hnonneg e.1 (ξ e))
  have hp' : ∀ i, 0 ≤ p' i :=
    pairedProductProbability_nonneg _ (fun e ↦ hnonneg e.1 (ζ e))
  have hpsum := sum_pairedProductProbability_eq_one
    (fun e : S ↦ lam e.1 (ξ e)) (fun e ↦ hmass e.1 (ξ e))
  have hp'sum := sum_pairedProductProbability_eq_one
    (fun e : S ↦ lam e.1 (ζ e)) (fun e ↦ hmass e.1 (ζ e))
  have hpsum' : ∑ i : CorrectedSchmidtCoordinates circuit S, p i = 1 := by
    convert hpsum using 1
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_univ]
    · intro i _
      rfl
  have hp'sum' : ∑ i : CorrectedSchmidtCoordinates circuit S, p' i = 1 := by
    convert hp'sum using 1
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_univ]
    · intro i _
      rfl
  have hz (q r : CorrectedSchmidtCoordinates circuit S ×
      CorrectedSchmidtCoordinates circuit S) :
      Integrable (fun ω ↦ z q ω * conj (z r ω)) (sourceGaussianLaw circuit k) :=
    integrable_sourceCorrection_product_mul_conj circuit k hk S ξ ζ lam hnonneg
      q.1 r.1 q.2 r.2
  have hcov (q r : CorrectedSchmidtCoordinates circuit S ×
      CorrectedSchmidtCoordinates circuit S) :
      (∫ ω, z q ω * conj (z r ω) ∂sourceGaussianLaw circuit k) =
        if q = r then
          (((k : ℝ) ^ (-(S.card : ℝ)) * Real.sqrt (p q.1 * p' q.2) : ℝ) : ℂ)
        else 0 := by
    have hc := integral_sourceCorrection_product_mul_conj circuit k hk S ξ ζ lam hnonneg
      q.1 r.1 q.2 r.2
    by_cases hqr : q = r <;> simpa only [← Prod.ext_iff, hqr, and_self, ↓reduceIte] using hc
  have h := Word.integral_rectangularTraceNorm_weightedPhysicalSource_le
    J x y v w F F' bD hv hw J' v' w' G G' bD' hv' hw'
    (sourceGaussianLaw circuit k) p p' tau tau' z ((k : ℝ) ^ (-(S.card : ℝ)))
    hp hp' htau htau' hpsum' hp'sum' htausum htau'sum
    (Real.rpow_nonneg (Nat.cast_nonneg k) _) hz hcov
  have hpow : Real.sqrt ((k : ℝ) ^ (-(S.card : ℝ))) =
      (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg k)]
    congr 1
    ring
  exact h.trans_eq hpow

end TNLean.PEPS.PairEffect.SourceCircuit
