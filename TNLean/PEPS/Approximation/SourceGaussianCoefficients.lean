/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianDensity

/-!
# Covariance of corrections at original source positions

The coefficients are products of entries of the actual centered Schmidt-space
source operators. Their independent Gaussian law comes from the single global
sample indexed by original occurrences and ordered local labels. The ket and
bra endpoint coordinates are independent summation indices.

Source: polynomial-PEPS Theorem 5.2, `eq:compression-product-covariance`,
`04-compression.tex`, lines 338–407.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-product-covariance.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-gaussian-sourcegaussiancoefficients-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sourceCorrection_product_eq_selected

Provenance-ID: 8769-source-gaussian-sourcegaussiancoefficients-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integrable_sourceCorrection_product_mul_conj

Provenance-ID: 8769-source-gaussian-sourcegaussiancoefficients-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integral_sourceCorrection_product_mul_conj

Provenance-ID: 8769-source-gaussian-sourcegaussiancoefficients-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integral_sourceCorrection_product_eq_zero

-/

noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}
  (w : SourceCircuit a b) (k : ℕ) (hk : 0 < k)
  (S : Finset (sourceLocations w))
  (ξ ζ : ∀ e : S, branchLabels w e.1.1)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
  (i i' l l' : ∀ e : S,
    Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
      Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))

include hk hnonneg in
/-- Products of actual centered source entries are the selected Gaussian coefficients
for the same original positions and deterministic local labels.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–407. -/
theorem sourceCorrection_product_eq_selected (ω : SourceGaussianSamples w k) :
    (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
      (ω e.1 (ξ e, ζ e)) (i e) (l e)) =
      selectedBranchDensityCoefficient
        (A := fun (e : sourceLocations w) (_ : branchLabels w e.1 × branchLabels w e.1) ↦
          Fin (min (sourceDims w e).1 (sourceDims w e).2))
        (C := fun (e : sourceLocations w) (_ : branchLabels w e.1 × branchLabels w e.1) ↦
          Fin (min (sourceDims w e).1 (sourceDims w e).2))
        k S (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e))
        i l ω := by
  apply Finset.prod_congr rfl
  intro e _
  exact sourceCorrection_apply k hk _ _ (hnonneg e.1 (ξ e)) (hnonneg e.1 (ζ e)) _ _ _

include hk hnonneg in
/-- The conjugate product of any two actual corrected-source coefficients is
integrable under the one global law.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-product-covariance`. -/
theorem integrable_sourceCorrection_product_mul_conj :
    Integrable (fun ω : SourceGaussianSamples w k ↦
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) *
      conj (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i' e) (l' e))) (sourceGaussianLaw w k) := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integrable_selectedBranchDensityCoefficient_mul_conj
    (B := fun e : sourceLocations w ↦ branchLabels w e.1 × branchLabels w e.1)
    (A := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
    (C := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2)) k S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i i' l l'

include hk hnonneg in
open Classical in
/-- The covariance of the actual corrected-source entry products is diagonal,
with inverse-sample exponent equal to the number of original corrected positions.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-product-covariance`. -/
theorem integral_sourceCorrection_product_mul_conj :
    (∫ ω : SourceGaussianSamples w k,
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) *
      conj (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i' e) (l' e)) ∂sourceGaussianLaw w k) =
      if i = i' ∧ l = l' then
        (((k : ℝ) ^ (-(S.card : ℝ)) * Real.sqrt
          (pairedProductProbability (fun e : S ↦ lam e.1 (ξ e)) i *
            pairedProductProbability (fun e : S ↦ lam e.1 (ζ e)) l) : ℝ) : ℂ)
      else 0 := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integral_selectedBranchDensityCoefficient_mul_conj
    (B := fun e : sourceLocations w ↦ branchLabels w e.1 × branchLabels w e.1)
    (A := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
    (C := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2)) k hk S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e))
    (fun e ↦ hnonneg e.1 (ξ e)) (fun e ↦ hnonneg e.1 (ζ e)) i i' l l'

include hk hnonneg in
/-- A nonempty product of actual centered source entries has zero mean.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–407. -/
theorem integral_sourceCorrection_product_eq_zero [Nonempty S] :
    (∫ ω : SourceGaussianSamples w k,
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) ∂sourceGaussianLaw w k) = 0 := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integral_selectedBranchDensityCoefficient_eq_zero
    (B := fun e : sourceLocations w ↦ branchLabels w e.1 × branchLabels w e.1)
    (A := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
    (C := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2)) k S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i l

end TNLean.PEPS.PairEffect.SourceCircuit
