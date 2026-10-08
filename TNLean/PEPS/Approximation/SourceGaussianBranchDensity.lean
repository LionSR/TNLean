/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianVectorDensity
import TNLean.PEPS.Approximation.SourceGaussianPhysicalIntegrability

/-!
# Summing the actual Gaussian partial branches

A partial branch pair gives a mixed operator built from its actual prepared
output vectors and the original Gaussian source coefficients. The expectation
of the full corrected trace norm is bounded by the branch expectations with
exactly one absolute ket and bra coefficient. All required integrability is
derived from the original Gaussian law.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-sourcegaussianbranchdensity-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.gaussianSchmidtBranchDensity

Provenance-ID: 8769-physical-sourcegaussianbranchdensity-02
Downstream declaration:
https://lionsr.github.io/TNLean/docs/TNLean/PEPS/Approximation/SourceGaussianBranchDensity.html#TNLean.PEPS.PairEffect.SourceCircuit.integrable_rectangularTraceNorm_map_gaussianSchmidtBranchDensity

Provenance-ID: 8769-physical-sourcegaussianbranchdensity-03
Downstream declaration:
https://lionsr.github.io/TNLean/docs/TNLean/PEPS/Approximation/SourceGaussianBranchDensity.html#TNLean.PEPS.PairEffect.SourceCircuit.integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum

-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P m n r s : Type} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    {a b : Layout P}

open Classical in
/-- The actual Gaussian operator for one partial ket and bra branch, before
multiplying by the two outer gate coefficients. -/
def gaussianSchmidtBranchDensity
    (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ω : SourceGaussianSamples w k) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ψ φ : Mem a) (ξ ζ : Choices A w) : Matrix m m ℂ :=
  ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
    (∏ i : selectedPartialSlots A w S,
      sourceCorrection k
        (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
        (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
        (ω (partialSlotEquiv A w i.1).1
          (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
      Matrix.vecMulVec (bOut.repr (partialSchmidtOutput A w S E F ξ u ψ)).ofLp
        (fun j ↦ conj (bOut.repr (partialSchmidtOutput A w S E F ζ v φ) j))

open Classical in
/-- Every fixed matrix-valued linear image of an actual partial branch has
integrable trace norm. No branch contraction bound is required. -/
theorem integrable_rectangularTraceNorm_map_gaussianSchmidtBranchDensity
    (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (bOut : OrthonormalBasis m ℂ (Mem b)) (ψ φ : Mem a) (ξ ζ : Choices A w)
    (L : Matrix m m ℂ →ₗ[ℂ] Matrix r s ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (L (gaussianSchmidtBranchDensity A w S k lam E F ω bOut ψ φ ξ ζ)))
      (sourceGaussianLaw w k) := by
  let z := fun (q : PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S)
      (ω : SourceGaussianSamples w k) ↦
    ∏ i : selectedPartialSlots A w S,
      sourceCorrection k
        (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
        (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
        (ω (partialSlotEquiv A w i.1).1
          (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (q.1 i) (q.2 i)
  let M := fun q : PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S ↦
    L (Matrix.vecMulVec (bOut.repr (partialSchmidtOutput A w S E F ξ q.1 ψ)).ofLp
      (fun j ↦ conj (bOut.repr (partialSchmidtOutput A w S E F ζ q.2 φ) j)))
  have h := ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two z
    (fun q ↦ partialSourceCorrection_product_memLp_two A w S hS k hk lam hnonneg ξ ζ q.1 q.2) M
  simpa only [gaussianSchmidtBranchDensity, map_sum, map_smul,
    Fintype.sum_prod_type, z, M] using h

open Classical in
/-- The expected norm of the actual corrected operator is at most the sum of
the actual partial-branch expectations, weighted by the original ket and bra
coefficient norms. Integrability of every term is supplied by the source law. -/
theorem integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum
    (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ψ φ : Mem a) (L : Matrix m m ℂ →ₗ[ℂ] Matrix r s ℂ) :
    (∫ ω, Matrix.rectangularTraceNorm
      (L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)))))
        ∂sourceGaussianLaw w k) ≤
      ∑ ξ, ∑ ζ, ‖coefficient A w ξ * conj (coefficient A w ζ)‖ *
        ∫ ω, Matrix.rectangularTraceNorm
          (L (gaussianSchmidtBranchDensity A w S k lam E F ω bOut ψ φ ξ ζ))
          ∂sourceGaussianLaw w k := by
  let c := fun q : Choices A w × Choices A w ↦
    coefficient A w q.1 * conj (coefficient A w q.2)
  let N := fun (q : Choices A w × Choices A w) (ω : SourceGaussianSamples w k) ↦
    L (gaussianSchmidtBranchDensity A w S k lam E F ω bOut ψ φ q.1 q.2)
  have hN (q : Choices A w × Choices A w) :
      Integrable (fun ω ↦ Matrix.rectangularTraceNorm (N q ω)) (sourceGaussianLaw w k) :=
    integrable_rectangularTraceNorm_map_gaussianSchmidtBranchDensity
      A w S k hk lam E F hS hnonneg bOut ψ φ q.1 q.2 L
  have he (ω : SourceGaussianSamples w k) :
      L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j)))) =
      ∑ q, c q • N q ω := by
    rw [correctedSourceTerm_gaussian_vecMulVec_eq_sum A w S hS k lam E F hsource]
    simp only [Fintype.sum_prod_type, map_sum, map_smul, c, N,
      gaussianSchmidtBranchDensity]
  have hsum := integrable_finsetSum Finset.univ (fun q _ ↦ (hN q).const_mul ‖c q‖)
  have hfull := integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian
    A w S hS k hk lam hnonneg E F hsource bIn bOut
    (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j))) L
  calc
    _ ≤ ∫ ω, ∑ q, ‖c q‖ * Matrix.rectangularTraceNorm (N q ω)
        ∂sourceGaussianLaw w k := by
      apply integral_mono hfull hsum
      intro ω
      dsimp only
      rw [he]
      exact Matrix.rectangularTraceNorm_sum_smul_le _ _ _
    _ = _ := by
      rw [integral_finsetSum _ (fun q _ ↦ (hN q).const_mul ‖c q‖)]
      simp only [integral_const_mul, Fintype.sum_prod_type, c, N]

end TNLean.PEPS.PairEffect.SourceCircuit
