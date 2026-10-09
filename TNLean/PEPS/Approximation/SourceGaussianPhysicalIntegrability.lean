/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianMoments
import Mathlib.MeasureTheory.Integral.Average

/-!
# Integrability of actual Gaussian corrected operators

Every corrected term, including its physical partial trace, has an integrable
trace norm under the original global Gaussian law. This follows from its
actual Schmidt-coordinate expansion and the second moments of its scalar
coefficients. No contractivity, normalized input, covariance bound, or bound
on the private dimensions is required for this integrability statement.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-sourcegaussianphysicalintegrability-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.exists_sampledSourceMatrix_error_le_sum_integral

Provenance-ID: 8769-physical-sourcegaussianphysicalintegrability-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian

Provenance-ID: 8769-physical-sourcegaussianphysicalintegrability-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian

-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- Any fixed matrix-valued linear image of the actual corrected term has
integrable trace norm. This includes partial traces and physical matrix blocks. -/
theorem integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian
    {P m n r s : Type} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) (L : Matrix m m ℂ →ₗ[ℂ] Matrix r s ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω)
        bIn bOut ρ))) (sourceGaussianLaw w k) := by
  let J := (Choices A w × Choices A w) ×
    (PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S)
  let z (q : J) (ω : SourceGaussianSamples w k) :=
    (coefficient A w q.1.1 * conj (coefficient A w q.1.2)) *
      ∏ i : selectedPartialSlots A w S,
        sourceCorrection k
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w q.1.1 i.1))
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w q.1.2 i.1))
          (ω (partialSlotEquiv A w i.1).1
            (partialSlotChoice A w q.1.1 i.1, partialSlotChoice A w q.1.2 i.1))
          (q.2.1 i) (q.2.2 i)
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  let K (ξ : Choices A w) (u : PartialSchmidtCoordinates A w S) :=
    (partialResidual A w ξ).preparedMatrix R U V
      (partialSchmidtSourceVectors A w S E F ξ u)
      (Layout.mapOwner (affectedOwner A) a)
      (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
      (bOut.map (Layout.mapOwnerIso (affectedOwner A) b))
  let M (q : J) := L (K q.1.1 q.2.1 * ρ * (K q.1.2 q.2.2)ᴴ)
  have hz (q : J) : MemLp (z q) 2 (sourceGaussianLaw w k) :=
    (partialSourceCorrection_product_memLp_two A w S hS k hk lam hnonneg
      q.1.1 q.1.2 q.2.1 q.2.2).const_mul _
  have he (ω : SourceGaussianSamples w k) :
      L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) bIn bOut ρ) =
        ∑ q : J, z q ω • M q := by
    rw [correctedSourceTerm_gaussian_eq_sum A w S E F hS k lam hsource]
    simp only [J, map_sum, map_smul, Finset.smul_sum, smul_smul,
      Fintype.sum_prod_type, z, M, K, R, U, V]
  simp_rw [he]
  exact ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two z hz M

open Classical in
/-- The globally defined physical corrected term has integrable trace norm
after tracing the actual discarded registers, for every fixed input matrix. -/
theorem integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian
    {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    (A : P → Bool) {a : Layout P} (physical garbage : Layout P)
    (w : SourceCircuit a (physical ++ garbage)) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ) (hk : 0 < k)
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
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (physicalCorrectedSourceTerm physical garbage w S
        (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ))
      (sourceGaussianLaw w k) := by
  exact integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian A w S hS k hk
    lam hnonneg E F hsource bIn
    ((bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm) ρ
    (Matrix.partialTraceRightLM (α := x) (β := d))

open Classical in
/-- Some actual Gaussian sample has physical error at most the sum of the
expected corrected-term norms. Integrability is proved from the original law,
and the error is the actual sampled-source replacement error. -/
theorem exists_sampledSourceMatrix_error_le_sum_integral
    {P n x d : Type} [Fintype n] [Fintype x] [Fintype d]
    {a : Layout P} (physical garbage : Layout P)
    (w : SourceCircuit a (physical ++ garbage)) (k : ℕ) (hk : 0 < k)
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
    ∃ ω : SourceGaussianSamples w k,
      Matrix.rectangularTraceNorm
        (physicalSourceReplacedDensity physical garbage w
          (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω)
          bIn bPhysical bGarbage ρ - physicalDensity physical garbage w bIn bPhysical bGarbage ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        ∫ ω, Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S
          (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ)
          ∂sourceGaussianLaw w k := by
  let T := (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅
  let f (S : Finset (sourceLocations w)) (ω : SourceGaussianSamples w k) :=
    Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S
      (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ)
  have hf (S : Finset (sourceLocations w)) : Integrable (f S) (sourceGaussianLaw w k) :=
    integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian
      (fun _ ↦ true) physical garbage w S (fun _ _ ↦ Or.inl rfl) k hk
      lam hnonneg E F hsource bIn bPhysical bGarbage ρ
  obtain ⟨ω, hω⟩ := exists_le_integral (integrable_finsetSum T (fun S _ ↦ hf S))
  refine ⟨ω, (rectangularTraceNorm_physical_sampledSourceMatrix_sub_le
    physical garbage w k lam E F bIn bPhysical bGarbage ρ ω).trans ?_⟩
  exact hω.trans_eq (integral_finsetSum T (fun S _ ↦ hf S))

end TNLean.PEPS.PairEffect.SourceCircuit
