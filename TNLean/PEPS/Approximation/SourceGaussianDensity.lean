/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianLaw
import TNLean.PEPS.Approximation.SourcePhysicalDensity

/-!
# Physical density for the actual Gaussian source replacements

The local correction is the sampled ambient operator minus the original mixed
source matrix. Substituting this family in the actual circuit gives the exact
physical error expansion after tracing the retained garbage. The index set is
the set of original source occurrences, independent of all random samples.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–383.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The centered correction of the actual sampled source operator in the original
endpoint coordinates, indexed by original positions and local ket–bra labels.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-random-source`. -/
def sourceGaussianCorrection (w : SourceCircuit a b) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ :=
  (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) - exactSourceMatrix w

/-- The actual ambient correction has zero mean on the one global Gaussian law.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–340. -/
theorem integral_sourceGaussianCorrection (w : SourceCircuit a b) (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    (∫ ω, sourceGaussianCorrection w k lam E F ω e ξ ζ ∂sourceGaussianLaw w k) = 0 := by
  change (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω - exactSourceMatrix w e ξ ζ
    ∂sourceGaussianLaw w k) = 0
  rw [integral_sub (integrable_sampledSourceMatrix w k lam E F hk hnonneg e ξ ζ)
    (integrable_const _), integral_sampledSourceMatrix w k lam E F hk hnonneg hsource]
  simp

/-- The actual centered ambient matrix is the Schmidt-frame transport of the
Gaussian correction whose coefficients enter the covariance estimate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–338. -/
theorem sourceGaussianCorrection_eq_transport (w : SourceCircuit a b) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (ω : SourceGaussianSamples w k) (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    sourceGaussianCorrection w k lam E F ω e ξ ζ =
      sourceTransport (E e ξ) (F e ξ) (E e ζ) (F e ζ)
        (sourceCorrection k (lam e ξ) (lam e ζ) (ω e (ξ, ζ))) := by
  have hs : exactSourceMatrix w e ξ ζ =
      ambientSchmidtSource (lam e ξ) (lam e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ) := by
    rw [ambientSchmidtSource, hsource, hsource]
    rfl
  change ambientSampledSource k (lam e ξ) (lam e ζ)
    (E e ξ) (F e ξ) (E e ζ) (F e ζ) (ω e (ξ, ζ)) - exactSourceMatrix w e ξ ζ = _
  rw [hs]
  exact ambientSourceCorrection_eq_transport k (lam e ξ) (lam e ζ)
    (E e ξ) (F e ξ) (E e ζ) (F e ζ) (ω e (ξ, ζ))

variable {n x d : Type} [Fintype n] [Fintype x] [Fintype d]
  (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage)) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (bIn : OrthonormalBasis n ℂ (Mem a))
  (bPhysical : OrthonormalBasis x ℂ (Mem physical))
  (bGarbage : OrthonormalBasis d ℂ (Mem garbage)) (ρ : Matrix n n ℂ)

open Classical in
/-- For each actual Gaussian sample, the physical output error is exactly the sum
of the nonempty original-source corrections after tracing the retained garbage.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`. -/
theorem physical_sampledSourceMatrix_sub_eq_sum (ω : SourceGaussianSamples w k) :
    physicalSourceReplacedDensity physical garbage w
        (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) bIn bPhysical bGarbage ρ -
      physicalDensity physical garbage w bIn bPhysical bGarbage ρ =
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        physicalCorrectedSourceTerm physical garbage w S
          (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ := by
  simpa only [sourceGaussianCorrection, sub_add_cancel] using
    physicalSourceReplacedDensity_sub_exact physical garbage w
      (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ

open Classical in
/-- The physical error of the actual sampled operators satisfies the corrected-term
trace-norm bound pointwise, with no factor depending on private-memory dimensions.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-total-error`. -/
theorem rectangularTraceNorm_physical_sampledSourceMatrix_sub_le
    (ω : SourceGaussianSamples w k) :
    Matrix.rectangularTraceNorm
      (physicalSourceReplacedDensity physical garbage w
          (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) bIn bPhysical bGarbage ρ -
        physicalDensity physical garbage w bIn bPhysical bGarbage ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical garbage w S
          (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bGarbage ρ) := by
  rw [physical_sampledSourceMatrix_sub_eq_sum]
  exact Matrix.rectangularTraceNorm_sum_le _ _

end TNLean.PEPS.PairEffect.SourceCircuit
