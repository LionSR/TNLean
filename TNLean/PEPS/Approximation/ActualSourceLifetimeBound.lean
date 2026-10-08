/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualCorrectedSourceBound
import TNLean.PEPS.Approximation.ExteriorPhysicalDimension
import TNLean.PEPS.Approximation.FiniteRegisterMemories
import TNLean.PEPS.Approximation.SourceCircuitResourceBounds

/-!
# The corrected-term estimate from the original circuit resources

The physical memory has the original local dimensions. Every discarded
register is finite-dimensional, as required in the source manuscript, but its
dimension is absent from the estimate. The affected dimensions, local branch
coefficients and whole-lifetime participation counts give the bound for the
actual corrected term.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
356–381 and 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-total-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-actual-sampling-actualsourcelifetimebound-01
TNLean.PEPS.PairEffect.SourceCircuit.integral_actualCorrectedSourceTerm_le_lifetime
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation

open Classical in
/-- The actual corrected term obeys the paper's lifetime and physical-dimension
bound. All local factors, input isometries and discarded bases are constructed;
no branch estimate or factorization certificate is assumed. -/
theorem integral_actualCorrectedSourceTerm_le_lifetime
    {P n x g : Type}
    [Fintype n] [Fintype x] [Fintype g]
    (physicalDim : P → ℕ) (ps : List P) (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps)
    {a discard : Layout P}
    (w : SourceCircuit a (familyPhysicalLayout physicalDim ps ++ discard))
    (hw : w.IsAllowed) (hfinite : ∀ r ∈ discard, FiniteDimensional ℂ r.space)
    (lifetime : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ j : gateLocations w, ∑ ξ : branchLabels w j, ‖branchCoefficient w j ξ‖ ≤ B)
    (hphysical : ∀ p, (physicalDim p : ℝ≥0) ≤ D)
    (S : Finset (sourceLocations w)) (k : ℕ) (hk : 0 < k)
    (lam : ∀ s : sourceLocations w, branchLabels w s.1 →
      Fin (min (sourceDims w s).1 (sourceDims w s).2) → ℝ)
    (E : ∀ s : sourceLocations w, branchLabels w s.1 →
      Matrix (Fin (sourceDims w s).1) (Fin (min (sourceDims w s).1 (sourceDims w s).2)) ℂ)
    (F : ∀ s : sourceLocations w, branchLabels w s.1 →
      Matrix (Fin (sourceDims w s).2) (Fin (min (sourceDims w s).1 (sourceDims w s).2)) ℂ)
    (hnonneg : ∀ s ξ j, 0 ≤ lam s ξ j) (hmass : ∀ s ξ, ∑ j, lam s ξ j = 1)
    (hE : ∀ s ξ, (E s ξ)ᴴ * E s ξ = 1) (hF : ∀ s ξ, (F s ξ)ᴴ * F s ξ = 1)
    (hsource : ∀ s ξ, ambientSchmidtVector (lam s ξ) (E s ξ) (F s ξ) =
      (sourceCoordinates w s ξ).ofLp)
    (p₀ : Word [] a) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem (familyPhysicalLayout physicalDim ps)))
    (bDiscard : OrthonormalBasis g ℂ (Mem discard)) :
    (∫ ω, Matrix.rectangularTraceNorm
      (physicalCorrectedSourceTerm (familyPhysicalLayout physicalDim ps) discard w S
        (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bDiscard
          (Matrix.vecMulVec (bIn.repr (p₀.eval 1)).ofLp
            (fun j ↦ conj (bIn.repr (p₀.eval 1) j)))) ∂sourceGaussianLaw w k) ≤
      ((B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4) ^ S.card *
        (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  let : Fintype P := Fintype.ofList ps hcover
  let A := correctedParties (endpoints w) S
  let mask := correctedMask w S
  let q := affectedOwner mask
  let r := fun p : Option {p // mask p = true} ↦ p.isSome
  let bA := affectedFamilyPhysicalBasis physicalDim ps hps hcover A
  let bE := exteriorFamilyPhysicalBasis physicalDim ps hps hcover A
  let bD := Layout.restrictedDiscardBasis q r (fun p : Bool ↦ p) discard hfinite
  let bF := Layout.restrictedDiscardBasis q r (fun p : Bool ↦ !p) discard hfinite
  have h := integral_actualCorrectedSourceTerm_le w hw S k hk lam E F
    hnonneg hmass hE hF hsource p₀ hp₀ hp₀s bIn bPhysical bDiscard bA bE bD bF
  have hdim : (Fintype.card ((p : {p // p ∈ A}) → Fin (physicalDim p)) : ℝ) ^ 2 =
      ∏ p ∈ A, (physicalDim p : ℝ) ^ 2 := by
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort,
      Nat.cast_prod, Finset.prod_pow]
  rw [hdim] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  apply coefficient_physical_cost_le w S physicalDim lifetime B D hB hD
  · intro p _
    rw [← participationCount_eq_card_incidentGates]
    exact hlifetime p
  · intro j _
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm] using hcoeff j
  · intro p _
    exact hphysical p

end TNLean.PEPS.PairEffect.SourceCircuit
