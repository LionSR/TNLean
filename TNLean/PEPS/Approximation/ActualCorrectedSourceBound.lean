/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualGaussianBranch
import TNLean.PEPS.Approximation.SourcePhysicalBasisInvariance

/-!
# Expected norm of the actual corrected source term

The partial branches of the original circuit give the physical corrected term
after summation with the original ket and bra coefficients. Adapted regional
bases are used only inside the proof; the conclusion holds in any physical and
discarded orthonormal coordinates.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-one-choice; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- The actual corrected term has the coefficient-weighted Gaussian bound in
arbitrary output coordinates. The local words and Schmidt isometries are
constructed from the allowed circuit and its source-free input preparation. -/
theorem integral_actualCorrectedSourceTerm_le
    {P n x g X Y d e : Type}
    [Fintype n] [Fintype x] [Fintype g]
    [Fintype X] [Fintype Y] [Fintype d] [Fintype e]
    {a physical discard : Layout P} (w : SourceCircuit a (physical ++ discard))
    (hw : w.IsAllowed) (S : Finset (sourceLocations w)) (k : ℕ) (hk : 0 < k)
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
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bDiscard : OrthonormalBasis g ℂ (Mem discard)) :
    let A := correctedMask w S
    let q := affectedOwner A
    let r := fun p : Option {p // A p = true} ↦ p.isSome
    let physical' := Layout.mapOwner r (Layout.mapOwner q physical)
    let discard' := Layout.mapOwner r (Layout.mapOwner q discard)
    ∀ (_ : OrthonormalBasis X ℂ (Mem (Layout.restrict (fun p : Bool ↦ p) physical')))
      (_ : OrthonormalBasis Y ℂ (Mem (Layout.restrict (fun p : Bool ↦ !p) physical')))
      (_ : OrthonormalBasis d ℂ (Mem (Layout.restrict (fun p : Bool ↦ p) discard')))
      (_ : OrthonormalBasis e ℂ (Mem (Layout.restrict (fun p : Bool ↦ !p) discard'))),
    (∫ ω, Matrix.rectangularTraceNorm (physicalCorrectedSourceTerm physical discard w S
      (sourceGaussianCorrection w k lam E F ω) bIn bPhysical bDiscard
        (Matrix.vecMulVec (bIn.repr (p₀.eval 1)).ofLp
          (fun j ↦ conj (bIn.repr (p₀.eval 1) j)))) ∂sourceGaussianLaw w k) ≤
      ((∑ ξ : Choices A w, ∑ ζ : Choices A w,
        ‖coefficient A w ξ * conj (coefficient A w ζ)‖) * (Fintype.card X : ℝ) ^ 2) *
        (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro A q r physical' discard' bA bE bD bF
  let bP := ((Layout.partitionBasis (fun p : Bool ↦ p) physical' bA bE).map
    (Layout.mapOwnerIso r (Layout.mapOwner q physical)).symm).map
      (Layout.mapOwnerIso q physical).symm
  let bG := ((Layout.partitionBasis (fun p : Bool ↦ p) discard' bD bF).map
    (Layout.mapOwnerIso r (Layout.mapOwner q discard)).symm).map
      (Layout.mapOwnerIso q discard).symm
  let bOut := (bP.tensorProduct bG).map (appendIso physical discard).symm
  let L := Matrix.partialTraceRightLM (α := X × Y) (β := d × e)
  have hbasis (ω : SourceGaussianSamples w k) :=
    rectangularTraceNorm_physicalCorrectedSourceTerm_basis_eq physical discard w S
      (sourceGaussianCorrection w k lam E F ω) bIn bP bPhysical bG bDiscard
      (p₀.eval 1) (p₀.eval 1)
  simp_rw [hbasis]
  have hsum := integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum
    A w S k hk lam E F (correctedMask_meets w S) hnonneg hsource
    bIn bOut (p₀.eval 1) (p₀.eval 1) L
  refine hsum.trans ?_
  calc
    _ ≤ ∑ ξ : Choices A w, ∑ ζ : Choices A w,
        ‖coefficient A w ξ * conj (coefficient A w ζ)‖ *
          ((Fintype.card X : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2)) := by
      apply Finset.sum_le_sum
      intro ξ _
      apply Finset.sum_le_sum
      intro ζ _
      exact mul_le_mul_of_nonneg_left
        (integrable_actualGaussianBranch_and_integral_le w hw S k hk lam E F
          hnonneg hmass hE hF p₀ hp₀ hp₀s ξ ζ bA bE bD bF).2 (norm_nonneg _)
    _ = _ := by simp only [← Finset.sum_mul, mul_assoc]

end TNLean.PEPS.PairEffect.SourceCircuit
