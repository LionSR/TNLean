/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CorrectedSchmidtOutput
import TNLean.PEPS.Approximation.SeparatedOutputCoordinates
import TNLean.PEPS.Approximation.SourceGaussianBranchReindex
import TNLean.PEPS.Approximation.GaussianSeparatedPhysicalDensity

/-!
# Expected physical norm of an actual partial branch

The local words and their input isometries are constructed from the original
allowed circuit and its actual scalar-input preparation. The physical and
discarded coordinates are the canonical bases induced by four regional
orthonormal bases. The estimate contains no exterior or discarded dimension.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-one-choice; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-actual-sampling-actualgaussianbranch-01
TNLean.PEPS.PairEffect.SourceCircuit.integrable_actualGaussianBranch_and_integral_le
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- An actual partial branch, reduced to the physical output in the canonical
regional bases, has integrable trace norm and the dimension-free Gaussian bound.
The two local contractions and their proper input isometries are constructed. -/
theorem integrable_actualGaussianBranch_and_integral_le
    {P X Y d e : Type} [Fintype X] [Fintype Y] [Fintype d] [Fintype e]
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
    (p₀ : Word [] a) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (ξ ζ : Choices (correctedMask w S) w) :
    let A := correctedMask w S
    let q := affectedOwner A
    let r := fun p : Option {p // A p = true} ↦ p.isSome
    let physical' := Layout.mapOwner r (Layout.mapOwner q physical)
    let discard' := Layout.mapOwner r (Layout.mapOwner q discard)
    ∀ (bA : OrthonormalBasis X ℂ (Mem (Layout.restrict (fun p : Bool ↦ p) physical')))
      (bE : OrthonormalBasis Y ℂ (Mem (Layout.restrict (fun p : Bool ↦ !p) physical')))
      (bD : OrthonormalBasis d ℂ (Mem (Layout.restrict (fun p : Bool ↦ p) discard')))
      (bF : OrthonormalBasis e ℂ (Mem (Layout.restrict (fun p : Bool ↦ !p) discard'))),
    let bP := ((Layout.partitionBasis (fun p : Bool ↦ p) physical' bA bE).map
      (Layout.mapOwnerIso r (Layout.mapOwner q physical)).symm).map
        (Layout.mapOwnerIso q physical).symm
    let bG := ((Layout.partitionBasis (fun p : Bool ↦ p) discard' bD bF).map
      (Layout.mapOwnerIso r (Layout.mapOwner q discard)).symm).map
        (Layout.mapOwnerIso q discard).symm
    let bOut := (bP.tensorProduct bG).map (appendIso physical discard).symm
    let M := fun ω ↦ Matrix.partialTraceRight
      (gaussianSchmidtBranchDensity A w S k lam E F ω bOut (p₀.eval 1) (p₀.eval 1) ξ ζ)
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm (M ω)) (sourceGaussianLaw w k) ∧
      (∫ ω, Matrix.rectangularTraceNorm (M ω) ∂sourceGaussianLaw w k) ≤
        (Fintype.card X : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro A q r physical' discard' bA bE bD bF bP bG bOut M
  obtain ⟨v, v', hv, hv', _, _, _, _, n, tau, L, G, htau, htausum, hξ⟩ :=
    exists_correctedSchmidtOutput w S E F hw hE hF p₀ hp₀ hp₀s ξ
  obtain ⟨z, z', hz, hz', _, _, _, _, m, tau', L', G', htau', htau'sum, hζ⟩ :=
    exists_correctedSchmidtOutput w S E F hw hE hF p₀ hp₀ hp₀s ζ
  let out := Layout.mapOwner r (Layout.mapOwner q (physical ++ discard))
  have hout : out = physical' ++ discard' :=
    (congrArg (Layout.mapOwner r) (Layout.mapOwner_append q physical discard)).trans
      (Layout.mapOwner_append r (Layout.mapOwner q physical) (Layout.mapOwner q discard))
  let J := Layout.regionalOutputIso (fun p : Bool ↦ p) physical' discard' out hout bA
  let J' := Layout.regionalOutputIso (fun p : Bool ↦ !p) physical' discard' out hout bE
  let hS := correctedMask_meets w S
  let eqv := partialSchmidtCoordinateEquiv A w S hS
  let ξ₀ := fun s : S ↦ choiceAt A w ξ s.1.1
    (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2))
  let ζ₀ := fun s : S ↦ choiceAt A w ζ s.1.1
    (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2))
  let coeff := fun (u : CorrectedSchmidtCoordinates w S × CorrectedSchmidtCoordinates w S)
      (ω : SourceGaussianSamples w k) ↦
    ∏ s : S, sourceCorrection k (lam s.1 (ξ₀ s)) (lam s.1 (ζ₀ s))
      (ω s.1 (ξ₀ s, ζ₀ s)) (u.1 s) (u.2 s)
  let N := fun ω ↦ Word.separatedPhysicalDensity J v z L L' tau tau'
    J' v' z' G G' bD bF (fun u ↦ coeff u ω)
  have hN : Integrable (fun ω ↦ Matrix.rectangularTraceNorm (N ω)) (sourceGaussianLaw w k) ∧
      (∫ ω, Matrix.rectangularTraceNorm (N ω) ∂sourceGaussianLaw w k) ≤
        (Fintype.card X : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2) :=
    integrable_gaussianSeparatedPhysicalDensity_and_integral_le w k hk S ξ₀ ζ₀
      lam hnonneg hmass J v z L L' bD hv hz J' v' z' G G' bF hv' hz'
      tau tau' htau htau' htausum htau'sum
  have hξcoord (i : CorrectedSchmidtCoordinates w S) :
      (bOut.repr (partialSchmidtOutput A w S E F ξ (eqv.symm i) (p₀.eval 1))).ofLp =
        Word.separatedPhysicalCoordinates J v L tau J' v' G bD bF i := by
    funext h
    rcases h with ⟨⟨x, y⟩, h, j⟩
    exact Layout.mapOwner_mapOwner_coordinates_eq_separated q r (fun p : Bool ↦ p)
      physical discard bA bE bD bF v v' L G tau _ i (hξ i) x y h j
  have hζcoord (i : CorrectedSchmidtCoordinates w S) :
      (bOut.repr (partialSchmidtOutput A w S E F ζ (eqv.symm i) (p₀.eval 1))).ofLp =
        Word.separatedPhysicalCoordinates J z L' tau' J' z' G' bD bF i := by
    funext h
    rcases h with ⟨⟨x, y⟩, h, j⟩
    exact Layout.mapOwner_mapOwner_coordinates_eq_separated q r (fun p : Bool ↦ p)
      physical discard bA bE bD bF z z' L' G' tau' _ i (hζ i) x y h j
  have he (ω : SourceGaussianSamples w k) : M ω = N ω := by
    dsimp only [M, N]
    rw [gaussianSchmidtBranchDensity_eq_sum_original A w S hS]
    simp only [Word.separatedPhysicalDensity, Fintype.sum_prod_type]
    simp_rw [← hξcoord, ← hζcoord]
    rfl
  simpa only [he] using hN

end TNLean.PEPS.PairEffect.SourceCircuit
