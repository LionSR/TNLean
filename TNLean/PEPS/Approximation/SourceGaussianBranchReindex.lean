/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianBranchDensity

/-!
# Actual branch densities indexed by original source occurrences

Both independent endpoint assignments in a partial branch can be indexed by
the original corrected occurrences. The Gaussian variables retain their
original occurrence and ordered ket and bra labels. The prepared output
vectors change only by this exact reindexing.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- The actual partial-branch density, with its two independent endpoint
assignments reindexed by the original corrected source occurrences. -/
theorem gaussianSchmidtBranchDensity_eq_sum_original
    {P m : Type} [Fintype m] {a b : Layout P}
    (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ω : SourceGaussianSamples w k) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ψ φ : Mem a) (ξ ζ : Choices A w) :
    let ξ₀ := fun e : S ↦ choiceAt A w ξ e.1.1
      (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
    let ζ₀ := fun e : S ↦ choiceAt A w ζ e.1.1
      (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
    let e := partialSchmidtCoordinateEquiv A w S hS
    gaussianSchmidtBranchDensity A w S k lam E F ω bOut ψ φ ξ ζ =
      ∑ u, ∑ v, (∏ s : S, sourceCorrection k (lam s.1 (ξ₀ s)) (lam s.1 (ζ₀ s))
        (ω s.1 (ξ₀ s, ζ₀ s)) (u s) (v s)) •
        Matrix.vecMulVec (bOut.repr (partialSchmidtOutput A w S E F ξ (e.symm u) ψ)).ofLp
          (fun j ↦ conj (bOut.repr (partialSchmidtOutput A w S E F ζ (e.symm v) φ) j)) := by
  intro ξ₀ ζ₀ e
  unfold gaussianSchmidtBranchDensity
  apply Fintype.sum_equiv e
  intro u
  apply Fintype.sum_equiv e
  intro v
  simp only [Equiv.symm_apply_apply]
  congr 1
  apply Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS)
  intro i
  rw [partialSchmidtCoordinateEquiv_apply, partialSchmidtCoordinateEquiv_apply]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
