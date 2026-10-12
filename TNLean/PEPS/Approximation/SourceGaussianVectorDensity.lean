/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianContraction
import TNLean.PEPS.Approximation.PreparedSourceVectorDensity

/-!
# Actual vectors in the Gaussian corrected density

For a mixed pure input, the corrected term is the Gaussian weighted sum of
the actual partial-word output vectors with the original endpoint Schmidt
columns prepared in the selected source registers. The owner identifications
are the canonical isometries on the original input and output memories.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-product-covariance.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

open Classical in
/-- The actual partial-word output with selected Schmidt endpoint columns,
returned to the original output memory by the canonical owner isometry. -/
def partialSchmidtOutput (A : P → Bool) (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ : Choices A w) (u : PartialSchmidtCoordinates A w S) (ψ : Mem a) : Mem b :=
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  (Layout.mapOwnerIso (affectedOwner A) b).symm
    ((partialResidual A w ξ).eval
      ((SourceInventory.prepareSlots R U V (partialSchmidtSourceVectors A w S E F ξ u)
        (Layout.mapOwner (affectedOwner A) a)).eval
          (Layout.mapOwnerIso (affectedOwner A) a ψ)))

open Classical in
/-- On a mixed pure input, the actual corrected Gaussian term is the sum of
mixed outer products of the actual Schmidt-substituted partial outputs. -/
theorem correctedSourceTerm_gaussian_vecMulVec_eq_sum
    {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (ω : SourceGaussianSamples w k)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ψ φ : Mem a) :
    correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ).ofLp (fun j ↦ conj (bIn.repr φ j))) =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
          (∏ i : selectedPartialSlots A w S,
            sourceCorrection k
              (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
              (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
              (ω (partialSlotEquiv A w i.1).1
                (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
            Matrix.vecMulVec (bOut.repr (partialSchmidtOutput A w S E F ξ u ψ)).ofLp
              (fun j ↦ conj (bOut.repr (partialSchmidtOutput A w S E F ζ v φ) j)) := by
  rw [correctedSourceTerm_gaussian_eq_sum A w S E F hS k lam hsource]
  have hin (x : Mem a) :
      (bIn.map (Layout.mapOwnerIso (affectedOwner A) a)).repr
        (Layout.mapOwnerIso (affectedOwner A) a x) = bIn.repr x := by
    simp only [OrthonormalBasis.map, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply]
  simp_rw [← hin, Word.preparedMatrix_mul_vecMulVec]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
