/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCorrectedContractionIdentity
import TNLean.PEPS.Approximation.PreparedSourceCorrections
import TNLean.PEPS.Approximation.AllSourceSlots

/-!
# Source replacements and the global corrected-subset identity

With finite orthonormal coordinates on the original input and full output
memories, replacing the original local source operators defines a density
matrix directly through the actual canonical residual words. Its difference
from the original circuit density is the sum of the nonempty corrected terms,
indexed by original source occurrences.

This is the full-output coordinate identity. It does not impose finite
dimensionality on intermediate private memories, and it does not identify a
partial trace over an arbitrary discarded output space.

Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–383.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The exact rank-one source operator at an original occurrence and local label pair.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
def exactSourceMatrix {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) (ξ ζ : branchLabels w e.1) :
    Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
      (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ :=
  Matrix.vecMulVec
    (((EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)).repr (sourceVectorAt w e ξ))
    (fun j ↦ conj (((EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)).repr (sourceVectorAt w e ζ) j))

/-- Replace the original local source operators in the full expansion of the
actual circuit. This definition is independent of the corrected-subset identity.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
def sourceReplacedDensity {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b)
    (Y : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  let A := fun _ : P ↦ true
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  Word.sourceOperatorDensity R U V
    (fun _ξ i ↦ EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ℂ)
    (fun _ξ i ↦ EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).2) ℂ)
    (coefficient A w) (Layout.mapOwner (affectedOwner A) a) (partialResidual A w)
    (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
    (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) ρ
    (fun ξ ζ i ↦ Y (partialSlotEquiv A w i).1
      (partialSlotChoice A w ξ i) (partialSlotChoice A w ζ i))

open Classical in
/-- Exact source operators recover the density of the original circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–355. -/
theorem sourceReplacedDensity_exact {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    sourceReplacedDensity w (exactSourceMatrix w) bIn bOut ρ =
      LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap * ρ *
        (LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap)ᴴ := by
  have h := correctedSourceTerm_eq_sourceContraction (fun _ : P ↦ true) w ∅
    (fun _ _ ↦ Or.inl rfl) (exactSourceMatrix w) bIn bOut ρ
  rw [correctedSourceTerm_empty] at h
  simpa [sourceReplacedDensity, Word.sourceOperatorDensity, selectedPartialSlots,
    exactSourceMatrix, partialSlotVector] using h.symm

private theorem selectedPartialSlots_map_allSourceSlotEquiv {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (Fin (partialSlots (fun _ : P ↦ true) w).length)) :
    selectedPartialSlots (fun _ : P ↦ true) w (S.map (allSourceSlotEquiv w).toEmbedding) = S := by
  classical
  ext i
  rw [mem_selectedPartialSlots, ← allSourceSlotEquiv_apply,
    Finset.mem_map_equiv, Equiv.symm_apply_apply]

open Classical in
/-- Replacing sources on a prescribed original subset gives its globally defined
corrected term, with the exact source operators elsewhere.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem sourceReplacedDensity_piecewise {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    sourceReplacedDensity w (S.piecewise E (exactSourceMatrix w)) bIn bOut ρ =
      correctedSourceTerm w S E bIn bOut ρ := by
  have h := correctedSourceTerm_eq_sourceContraction (fun _ : P ↦ true) w S
    (fun _ _ ↦ Or.inl rfl) E bIn bOut ρ
  simpa [sourceReplacedDensity, Word.sourceOperatorDensity, Finset.piecewise,
    mem_selectedPartialSlots, exactSourceMatrix, partialSlotVector, ite_apply] using h.symm

open Classical in
/-- The density defined by local source replacements differs from the original
circuit density by the sum over nonempty subsets of original source occurrences.
The branch coefficients and local ket–bra labels are retained exactly.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-subset-expansion`,
`04-compression.tex`, lines 338–383. -/
theorem sourceReplacedDensity_sub_exact {m n : Type} [Fintype m] [Fintype n]
    {a b : Layout P} (w : SourceCircuit a b)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    sourceReplacedDensity w (E + exactSourceMatrix w) bIn bOut ρ -
        (LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap * ρ *
          (LinearMap.toMatrix bIn.toBasis bOut.toBasis w.eval.toLinearMap)ᴴ) =
      ∑ S ∈ (Finset.univ : Finset (Finset (sourceLocations w))).erase ∅,
        correctedSourceTerm w S E bIn bOut ρ := by
  rw [← sourceReplacedDensity_exact w bIn bOut ρ]
  unfold sourceReplacedDensity
  dsimp only
  erw [Word.sourceOperatorDensity_sub]
  rw [← sum_nonempty_allSourceSlots w (fun S ↦ correctedSourceTerm w S E bIn bOut ρ)]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← sourceReplacedDensity_piecewise]
  unfold sourceReplacedDensity
  dsimp only
  have hm (i : Fin (partialSlots (fun _ : P ↦ true) w).length) :
      (partialSlotEquiv (fun _ : P ↦ true) w i).1 ∈ S.map (allSourceSlotEquiv w).toEmbedding ↔
        i ∈ S := by
    rw [← mem_selectedPartialSlots, selectedPartialSlots_map_allSourceSlotEquiv]
  simp only [Finset.piecewise, hm, ite_apply]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
