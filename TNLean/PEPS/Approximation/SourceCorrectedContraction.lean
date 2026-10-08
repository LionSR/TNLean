/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCorrectedTerm
import TNLean.PEPS.Approximation.SourceSubstitutionInventory
import TNLean.PEPS.Approximation.SourcePreparationCoordinates
import TNLean.PEPS.Approximation.SourceGateDensity

/-!
# Original source labels in a corrected density contraction

In a partial expansion, the basis substitutions at every selected original
source position vanish unless their labels agree with the gate's actual local
choice. Summing these labels leaves the corrected source entries at the actual
ket and bra choices. The remaining operators are the canonical partial residuals,
independently of the vectors inserted at the selected positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.SelectedSourceCoordinates

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.selectedSourceCoordinatesFintype

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.coordinateBasisVectors

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialCoordinateBasisMatrix

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceBasisMatrix_eq_ite

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.correctedSourceTerm_eq_sum_coordinates

Provenance-ID: 8769-source-corrections-sourcecorrectedcontraction-07
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.partialCoordinateBasisMatrix_eq_preparedMatrix

-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
private theorem sum_labelBasis_density {I m n : Type} [Fintype I] [DecidableEq I] [Fintype n]
    {L C : I → Type} [∀ i, Fintype (L i)] [∀ i, Fintype (C i)]
    (l l' : ∀ i, L i)
    (E : ∀ i, L i → L i → C i → C i → ℂ)
    (K K' : (∀ i, C i) → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    (∑ u : ∀ i, L i × C i, ∑ v : ∀ i, L i × C i,
      (∏ i, E i (u i).1 (v i).1 (u i).2 (v i).2) •
        ((if (fun i ↦ (u i).1) = l then K (fun i ↦ (u i).2) else 0) * ρ *
          (if (fun i ↦ (v i).1) = l' then K' (fun i ↦ (v i).2) else 0)ᴴ)) =
      ∑ a, ∑ b, (∏ i, E i (l i) (l' i) (a i) (b i)) •
        (K a * ρ * (K' b)ᴴ) := by
  classical
  let e := Equiv.arrowProdEquivProdArrow I L C
  calc
    _ = ∑ u : (∀ i, L i) × (∀ i, C i), ∑ v : (∀ i, L i) × (∀ i, C i),
      (∏ i, E i (u.1 i) (v.1 i) (u.2 i) (v.2 i)) •
        ((if u.1 = l then K u.2 else 0) * ρ *
          (if v.1 = l' then K' v.2 else 0)ᴴ) := by
        apply Fintype.sum_equiv e
        intro u
        apply Fintype.sum_equiv e
        intro v
        rfl
    _ = _ := by
      have h (p q : Prop) [Decidable p] [Decidable q] (X Y : Matrix m n ℂ) :
          (if p then X else 0) * ρ * (if q then Y else 0)ᴴ =
            if p then if q then X * ρ * Yᴴ else 0 else 0 := by
        split_ifs <;> simp
      simp only [Fintype.sum_prod_type, h, smul_ite, smul_zero]
      simp

variable {P : Type}

/-- Endpoint coordinate choices at the selected original source positions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def SelectedSourceCoordinates {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Type :=
  ∀ e : S, Fin (sourceDims w e.1).1 × Fin (sourceDims w e.1).2

/-- There are finitely many endpoint coordinate choices. -/
instance selectedSourceCoordinatesFintype {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Fintype (SelectedSourceCoordinates w S) := by
  classical
  exact inferInstanceAs (Fintype (∀ e : S,
    Fin (sourceDims w e.1).1 × Fin (sourceDims w e.1).2))

/-- Basis substitutions that are independent of every local branch label.
Values outside the selected positions are zero and will not be used.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def coordinateBasisVectors {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u : SelectedSourceCoordinates w S)
    (e : sourceLocations w) (_ξ : branchLabels w e.1) :
    euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2) := by
  classical
  exact if he : e ∈ S then
    EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ (u ⟨e, he⟩).1 ⊗ₜ[ℂ]
      EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ (u ⟨e, he⟩).2
    else 0

/-- The actual partial matrix with endpoint basis tensors at the selected sources
and the original source vectors elsewhere.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def partialCoordinateBasisMatrix {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (u : SelectedSourceCoordinates w S)
    (ξ : Choices A w) (bIn : OrthonormalBasis n ℂ (Mem a))
    (bOut : OrthonormalBasis m ℂ (Mem b)) : Matrix m n ℂ := by
  classical
  exact LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (isoL (Layout.mapOwnerIso (affectedOwner A) b).symm ∘L
      (partialWithSources A w (selectedSourceVectors w S (coordinateBasisVectors w S u)) ξ).eval ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a)).toLinearMap

private theorem selectedSourceVectors_exterior (A : P → Bool)
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (e : sourceLocations w) (ξ : branchLabels w e.1)
    (hl : A (endpoints w e).1 = false) (hr : A (endpoints w e).2 = false) :
    selectedSourceVectors w S η e ξ = sourceVectorAt w e ξ := by
  have he : e ∉ S := by
    intro h
    simpa [hl, hr] using hS e h
  simp only [selectedSourceVectors, ite_eq_right he]

private theorem eval_prepareSlots_eq_zero_of_coord_zero {Q : Type}
    (R : SourceInventory Q) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout Q) (i : Fin R.length) (hi : η i = 0) :
    (SourceInventory.prepareSlots R U V η ℓ).eval = 0 := by
  ext x
  simp only [SourceInventory.eval_prepareSlots_eq_appendIso_symm,
    (SourceInventory.slotVector R U V).map_coord_zero i hi,
    TensorProduct.zero_tmul, map_zero, zero_apply]

private theorem selected_labelBasis_eq_coordinate (A : P → Bool)
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : SourceBasisChoice w S) (ξ : Choices A w)
    (hu : (fun e : S ↦ (u e).1) =
      fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
    (i : Fin (partialSlots A w).length) :
    selectedSourceVectors w S (labelBasisVectors w S u)
        (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) =
      selectedSourceVectors w S (coordinateBasisVectors w S (fun e ↦ (u e).2))
        (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) := by
  classical
  by_cases he : (partialSlotEquiv A w i).1 ∈ S
  · have hi := congrFun hu ⟨(partialSlotEquiv A w i).1, he⟩
    have hc : partialSlotChoice A w ξ i = (u ⟨(partialSlotEquiv A w i).1, he⟩).1 :=
      hi.symm
    simp only [selectedSourceVectors, ite_eq_left he, labelBasisVectors,
      coordinateBasisVectors, dite_eq_left he, ite_eq_left hc]
  · simp only [selectedSourceVectors, ite_eq_right he]

private theorem selected_labelBasis_zero_of_ne (A : P → Bool)
    {a b : Layout P} (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : SourceBasisChoice w S) (ξ : Choices A w)
    (hu : (fun e : S ↦ (u e).1) ≠
      fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))) :
    ∃ i : Fin (partialSlots A w).length,
      selectedSourceVectors w S (labelBasisVectors w S u)
        (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) = 0 := by
  classical
  obtain ⟨e, he⟩ := Function.ne_iff.mp hu
  obtain ⟨i, hi⟩ := (partialSlotEquiv A w).surjective ⟨e.1, hS e.1 e.2⟩
  refine ⟨i, ?_⟩
  have hz : selectedSourceVectors w S (labelBasisVectors w S u) e.1
      (choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))) = 0 := by
    simp only [selectedSourceVectors, ite_eq_left e.2, labelBasisVectors,
      dite_eq_left e.2, ite_eq_right (Ne.symm he)]
  exact (congrArg (fun t : {e : sourceLocations w //
      A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true} ↦
    selectedSourceVectors w S (labelBasisVectors w S u) t.1
      (choiceAt A w ξ t.1.1 (isTouched_of_source_endpoint A w t.1 t.2)) = 0) hi).mpr hz

open Classical in
/-- A label-selective partial matrix vanishes unless its labels agree with the
actual local choices. In the remaining case only endpoint basis tensors are inserted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem partialSourceBasisMatrix_eq_ite {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : SourceBasisChoice w S) (ξ : Choices A w)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b)) :
    partialSourceBasisMatrix A w S u ξ bIn bOut =
      if (fun e : S ↦ (u e).1) =
          (fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
      then partialCoordinateBasisMatrix A w S (fun e ↦ (u e).2) ξ bIn bOut else 0 := by
  have hη := selectedSourceVectors_exterior A w S (labelBasisVectors w S u) hS
  have hθ := selectedSourceVectors_exterior A w S
    (coordinateBasisVectors w S (fun e ↦ (u e).2)) hS
  have heη := eval_partialResidual_prepare_substituted A w _ hη ξ
  have heθ := eval_partialResidual_prepare_substituted A w _ hθ ξ
  by_cases hu : (fun e : S ↦ (u e).1) =
      (fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
  · rw [ite_eq_left hu]
    have hv := funext (selected_labelBasis_eq_coordinate A w S hS u ξ hu)
    rw [hv] at heη
    have heval := heη.symm.trans heθ
    simp only [partialSourceBasisMatrix, partialCoordinateBasisMatrix, heval]
  · rw [ite_eq_right hu]
    obtain ⟨i, hi⟩ := selected_labelBasis_zero_of_ne A w S hS u ξ hu
    rw [eval_prepareSlots_eq_zero_of_coord_zero _ _ _ _ _ i hi, comp_zero] at heη
    simp [partialSourceBasisMatrix, ← heη]

/-- In the partial expansion, each corrected source operator uses exactly the
original local ket and bra labels. Different corrected slots of the same gate
therefore share that label, and its branch coefficient occurs only once.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem correctedSourceTerm_eq_sum_coordinates {m n : Type} [Fintype m] [Fintype n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    correctedSourceTerm w S E bIn bOut ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        (∑ u : SelectedSourceCoordinates w S, ∑ v : SelectedSourceCoordinates w S,
          (∏ e : S, E e.1
            (choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
            (choiceAt A w ζ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
            (u e) (v e)) •
            (partialCoordinateBasisMatrix A w S u ξ bIn bOut * ρ *
              (partialCoordinateBasisMatrix A w S v ζ bIn bOut)ᴴ)) := by
  classical
  rw [correctedSourceTerm_eq_sum_partial A w S hS E bIn bOut ρ]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  apply congrArg (fun M : Matrix m m ℂ ↦
    (coefficient A w ξ * conj (coefficient A w ζ)) • M)
  let l := fun e : S ↦
    choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  let l' := fun e : S ↦
    choiceAt A w ζ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  let K := fun u : SelectedSourceCoordinates w S ↦
    partialCoordinateBasisMatrix A w S u ξ bIn bOut
  let K' := fun v : SelectedSourceCoordinates w S ↦
    partialCoordinateBasisMatrix A w S v ζ bIn bOut
  have hK (u : SourceBasisChoice w S) : partialSourceBasisMatrix A w S u ξ bIn bOut =
      if (fun e ↦ (u e).1) = l then K (fun e ↦ (u e).2) else 0 :=
    partialSourceBasisMatrix_eq_ite A w S hS u ξ bIn bOut
  have hK' (u : SourceBasisChoice w S) : partialSourceBasisMatrix A w S u ζ bIn bOut =
      if (fun e ↦ (u e).1) = l' then K' (fun e ↦ (u e).2) else 0 :=
    partialSourceBasisMatrix_eq_ite A w S hS u ζ bIn bOut
  simp_rw [hK, hK']
  exact sum_labelBasis_density l l' (fun e ↦ E e.1) K K' ρ

/-- The coordinate-substituted partial matrix uses the same canonical residual
for every choice of endpoint basis tensors; the unselected sources stay original.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem partialCoordinateBasisMatrix_eq_preparedMatrix {m n : Type}
    [Fintype m] [Fintype n] (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : SelectedSourceCoordinates w S) (ξ : Choices A w)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b)) :
    partialCoordinateBasisMatrix A w S u ξ bIn bOut =
      (partialResidual A w ξ).preparedMatrix (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
        (fun i ↦ selectedSourceVectors w S (coordinateBasisVectors w S u)
          (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i))
        (Layout.mapOwner (affectedOwner A) a)
        (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
        (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) := by
  classical
  have he := eval_partialResidual_prepare_substituted A w _
    (selectedSourceVectors_exterior A w S (coordinateBasisVectors w S u) hS) ξ
  ext i j
  simp only [partialCoordinateBasisMatrix, Word.preparedMatrix, he,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.map_apply]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
