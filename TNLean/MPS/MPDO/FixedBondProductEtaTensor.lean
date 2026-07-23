/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicTransport
import TNLean.MPS.MPDO.FixedBondPositivePhysicalSectorConstructor
import TNLean.MPS.MPDO.FixedBondProductTensor

/-!
# Fixed matrix-product tensors from neighboring operators

This file represents the cyclic neighboring-operator decomposition of a fixed
commuting bond by one matrix-product tensor.  The virtual dimension is
independent of the chain length.

## Main definitions and statements

* `etaCyclicEdgeWeight` gives the scalar neighboring-operator weight.
* `reindex_mpo_cyclicEdgeWeightTensor_etaCyclicEdgeWeight` identifies its
  closed operator in sector-edge coordinates.
* `TranslationInvariantBondData.fixedProductTensorData` constructs an exact
  fixed tensor for an arbitrary positive commuting bond.

## References

* arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1593.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d : ℕ}

open PhysicalSectorFactorization

/-- The scalar edge weight obtained from a family of neighboring operators.

The current site contributes its right coordinate and the following site
contributes its left coordinate.  The block-diagonal matrix forces the ket and
bra sector labels to agree at both endpoints of the edge.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1593. -/
noncomputable def etaCyclicEdgeWeight {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ) :
    Fin d → Fin d → Fin d → Fin d → ℂ :=
  fun i j i' j' ↦
    let x := e.symm i
    let y := e.symm j
    let x' := e.symm i'
    let y' := e.symm j'
    Matrix.blockDiagonal' (fun qh : Fin K × Fin K ↦ η qh.1 qh.2)
      ⟨(x.1, x'.1), (x.2.1, x'.2.2)⟩
      ⟨(y.1, y'.1), (y.2.1, y'.2.2)⟩

/-- The cyclic edge-weight tensor is the direct sum of the cyclic products of
the neighboring operators in sector-edge coordinates.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
theorem reindex_mpo_cyclicEdgeWeightTensor_etaCyclicEdgeWeight
    {K N : ℕ} [NeZero N] (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ) :
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (mpo (cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e η)) N) =
      Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
        fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  ext ⟨k, x⟩ ⟨h, y⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    mpo_cyclicEdgeWeightTensor]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    apply Finset.prod_congr rfl
    intro n _
    have hx (m : Fin N) :
        e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ m) =
          ⟨k m, (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm x m⟩ := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    have hy (m : Fin N) :
        e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, y⟩ m) =
          ⟨k m, (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm y m⟩ := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    rw [etaCyclicEdgeWeight]
    rw [hx n, hx (n + 1), hy n, hy (n + 1)]
    rw [Matrix.blockDiagonal'_apply_eq]
    exact congrArg₂ (η (k n) (k (n + 1)))
      (Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge dl dr k x n)
      (Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge dl dr k y n)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hkh
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    have hk :
        (e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ n)).1 = k n := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    have hh :
        (e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨h, y⟩ n)).1 = h n := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    rw [etaCyclicEdgeWeight]
    rw [Matrix.blockDiagonal'_apply_ne]
    intro hpairs
    apply hn
    simpa only [hk, hh] using congrArg Prod.fst hpairs

/-- Conjugating a two-site bond by a sitewise conjugate-transposed matrix is
the corresponding Kronecker conjugation in pair coordinates. -/
private theorem singleKrausMap_sitewise_conjTranspose_pairBond
    (U : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix Uᴴ 2) B =
      Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)) := by
  apply (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_two]
  rw [show Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U))) =
      star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U) by
    exact (Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))).apply_symm_apply _]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose]
  change (Uᴴ ⊗ₖ Uᴴ) * pairBondMatrix B * (U ⊗ₖ U) =
    star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)
  simp [Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose]

/-- Sitewise conjugation by a unitary carries the complete periodic bond
product to the product of the conjugated pair-coordinate bonds. -/
private theorem singleKrausMap_sitewise_conjTranspose_bondProduct
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix Uᴴ N)
        (List.ofFn fun i : Fin N ↦ embedLocalOperator 2 N hN i B).prod =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm
            (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)))).prod := by
  have hUco : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  have hUiso : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [singleKrausMap_bondProduct_of_unitary Uᴴ (by simpa) (by simpa) hN]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [singleKrausMap_sitewise_conjTranspose_pairBond]

/-- The cyclic eta edge-weight tensor represents exactly the conjugated
periodic bond product determined by the same local decomposition. -/
private theorem mpo_cyclicEdgeWeightTensor_eta_eq_conjugated_bondProduct
    {K N : ℕ} [NeZero N] (hN : 2 ≤ N) (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (eta : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)) =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          eta qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    mpo (cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e eta)) N =
      singleKrausMap (sitewisePhysicalMatrix Uᴴ N)
        (List.ofFn fun i : Fin N ↦ embedLocalOperator 2 N hN i B).prod := by
  apply (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
    (Matrix.etaCyclicEdgeEquiv dl dr e)).injective
  rw [reindex_mpo_cyclicEdgeWeightTensor_etaCyclicEdgeWeight]
  rw [singleKrausMap_sitewise_conjTranspose_bondProduct U hU hN B]
  rw [reindex_product_embedLocalOperator_of_etaPair_decomposition
    hN dl dr e eta (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)) hB]

/-- Successive single-Kraus conjugations by a coisometry and its conjugate
transpose cancel. -/
private theorem singleKrausMap_comp_conjTranspose_of_mul_conjTranspose_eq_one
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (V : Matrix alpha alpha ℂ) (hV : V * Vᴴ = 1) (X : Matrix alpha alpha ℂ) :
    singleKrausMap V (singleKrausMap Vᴴ X) = X := by
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    V * (Vᴴ * X * V) * Vᴴ = (V * Vᴴ) * X * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hV, one_mul, mul_one]

namespace TranslationInvariantBondData

/-- The tensor obtained from one eta decomposition realizes the corresponding
fixed periodic bond product at every chain length at least two. -/
private theorem mpo_changePhysicalBasis_cyclicEtaWeight_eq_product
    (data : TranslationInvariantBondData d) {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (eta : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          eta qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ))
    (N : ℕ) (hN : 2 ≤ N) :
    mpo (changePhysicalBasis U
      (cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e eta))) N =
        (data.toCommutingFormData hN).product := by
  letI : NeZero N := ⟨by omega⟩
  let C₀ : MPOTensor d (d * d) :=
    cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e eta)
  let P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    (data.toCommutingFormData hN).product
  change mpo (changePhysicalBasis U C₀) N = P
  rw [← singleKrausMap_sitewisePhysicalMatrix_mpo U C₀ N]
  let V := sitewisePhysicalMatrix U N
  change singleKrausMap V (mpo C₀ N) = P
  change Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
      (Matrix.etaPairSpatialBlockEquiv e).symm
      (star (U ⊗ₖ U) * pairBondMatrix data.bond * (U ⊗ₖ U)) = _ at hB
  have hsector : mpo C₀ N =
      singleKrausMap (sitewisePhysicalMatrix Uᴴ N) P := by
    dsimp only [C₀, P]
    change mpo (cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e eta)) N =
      singleKrausMap (sitewisePhysicalMatrix Uᴴ N)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator 2 N hN i data.bond).prod
    exact mpo_cyclicEdgeWeightTensor_eta_eq_conjugated_bondProduct
      hN dl dr e U eta data.bond hU hB
  have hsectorV : mpo C₀ N = singleKrausMap Vᴴ P := by
    rw [sitewisePhysicalMatrix_conjTranspose]
    exact hsector
  rw [hsectorV]
  apply singleKrausMap_comp_conjTranspose_of_mul_conjTranspose_eq_one V
  dsimp only [V]
  rw [sitewisePhysicalMatrix_mul_conjTranspose]
  have hUco : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  rw [hUco, sitewisePhysicalMatrix_one]

/-- Every positive fixed bond whose periodic translates commute has one
exact matrix-product representation with positive bond dimension, independent
of the chain length.

This proves only the finite representation of the product.  It does not assert
that the representing tensor is normal and does not constrain the positive
realization scalar of the source MPO.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605; Beigi, arXiv:1105.1019v2, Lemma 2.1. -/
theorem nonempty_fixedProductTensorData (data : TranslationInvariantBondData d) :
    Nonempty (FixedProductTensorData data) := by
  exact Nonempty.map
    PositivePhysicalSectorFixedProductTensorData.repr
    data.nonempty_positivePhysicalSectorFixedProductTensorData

/-- A chosen exact matrix-product representation of the fixed commuting-bond
product.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605; Beigi, arXiv:1105.1019v2, Lemma 2.1. -/
noncomputable def fixedProductTensorData (data : TranslationInvariantBondData d) :
    FixedProductTensorData data :=
  data.positivePhysicalSectorFixedProductTensorData.repr

/-- The positive physical-sector factorization retained by the exact selected
fixed-product tensor.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, arXiv:1105.1019v2, Lemma 2.1 and Section III. -/
noncomputable def fixedProductTensorDataPhysicalSectorFactorization
    (data : TranslationInvariantBondData d) :
    PhysicalSectorFactorization data.fixedProductTensorData.tensor :=
  data.positivePhysicalSectorFixedProductTensorData.factorization

/-- The physical bond reconstructed from the selected fixed-product
factorization is the input commuting bond.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, arXiv:1105.1019v2, Lemma 2.1 and Section III. -/
theorem fixedProductTensorDataPhysicalSectorFactorization_physicalBond_eq
    (data : TranslationInvariantBondData d) :
    data.fixedProductTensorDataPhysicalSectorFactorization.physicalBond =
      data.bond :=
  data.positivePhysicalSectorFixedProductTensorData.physicalBond_eq

/-- The neighboring operators retained by the selected fixed-product
factorization are positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, arXiv:1105.1019v2, Lemma 2.1 and Section III. -/
theorem fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos
    (data : TranslationInvariantBondData d) :
    ∀ q h,
      (data.fixedProductTensorDataPhysicalSectorFactorization
        |>.neighboringOperator q h).PosSemidef :=
  data.positivePhysicalSectorFixedProductTensorData.neighboring_pos

end TranslationInvariantBondData

namespace EtaLocalStructureData

variable {D : ℕ} {M : MPOTensor d D}

/-- The bond carried by an eta-local structure has one exact fixed matrix-product
representation.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605. -/
theorem nonempty_fixedProductTensorData (data : EtaLocalStructureData M) :
    Nonempty (TranslationInvariantBondData.FixedProductTensorData data.bondData) :=
  data.bondData.nonempty_fixedProductTensorData

/-- A chosen exact fixed matrix-product representation of the bond carried by an eta-local
structure.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605. -/
noncomputable def fixedProductTensorData (data : EtaLocalStructureData M) :
    TranslationInvariantBondData.FixedProductTensorData data.bondData :=
  data.bondData.fixedProductTensorData

end EtaLocalStructureData

end MPOTensor
