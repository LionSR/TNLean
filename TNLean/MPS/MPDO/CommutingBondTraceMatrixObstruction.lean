/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPDO.PhysicalSectorEtaLocalStructure
import TNLean.MPS.MPDO.ZCL

/-!
# A nonminimal sector factorization with nonprimitive trace matrix

This file records the inactive-sector obstruction in the converse argument of
arXiv:1606.00608, Appendix C.2, the converse implication, lines 1603--1613.
Even for
a normal source block with source zero correlation length and one exact positive
translation-invariant commuting-bond presentation, a chosen nonminimal
middle-space decomposition can retain a physical summand on which the bond
vanishes.  Its trace matrix is then not primitive.

The example is the pure product MPDO on a two-dimensional physical space.  Its
bond dimension is one and its only nonzero tensor entry is
$\mathcal K^{0,0}=1$.  In the chosen two-sector Beigi-style factorization, the
neighboring operators have trace matrix
\[
  T=\begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]
This does not exclude another factorization with primitive trace matrix: the
same product tensor has a one-sector factorization.  Thus an existential
repair of the source proof requires a source-faithful minimal or visible-sector
selection theorem; primitivity cannot be inferred for an arbitrary selected
factorization merely from the displayed commuting product.

## References

* arXiv:1606.00608, Appendix C.2, converse implication, lines 1597--1619.
* Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPOTensor.CommutingBondTraceMatrixObstruction

/-- The indicator of the retained physical sector. -/
noncomputable def sectorWeight (k : Fin 2) : ℂ := if k = 0 then 1 else 0

/-- The bond-dimension-one pure product MPDO with only
$\mathcal K^{0,0}$ nonzero. -/
noncomputable def tensor : MPOTensor 2 1 :=
  fun i j => if i = j then Matrix.of fun _ _ => sectorWeight i else 0

/-- The two-dimensional physical space as two one-dimensional sectors in the
decomposition of Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
noncomputable def sectorEquiv :
    Fin 2 ≃ Sigma fun _k : Fin 2 => Fin 1 × Fin 1 where
  toFun k := ⟨k, (0, 0)⟩
  invFun q := q.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨k, x, y⟩
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    subst x
    subst y
    rfl

/-- A two-sector factorization of the kind invoked in arXiv:1606.00608,
Appendix C.2, lines 1603--1605, specialized to the product tensor. -/
noncomputable def factorization : PhysicalSectorFactorization tensor where
  sectorCount := 2
  leftDim := fun _ => 1
  rightDim := fun _ => 1
  leftDim_pos := fun _ => by omega
  rightDim_pos := fun _ => by omega
  sectorEquiv := sectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun k _ => Matrix.of fun _ _ => sectorWeight k
  rightTensor := fun k _ => Matrix.of fun _ _ => sectorWeight k
  factorization := by
    intro beta alpha
    ext q r
    obtain ⟨k, x, y⟩ := q
    obtain ⟨h, u, v⟩ := r
    fin_cases x
    fin_cases y
    fin_cases u
    fin_cases v
    by_cases hkh : k = h
    · subst h
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one]
      rw [Matrix.blockDiagonal'_apply_eq]
      simp [Matrix.submatrix_apply, sectorEquiv, physicalSlice, tensor]
      simp [sectorWeight]
    · simp only [Matrix.reindex_apply, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one]
      change tensor k h beta alpha =
        Matrix.blockDiagonal'
          (fun q => Matrix.kroneckerMap (· * ·)
            (Matrix.of fun _ _ => sectorWeight q)
            (Matrix.of fun _ _ => sectorWeight q))
          ⟨k, (0, 0)⟩ ⟨h, (0, 0)⟩
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
      simp [tensor, hkh]

/-- The two physical basis vectors as one sector with a two-dimensional left
factor and a one-dimensional right factor.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1; arXiv:1606.00608,
Appendix C.2, lines 1603--1605. -/
noncomputable def oneSectorEquiv :
    Fin 2 ≃ Sigma fun _k : Fin 1 => Fin 2 × Fin 1 where
  toFun i := ⟨0, (i, 0)⟩
  invFun q := q.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨k, i, j⟩
    have hk : k = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst k
    subst j
    rfl

/-- A one-sector factorization of the product tensor, with the sector weight
placed entirely in its two-dimensional left factor.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1; arXiv:1606.00608,
Appendix C.2, lines 1603--1605. -/
noncomputable def oneSectorFactorization : PhysicalSectorFactorization tensor where
  sectorCount := 1
  leftDim := fun _ => 2
  rightDim := fun _ => 1
  leftDim_pos := fun _ => by omega
  rightDim_pos := fun _ => by omega
  sectorEquiv := oneSectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun _ _ => Matrix.diagonal sectorWeight
  rightTensor := fun _ _ => 1
  factorization := by
    intro beta alpha
    ext q r
    obtain ⟨k, x, y⟩ := q
    obtain ⟨h, u, v⟩ := r
    fin_cases k
    fin_cases h
    fin_cases y
    fin_cases v
    fin_cases beta
    fin_cases alpha
    simp [Matrix.reindex_apply, oneSectorEquiv, physicalSlice, tensor,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
    by_cases hxu : x = u
    all_goals simp [hxu]

/-- The real trace matrix of the neighboring operators considered in
arXiv:1606.00608, Appendix C.2, line 1613. -/
noncomputable def traceMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  fun k h => (Matrix.trace (factorization.neighboringOperator k h)).re

/-- The real trace matrix of the one-sector neighboring family.

Source: arXiv:1606.00608, Appendix C.2, line 1613. -/
noncomputable def oneSectorTraceMatrix : Matrix (Fin 1) (Fin 1) ℝ :=
  fun k h => (Matrix.trace (oneSectorFactorization.neighboringOperator k h)).re

/-- The sole neighboring operator in the one-sector factorization is the
rank-one diagonal matrix with diagonal $(1,0)$.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
lemma oneSector_neighboringOperator_eq
    (k h : Fin oneSectorFactorization.sectorCount) :
    oneSectorFactorization.neighboringOperator k h =
      Matrix.diagonal (fun x : Fin 1 × Fin 2 => sectorWeight x.2) := by
  ext x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  simp only [PhysicalSectorFactorization.neighboringOperator_apply, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  fin_cases x₁
  fin_cases y₁
  simp only [oneSectorFactorization, Matrix.one_apply, Matrix.diagonal_apply]
  simp only [if_true, one_mul, Prod.mk.injEq, true_and]

/-- Every neighboring operator in the one-sector factorization is positive
semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
lemma oneSector_neighboringOperator_posSemidef
    (k h : Fin oneSectorFactorization.sectorCount) :
    (oneSectorFactorization.neighboringOperator k h).PosSemidef := by
  rw [oneSector_neighboringOperator_eq]
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ sectorWeight (show Fin 2 from i.2)
  by_cases hi : (show Fin 2 from i.2) = 0
  all_goals simp [sectorWeight, hi]

/-- The one-sector trace matrix is the positive one-by-one matrix $(1)$.

Source: arXiv:1606.00608, Appendix C.2, line 1613. -/
lemma oneSectorTraceMatrix_eq : oneSectorTraceMatrix = 1 := by
  ext k h
  fin_cases k
  fin_cases h
  rw [oneSectorTraceMatrix, oneSector_neighboringOperator_eq]
  norm_num [Matrix.trace, sectorWeight]
  decide

/-- The trace matrix of the one-sector factorization is primitive.

Source: arXiv:1606.00608, Appendix C.2, line 1613. -/
lemma oneSectorTraceMatrix_isPrimitive :
    Matrix.IsPrimitive oneSectorTraceMatrix := by
  rw [oneSectorTraceMatrix_eq]
  refine ⟨?_, ⟨1, by norm_num, ?_⟩⟩
  all_goals intro i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num

/-- The neighboring operator is the scalar product of the two sector
indicators. -/
lemma neighboringOperator_eq (k h : Fin 2) :
    factorization.neighboringOperator k h =
      Matrix.diagonal (fun _ : Fin 1 × Fin 1 => sectorWeight k * sectorWeight h) := by
  ext x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  fin_cases x₁
  fin_cases x₂
  fin_cases y₁
  fin_cases y₂
  simp [PhysicalSectorFactorization.neighboringOperator_apply,
    factorization]

/-- Every neighboring operator in the displayed decomposition is positive
semidefinite. -/
lemma neighboringOperator_posSemidef (k h : Fin 2) :
    (factorization.neighboringOperator k h).PosSemidef := by
  rw [neighboringOperator_eq]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases k <;> fin_cases h <;> norm_num [sectorWeight, Complex.nonneg_iff]

/-- The full two-sector trace matrix is $\operatorname{diag}(1,0)$. -/
lemma traceMatrix_eq : traceMatrix = !![1, 0; 0, 0] := by
  have huniv : (Finset.univ : Finset (Fin 1 × Fin 1)) = {(0, 0)} := by
    ext x
    simp [Subsingleton.elim x (0, 0)]
  ext k h
  rw [traceMatrix, neighboringOperator_eq]
  change (∑ _i : Fin 1 × Fin 1, sectorWeight k * sectorWeight h).re =
    !![1, 0; 0, 0] k h
  rw [huniv]
  fin_cases k <;> fin_cases h <;> norm_num [sectorWeight]

/-- The unused physical summand makes the full Beigi trace matrix
nonprimitive. -/
lemma traceMatrix_not_isPrimitive : ¬ Matrix.IsPrimitive traceMatrix := by
  intro h
  obtain ⟨n, hn, hpos⟩ := h.exists_pos_pow
  have h11 := hpos (1 : Fin 2) (1 : Fin 2)
  rw [traceMatrix_eq] at h11
  have hdiag : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hdiag, Matrix.diagonal_pow] at h11
  norm_num [hn.ne'] at h11

/-- The doubled-index transfer map of the product tensor is the identity on its
one-dimensional bond algebra. -/
lemma transferMap_toMPSTensor :
    MPSTensor.transferMap tensor.toMPSTensor = LinearMap.id := by
  rw [← transferMap_eq_toMPSTensor]
  apply LinearMap.ext
  intro X
  rw [transferMap_apply]
  ext a b
  fin_cases a
  fin_cases b
  simp [tensor, sectorWeight, Fin.sum_univ_two, Matrix.mul_apply]

/-- The source tensor is normal. -/
lemma tensor_isNormalTensor : MPSTensor.IsNormalTensor tensor.toMPSTensor :=
  MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    tensor.toMPSTensor transferMap_toMPSTensor

/-- The product tensor is already injective before blocking. -/
lemma tensor_isInjective : tensor.IsInjective := by
  apply top_unique
  intro X _hX
  have hdiv : (0 : Fin (2 * 2)).divNat = (0 : Fin 2) := by decide
  have hmod : (0 : Fin (2 * 2)).modNat = (0 : Fin 2) := by decide
  have hone : tensor.toMPSTensor (0 : Fin (2 * 2)) = 1 := by
    change tensor (0 : Fin (2 * 2)).divNat (0 : Fin (2 * 2)).modNat = 1
    rw [hdiv, hmod]
    ext a b
    fin_cases a
    fin_cases b
    simp [tensor, sectorWeight]
  have hone_mem : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ (Set.range tensor.toMPSTensor) := by
    rw [← hone]
    exact Submodule.subset_span (Set.mem_range_self _)
  have hX : X = (X 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a b
    fin_cases a
    fin_cases b
    simp
  rw [hX]
  exact Submodule.smul_mem _ _ hone_mem

/-- The physical-trace transfer is the identity matrix. -/
lemma physTraceTransfer_tensor : physTraceTransfer tensor = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [physTraceTransfer, tensor, sectorWeight, Fin.sum_univ_two]

/-- The product tensor has source zero correlation length. -/
lemma tensor_isSourceZCL : tensor.IsSourceZCL := by
  apply isSourceZCL_of_physTraceTransfer_sq tensor
  · rw [physTraceTransfer_tensor]
    exact one_ne_zero
  · rw [physTraceTransfer_tensor, one_mul]

/-- The unique bond index as a pair of unique purification indices. -/
noncomputable def singletonPairEquiv : Fin 1 ≃ Fin 1 × Fin 1 where
  toFun _ := (0, 0)
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A local purification of the product tensor. -/
noncomputable def purification (i : Fin 2) (_k : Fin 1) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of fun _ _ => sectorWeight i

/-- The product tensor is locally purifiable. -/
lemma tensor_isLPDO : tensor.IsLPDO := by
  refine ⟨1, 1, purification, singletonPairEquiv, ?_⟩
  intro i j
  ext a b
  fin_cases a
  fin_cases b
  fin_cases i <;> fin_cases j <;>
    norm_num [tensor, purification, singletonPairEquiv, sectorWeight,
      Matrix.kroneckerMap_apply]

/-- The product tensor generates positive semidefinite operators on every
nonempty chain. -/
lemma tensor_isMPDO : tensor.IsMPDO := tensor_isLPDO.isMPDO

/-- The exact fixed commuting-bond presentation assembled from the displayed
Beigi neighboring operators. -/
noncomputable def commutingBondData : EtaLocalStructureData tensor :=
  factorization.etaLocalStructureData neighboringOperator_posSemidef

/-- The fixed commuting-bond product equals the source MPO with coefficient
one at every length in the source range. -/
lemma mpo_eq_commutingBondProduct (N : ℕ) (hN : 2 ≤ N) :
    mpo tensor N =
      (commutingBondData.bondData.toCommutingFormData hN).product := by
  exact factorization.mpo_eq_product_physicalBond hN

/-- A chosen nonminimal factorization of a normal source-ZCL MPDO with an exact
fixed positive commuting-bond presentation need not have a primitive trace
matrix.

This shows that the factorization needed after arXiv:1606.00608, Appendix C.2,
line 1613, must be selected after deleting inactive summands by a separate
argument.  The example does not rule out another factorization with primitive
trace matrix: the explicit one-sector factorization above has trace matrix
$(1)$. -/
theorem normal_sourceZCL_fixed_commutingBond_does_not_force_traceMatrix_primitive :
    tensor.IsMPDO ∧
      tensor.IsInjective ∧
      MPSTensor.IsNormalTensor tensor.toMPSTensor ∧
      tensor.IsSourceZCL ∧
      (∀ k h, (factorization.neighboringOperator k h).PosSemidef) ∧
      (∀ (N : ℕ) (hN : 2 ≤ N),
        mpo tensor N =
          (commutingBondData.bondData.toCommutingFormData hN).product) ∧
      traceMatrix = !![1, 0; 0, 0] ∧
      ¬ Matrix.IsPrimitive traceMatrix ∧
      oneSectorFactorization.sectorCount = 1 ∧
      (∀ k h,
        (oneSectorFactorization.neighboringOperator k h).PosSemidef) ∧
      Matrix.IsPrimitive oneSectorTraceMatrix := by
  exact ⟨tensor_isMPDO, tensor_isInjective, tensor_isNormalTensor, tensor_isSourceZCL,
    neighboringOperator_posSemidef, mpo_eq_commutingBondProduct,
    traceMatrix_eq, traceMatrix_not_isPrimitive, rfl,
    oneSector_neighboringOperator_posSemidef, oneSectorTraceMatrix_isPrimitive⟩

end MPOTensor.CommutingBondTraceMatrixObstruction
