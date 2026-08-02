/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapActiveSectorZCL

/-!
# Virtual spanning does not remove the active-sector nilpotent remainder

This file gives a four-sector, bond-dimension-two tensor for which the virtual
matrices of the physical sectors span the full matrix algebra, the
physical-trace transfer is idempotent, and every neighboring operator is
positive semidefinite.  The active sector trace matrix is primitive, but it is not
idempotent.  In the rectangular notation of Appendix C.2 of
arXiv:1606.00608, the tensor therefore satisfies
\[
  S=LQ,\qquad S^2=S,
\]
while
\[
  Q(1-S)L=T-T^2\ne0,\qquad T=QL.
\]

Thus spanning by the full virtual matrix algebra does not, by itself, prove
the missing vanishing in the proof of Lemma C.5.  The induced classical cyclic
family satisfies the strong area law mathematically.  The companion
`ActiveSectorInverseMapProvenance` calculation identifies the factorization
below with one selected by an explicit Hayashi decomposition, normalized tail,
and inverse map.

## Main result

* `virtual_spanning_does_not_force_rectangular_remainder_zero`: the combined
  counterexample to the proposed rectangular-vanishing argument.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1406--1499
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ActiveSectorSpanningCounterexample

/-- The closed left-sector vectors. -/
noncomputable def leftPairing : Matrix (Fin 2) (Fin 4) ℂ :=
  !![1 / 4, 1 / 4, 1 / 4, 1 / 4;
     1, -1, 1, -1]

/-- The closed right-sector functionals. -/
noncomputable def rightPairing : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 1 / 8;
     1, 1 / 8;
     1, -1 / 8;
     1, -1 / 8]

/-- The virtual matrix belonging to a scalar physical sector. -/
noncomputable def sectorMatrix (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (fun beta => leftPairing beta k) (fun alpha => rightPairing k alpha)

/-- The tensor whose four diagonal physical entries are the sector matrices. -/
noncomputable def tensor : MPOTensor 4 2 :=
  fun i j => if i = j then sectorMatrix i else 0

lemma leftPairing_mul_rightPairing : leftPairing * rightPairing = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftPairing, rightPairing, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma rightPairing_mul_leftPairing : rightPairing * leftPairing =
    !![3 / 8, 1 / 8, 3 / 8, 1 / 8;
       3 / 8, 1 / 8, 3 / 8, 1 / 8;
       1 / 8, 3 / 8, 1 / 8, 3 / 8;
       1 / 8, 3 / 8, 1 / 8, 3 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftPairing, rightPairing, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma rightPairing_mul_leftPairing_re_pos (k h : Fin 4) :
    0 < ((rightPairing * leftPairing) k h).re := by
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases h <;> norm_num

lemma rightPairing_mul_leftPairing_ne_idempotent :
    (rightPairing * leftPairing) * (rightPairing * leftPairing) ≠
      rightPairing * leftPairing := by
  intro h
  rw [rightPairing_mul_leftPairing] at h
  have hij := congrFun (congrFun h 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three] at hij

lemma sectorMatrix_span_eq_top : Submodule.span ℂ (Set.range sectorMatrix) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro X
  let c : Fin 4 → ℂ := ![
    X 0 0 + 8 * X 0 1 + (1 / 4) * X 1 0 + 2 * X 1 1,
    X 0 0 + 8 * X 0 1 - (1 / 4) * X 1 0 - 2 * X 1 1,
    X 0 0 - 8 * X 0 1 + (1 / 4) * X 1 0 - 2 * X 1 1,
    X 0 0 - 8 * X 0 1 - (1 / 4) * X 1 0 + 2 * X 1 1]
  have hsum : X = ∑ k, c k • sectorMatrix k := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [c, sectorMatrix, leftPairing, rightPairing, Fin.sum_univ_four] <;> ring
  rw [hsum]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

/-- The four diagonal sector matrices make the tensor injective. -/
lemma tensor_isInjective : tensor.IsInjective := by
  apply top_unique
  rw [← sectorMatrix_span_eq_top]
  apply Submodule.span_le.2
  rintro _ ⟨k, rfl⟩
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (k, k), ?_⟩
  change tensor (finProdFinEquiv (k, k)).divNat
      (finProdFinEquiv (k, k)).modNat = sectorMatrix k
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp [tensor]

lemma physTraceTransfer_tensor : physTraceTransfer tensor = leftPairing * rightPairing := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physTraceTransfer, tensor, sectorMatrix, leftPairing, rightPairing,
      Fin.sum_univ_four, Matrix.mul_apply]

lemma physTraceTransfer_tensor_idempotent :
    physTraceTransfer tensor * physTraceTransfer tensor = physTraceTransfer tensor := by
  rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Idempotence of the nonzero physical-trace transfer gives source zero
correlation length. -/
lemma tensor_isSourceZCL : tensor.IsSourceZCL := by
  apply isSourceZCL_of_physTraceTransfer_sq tensor
  · rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]
    intro h
    have hij := congrFun (congrFun h 0) 0
    norm_num at hij
  · exact physTraceTransfer_tensor_idempotent

/-- The identification of the four-dimensional physical space with four
one-dimensional sectors. -/
noncomputable def sectorEquiv :
    Fin 4 ≃ Σ _k : Fin 4, Fin 1 × Fin 1 where
  toFun k := ⟨k, (0, 0)⟩
  invFun q := q.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨k, ⟨x, y⟩⟩
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    subst x
    subst y
    rfl

/-- The scalar physical-sector factorization of the counterexample tensor. -/
noncomputable def factorization : PhysicalSectorFactorization tensor where
  sectorCount := 4
  leftDim := fun _ => 1
  rightDim := fun _ => 1
  leftDim_pos := fun _ => by omega
  rightDim_pos := fun _ => by omega
  sectorEquiv := sectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun k beta => Matrix.of fun _ _ => leftPairing beta k
  rightTensor := fun k alpha => Matrix.of fun _ _ => rightPairing k alpha
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
      simp [Matrix.submatrix_apply, sectorEquiv, physicalSlice, tensor, sectorMatrix]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one]
      change tensor k h beta alpha =
        Matrix.blockDiagonal'
          (fun q => Matrix.kroneckerMap (· * ·)
            (Matrix.of fun _ _ => leftPairing beta q) (Matrix.of fun _ _ => rightPairing q alpha))
          ⟨k, (0, 0)⟩ ⟨h, (0, 0)⟩
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
      simp [tensor, hkh]

/-- The normalized, strictly positive weight of each sector. -/
noncomputable def p : Fin 4 → ℝ := fun _ => 1 / 4

lemma p_nonneg (k : Fin 4) : 0 ≤ p k := by norm_num [p]

lemma sum_p : ∑ k, p k = 1 := by
  simp [p]

lemma neighboringOperator_eq (k h : Fin 4) :
    factorization.neighboringOperator k h =
      Matrix.diagonal (fun _ : Fin 1 × Fin 1 => (rightPairing * leftPairing) k h) := by
  ext x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  fin_cases x₁
  fin_cases x₂
  fin_cases y₁
  fin_cases y₂
  simp [PhysicalSectorFactorization.neighboringOperator_apply,
    factorization, Matrix.mul_apply]

/-- Every neighboring operator is a positive semidefinite scalar matrix. -/
lemma neighboringOperator_posSemidef (k h : Fin 4) :
    (factorization.neighboringOperator k h).PosSemidef := by
  rw [neighboringOperator_eq]
  apply Matrix.PosSemidef.diagonal
  intro i
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases h <;> norm_num [Complex.nonneg_iff]

lemma factorization_sectorVirtualMatrixFamily_span_eq_top :
    Submodule.span ℂ (Set.range factorization.sectorVirtualMatrixFamily) = ⊤ :=
  factorization.sectorVirtualMatrixFamily_span_eq_top tensor_isInjective

/-- All four sectors are active because their weights are strictly positive. -/
noncomputable def activeEquiv : factorization.ActiveSector p ≃ Fin 4 where
  toFun k := k.1
  invFun k := ⟨k, by norm_num [p]⟩
  left_inv k := Subtype.ext rfl
  right_inv _ := rfl

lemma reindex_activeSectorTraceMatrix :
    Matrix.reindex activeEquiv activeEquiv
        (factorization.activeSectorTraceMatrix p) =
      Matrix.map (rightPairing * leftPairing) Complex.re := by
  ext k h
  simp only [Matrix.reindex_apply, Matrix.map_apply]
  change (factorization.neighboringOperator k h).trace.re = ((rightPairing * leftPairing) k h).re
  rw [neighboringOperator_eq]
  have hcard : Fintype.card (factorization.NeighborIndex k h) = 1 := by
    change Fintype.card (Fin 1 × Fin 1) = 1
    simp
  simp [Matrix.trace, hcard]

/-- The active-sector trace matrix is not idempotent. -/
lemma activeSectorTraceMatrix_ne_idempotent :
    factorization.activeSectorTraceMatrix p *
        factorization.activeSectorTraceMatrix p ≠
      factorization.activeSectorTraceMatrix p := by
  intro hidem
  have hmap := congrArg
    (Matrix.reindexAlgEquiv ℝ ℝ activeEquiv) hidem
  rw [map_mul] at hmap
  change Matrix.reindex activeEquiv activeEquiv
      (factorization.activeSectorTraceMatrix p) *
        Matrix.reindex activeEquiv activeEquiv
          (factorization.activeSectorTraceMatrix p) =
      Matrix.reindex activeEquiv activeEquiv
        (factorization.activeSectorTraceMatrix p) at hmap
  rw [reindex_activeSectorTraceMatrix] at hmap
  have h01 := congrFun (congrFun hmap 0) 1
  rw [rightPairing_mul_leftPairing] at h01
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three] at h01

lemma trace_activeSectorTraceMatrix :
    Matrix.trace (factorization.activeSectorTraceMatrix p) = 1 := by
  rw [Matrix.trace]
  calc
    ∑ k, factorization.activeSectorTraceMatrix p k k =
        ∑ i : Fin 4, factorization.activeSectorTraceMatrix p
          (activeEquiv.symm i) (activeEquiv.symm i) :=
      (Equiv.sum_comp activeEquiv.symm
        (fun k => factorization.activeSectorTraceMatrix p k k)).symm
    _ = ∑ i : Fin 4, ((rightPairing * leftPairing) i i).re := by
      apply Finset.sum_congr rfl
      intro i _
      have happ := congrFun (congrFun reindex_activeSectorTraceMatrix i) i
      exact happ
    _ = 1 := by
      rw [rightPairing_mul_leftPairing]
      norm_num [Fin.sum_univ_four, Matrix.cons_val_two,
        Matrix.cons_val_three]

/-- Strict positivity of all entries makes the active-sector trace matrix primitive. -/
lemma activeSectorTraceMatrix_isPrimitive :
    Matrix.IsPrimitive (factorization.activeSectorTraceMatrix p) := by
  refine ⟨factorization.activeSectorTraceMatrix_nonneg p
    neighboringOperator_posSemidef, 1, by omega, ?_⟩
  intro k h
  rw [pow_one]
  have happ := congrFun (congrFun reindex_activeSectorTraceMatrix
    (activeEquiv k)) (activeEquiv h)
  change factorization.activeSectorTraceMatrix p
      (activeEquiv.symm (activeEquiv k)) (activeEquiv.symm (activeEquiv h)) =
    ((rightPairing * leftPairing) (activeEquiv k) (activeEquiv h)).re at happ
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at happ
  rw [happ]
  exact rightPairing_mul_leftPairing_re_pos (activeEquiv k) (activeEquiv h)

/-- The rectangular remainder is exactly the failure of the opposite product
`rightPairing * leftPairing` to be idempotent.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1484--1499. -/
lemma rectangular_remainder_eq_mul_sub_sq :
    rightPairing * (1 - leftPairing * rightPairing) * leftPairing =
      rightPairing * leftPairing -
        (rightPairing * leftPairing) * (rightPairing * leftPairing) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

/-- The rectangular remainder from CPSV16, Appendix C.2, does not vanish for
this factorization. -/
lemma rectangular_remainder_ne_zero :
    rightPairing * (1 - leftPairing * rightPairing) * leftPairing ≠ 0 := by
  intro hzero
  apply rightPairing_mul_leftPairing_ne_idempotent
  have hdiff :
      rightPairing * leftPairing -
          (rightPairing * leftPairing) * (rightPairing * leftPairing) = 0 := by
    rw [← rectangular_remainder_eq_mul_sub_sq]
    exact hzero
  exact (sub_eq_zero.mp hdiff).symm

/-- Full virtual-matrix spanning does not force the rectangular remainder
$Q(1-LQ)L$ to vanish.  The example has normalized positive sector weights,
positive semidefinite neighboring operators, an injective tensor with literal
physical-trace idempotence, and a primitive trace-one active trace matrix, while
that matrix is non-idempotent and the rectangular remainder is nonzero.

The companion area-law theorem proves the strong area law for this tensor.
Nevertheless, this is a counterexample only to the proposed intermediate
implication.  Lemma C.5 is proved in Case I under the standing assumption that
the tensor is an injective normal tensor; the raw tensor here does not have that
normalization, and its normalized representative loses the paper's literal
physical-trace identity.  Hence the result records a normalization obstruction,
not a counterexample to Lemma C.5 under its complete hypotheses.  The
source-selected inverse-map identification is proved separately in
`inverseMap_provenance_preserves_rectangular_remainder`.

**Scope restriction (non-normal representative):** documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem virtual_spanning_does_not_force_rectangular_remainder_zero :
    tensor.IsInjective ∧ tensor.IsSourceZCL ∧
      physTraceTransfer tensor * physTraceTransfer tensor = physTraceTransfer tensor ∧
      (∀ k, p k = 1 / 4) ∧ (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
      Submodule.span ℂ (Set.range factorization.sectorVirtualMatrixFamily) = ⊤ ∧
      (∀ k h, (factorization.neighboringOperator k h).PosSemidef) ∧
      Matrix.IsPrimitive (factorization.activeSectorTraceMatrix p) ∧
      Matrix.trace (factorization.activeSectorTraceMatrix p) = 1 ∧
      factorization.activeSectorTraceMatrix p *
          factorization.activeSectorTraceMatrix p ≠
        factorization.activeSectorTraceMatrix p ∧
      rightPairing * (1 - leftPairing * rightPairing) * leftPairing ≠ 0 :=
  ⟨tensor_isInjective, tensor_isSourceZCL, physTraceTransfer_tensor_idempotent,
    (by intro k; rfl), p_nonneg, sum_p,
    factorization_sectorVirtualMatrixFamily_span_eq_top,
    neighboringOperator_posSemidef, activeSectorTraceMatrix_isPrimitive,
    trace_activeSectorTraceMatrix, activeSectorTraceMatrix_ne_idempotent,
    rectangular_remainder_ne_zero⟩

end MPOTensor.ActiveSectorSpanningCounterexample
