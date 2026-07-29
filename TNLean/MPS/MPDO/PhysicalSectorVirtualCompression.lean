/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Virtual compression of physical-sector factorizations

A rectangular change of virtual coordinates can be absorbed separately into
the left and right tensors of a physical-sector factorization.  Their
contraction inserts the range matrix of the coordinate map between the
original right and left tensors.

## Main definitions

* `MPOTensor.PhysicalSectorFactorization.neighboringOperatorWithMatrix`
  contracts neighboring sector tensors through a prescribed virtual matrix.
* `MPOTensor.PhysicalSectorFactorization.ofVirtualCompression` transports a
  physical-sector factorization through a rectangular virtual compression.

## References

* arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219
* arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
  lines 1381--1450
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D E : ℕ} {K : MPOTensor d D} {L : MPOTensor d E}

/-- The neighboring-sector contraction through a virtual matrix `P`.

For `P = 1`, this is the ordinary neighboring operator.  A rectangular
virtual compression by `V` produces this contraction with `P = V * Vᴴ`.

Source context: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines
1441--1445. -/
noncomputable def neighboringOperatorWithMatrix
    (F : PhysicalSectorFactorization K) (P : Matrix (Fin D) (Fin D) ℂ)
    (k h : Fin F.sectorCount) :
    Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ :=
  Matrix.of fun x y ↦
    ∑ delta, ∑ gamma,
      P delta gamma * F.rightTensor k delta x.1 y.1 *
        F.leftTensor h gamma x.2 y.2

/-- Entries of the matrix-weighted neighboring operator are the corresponding
weighted contractions of the right and left sector tensors. -/
@[simp] theorem neighboringOperatorWithMatrix_apply
    (F : PhysicalSectorFactorization K) (P : Matrix (Fin D) (Fin D) ℂ)
    (k h : Fin F.sectorCount) (x y : NeighborIndex F k h) :
    F.neighboringOperatorWithMatrix P k h x y =
      ∑ delta, ∑ gamma,
        P delta gamma * F.rightTensor k delta x.1 y.1 *
          F.leftTensor h gamma x.2 y.2 :=
  rfl

/-- Contraction through the identity matrix is the ordinary neighboring
operator. -/
@[simp] theorem neighboringOperatorWithMatrix_one
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    F.neighboringOperatorWithMatrix 1 k h = F.neighboringOperator k h := by
  ext x y
  rw [neighboringOperatorWithMatrix_apply, neighboringOperator_apply]
  apply Finset.sum_congr rfl
  intro delta _
  simp [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ]

/-- Transport a physical-sector factorization through a rectangular virtual
compression.

The physical-sector decomposition and physical isometry are unchanged.  The
coordinate map and its adjoint are absorbed into the right and left virtual
tensor families, respectively.

Source context: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines
195--219, and Appendix C.2, equation `AppUkU=rl`, lines 1381--1388. -/
noncomputable def ofVirtualCompression (F : PhysicalSectorFactorization K)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hCompression : ∀ i : Fin (d * d),
      L.toMPSTensor i = Vᴴ * K.toMPSTensor i * V) :
    PhysicalSectorFactorization L := by
  classical
  refine
    { sectorCount := F.sectorCount
      leftDim := F.leftDim
      rightDim := F.rightDim
      leftDim_pos := F.leftDim_pos
      rightDim_pos := F.rightDim_pos
      sectorEquiv := F.sectorEquiv
      physicalIsometry := F.physicalIsometry
      physicalIsometry_isometry := F.physicalIsometry_isometry
      leftTensor := fun k beta ↦
        ∑ gamma, star (V gamma beta) • F.leftTensor k gamma
      rightTensor := fun k alpha ↦
        ∑ delta, V delta alpha • F.rightTensor k delta
      factorization := ?_ }
  intro beta alpha
  ext ⟨k, a⟩ ⟨h, b⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hLetter (i j : Fin d) :
      L i j = Vᴴ * K i j * V := by
    simpa only [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat] using
      hCompression (finProdFinEquiv (i, j))
  have hSlice :
      physicalSlice L beta alpha =
        ∑ gamma, ∑ delta,
          (star (V gamma beta) * V delta alpha) •
            physicalSlice K gamma delta := by
    ext i j
    simp only [physicalSlice, hLetter, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro delta _
    ring
  have hConj :
      F.physicalIsometry * physicalSlice L beta alpha *
          F.physicalIsometryᴴ =
        ∑ gamma, ∑ delta, (star (V gamma beta) * V delta alpha) •
          (F.physicalIsometry * physicalSlice K gamma delta *
            F.physicalIsometryᴴ) := by
    rw [hSlice]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [hConj]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    have hF (gamma delta : Fin D) :=
      congrFun (congrFun (F.factorization gamma delta) ⟨k, a⟩) ⟨k, b⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] at hF
    simp_rw [hF]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro delta _
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    have hF (gamma delta : Fin D) :=
      congrFun (congrFun (F.factorization gamma delta) ⟨k, a⟩) ⟨h, b⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkh] at hF
    simp_rw [hF]
    simp

/-- Virtual compression replaces the ordinary neighboring contraction by the
matrix-weighted contraction through `V * Vᴴ`.

No positivity is asserted: positivity of the ordinary neighboring contraction
does not by itself establish positivity after inserting the range matrix.

Source context: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines
195--219, and Appendix C.2, equation `etarl`, lines 1441--1445. -/
@[simp] theorem ofVirtualCompression_neighboringOperator
    (F : PhysicalSectorFactorization K) (V : Matrix (Fin D) (Fin E) ℂ)
    (hCompression : ∀ i : Fin (d * d),
      L.toMPSTensor i = Vᴴ * K.toMPSTensor i * V)
    (k h : Fin F.sectorCount) :
    (F.ofVirtualCompression V hCompression).neighboringOperator k h =
      F.neighboringOperatorWithMatrix (V * Vᴴ) k h := by
  classical
  ext x y
  simp only [neighboringOperator_apply, ofVirtualCompression,
    neighboringOperatorWithMatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro delta _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gamma _
  apply Finset.sum_congr rfl
  intro beta _
  ring

end MPOTensor.PhysicalSectorFactorization
