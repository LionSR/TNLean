/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBondTransport

/-!
# The crossed two-site translates of the physical-sector bond

On a periodic chain of length two, the translates of a two-site bond beginning
at sites `0` and `1` read the sites in the opposite cyclic orders `(0, 1)` and
`(1, 0)`.  This file isolates that finite-size case.  In fixed sector
coordinates `(k, h)`, the first translate acts on
$R_k \otimes L_h$, whereas the crossed translate acts on the complementary
factor $R_h \otimes L_k$.  Hence the two translates commute.

The final theorem combines this two-site calculation with adjacent-window
commutativity and disjoint-window locality to obtain pairwise commutativity on
every periodic chain of length at least two.

Appendix C.2, Proposition C.8 of arXiv:1606.00608 proves commutativity of the
translated bonds.  The source does not discuss this crossed two-site ordering
separately.
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Exchange the two factors of a matrix indexed by ordered pairs. -/
private noncomputable def swapPairMatrix {n : Type*}
    (B : Matrix (n × n) (n × n) ℂ) : Matrix (n × n) (n × n) ℂ :=
  Matrix.reindex (Equiv.prodComm n n) (Equiv.prodComm n n) B

/-- The tensor square of a matrix is unchanged when both its row pair and
column pair are exchanged. -/
private theorem reindex_prodComm_kronecker_self
    {m n : Type*}
    (A : Matrix m n ℂ) :
    Matrix.reindex (Equiv.prodComm m m) (Equiv.prodComm n n) (A ⊗ₖ A) =
      A ⊗ₖ A := by
  ext ⟨i, j⟩ ⟨p, q⟩
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply, mul_comm]

/-- Exchanging both physical sites commutes with a change of coordinates
which is the tensor square of one single-site coordinate matrix. -/
private theorem swapPairMatrix_sandwich_kronecker_self
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix (m × m) (m × m) ℂ) :
    swapPairMatrix (sandwichMap (A ⊗ₖ A)ᴴ B) =
      sandwichMap (A ⊗ₖ A)ᴴ (swapPairMatrix B) := by
  let em := Equiv.prodComm m m
  let en := Equiv.prodComm n n
  have hA : Matrix.reindex em en (A ⊗ₖ A) = A ⊗ₖ A :=
    reindex_prodComm_kronecker_self A
  have hAH : Matrix.reindex en em (A ⊗ₖ A)ᴴ = (A ⊗ₖ A)ᴴ := by
    ext x y
    have h := congrArg star (congrFun (congrFun hA y) x)
    simpa [Matrix.reindex_apply, star_mul', mul_comm] using h
  simp only [swapPairMatrix, sandwichMap_apply,
    Matrix.conjTranspose_conjTranspose]
  change (Matrix.reindexLinearEquiv ℂ ℂ en en)
      ((A ⊗ₖ A)ᴴ * B * (A ⊗ₖ A)) =
    (A ⊗ₖ A)ᴴ * Matrix.reindex em em B * (A ⊗ₖ A)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ en em en,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ en em em,
    Matrix.coe_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv,
    Matrix.coe_reindexLinearEquiv, hA, hAH]

/-- Swapping the two sector sites exchanges their sector labels and exchanges
the outer and neighboring pairs in the regrouped coordinates. -/
@[simp] private theorem twoSiteGlobalRegroupEquiv_swap_symm
    (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount)
    (x : BoundaryIndex F k h × NeighborIndex F k h) :
    F.twoSiteGlobalRegroupEquiv
        (F.twoSiteGlobalRegroupEquiv.symm ⟨(k, h), x⟩).swap =
      ⟨(h, k), (x.2.swap, x.1.swap)⟩ := by
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The crossed bond on a fixed `(k,h)` sector block.  It acts on the outer
factor $L_k \otimes R_h$, leaving the neighboring factor fixed. -/
private noncomputable def crossedSectorBond (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :
    Matrix (BoundaryIndex F k h × NeighborIndex F k h)
      (BoundaryIndex F k h × NeighborIndex F k h) ℂ :=
  Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
      (F.neighboringOperator h k) ⊗ₖ
    (1 : Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ)

/-- On a fixed sector pair, the ordinary and crossed two-site bonds act on
complementary tensor factors and hence commute. -/
private theorem fixedSectorBond_crossed_comm
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        F.neighboringOperator k h) * F.crossedSectorBond k h =
      F.crossedSectorBond k h *
        ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
          F.neighboringOperator k h) := by
  simp only [crossedSectorBond, ← Matrix.mul_kronecker_mul]
  simp

/-- Regrouping the swapped sector-coordinate bond gives the dependent direct
sum of the crossed fixed-sector bonds. -/
private theorem reindex_swapPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
        (swapPairMatrix F.sectorCoordinateBond) =
      Matrix.blockDiagonal' fun kh :
          Fin F.sectorCount × Fin F.sectorCount ↦
        F.crossedSectorBond kh.1 kh.2 := by
  ext ⟨kh, x⟩ ⟨pq, y⟩
  rcases kh with ⟨k, h⟩
  rcases pq with ⟨p, q⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, swapPairMatrix,
    sectorCoordinateBond, Equiv.symm_symm]
  change Matrix.blockDiagonal' (fun kh :
      Fin F.sectorCount × Fin F.sectorCount =>
      (1 : Matrix (BoundaryIndex F kh.1 kh.2)
        (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ F.neighboringOperator kh.1 kh.2)
        (F.twoSiteGlobalRegroupEquiv
          (F.twoSiteGlobalRegroupEquiv.symm ⟨(k, h), x⟩).swap)
        (F.twoSiteGlobalRegroupEquiv
          (F.twoSiteGlobalRegroupEquiv.symm ⟨(p, q), y⟩).swap) = _
  rw [twoSiteGlobalRegroupEquiv_swap_symm,
    twoSiteGlobalRegroupEquiv_swap_symm]
  by_cases hk : k = p
  · subst p
    by_cases hh : h = q
    · subst q
      simp [crossedSectorBond, Matrix.one_apply, Prod.ext_iff, mul_comm]
      by_cases hx : x.2.1 = y.2.1 <;>
        by_cases hy : x.2.2 = y.2.2 <;> simp_all
    · simp [Matrix.blockDiagonal'_apply, hh, crossedSectorBond]
  · simp [Matrix.blockDiagonal'_apply, hk, crossedSectorBond]

/-- Regrouping the ordinary sector-coordinate bond recovers its defining
fixed-sector blocks. -/
private theorem reindex_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
        F.sectorCoordinateBond =
      Matrix.blockDiagonal' fun kh :
          Fin F.sectorCount × Fin F.sectorCount ↦
        (1 : Matrix (BoundaryIndex F kh.1 kh.2)
          (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ
            F.neighboringOperator kh.1 kh.2 := by
  simp [sectorCoordinateBond]

/-- The sector-coordinate bond commutes with the bond obtained by exchanging
the two sites. -/
private theorem sectorCoordinateBond_swap_comm
    (F : PhysicalSectorFactorization K) :
    F.sectorCoordinateBond * swapPairMatrix F.sectorCoordinateBond =
      swapPairMatrix F.sectorCoordinateBond * F.sectorCoordinateBond := by
  apply (Matrix.reindex F.twoSiteGlobalRegroupEquiv
    F.twoSiteGlobalRegroupEquiv).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv) (_ * _) =
    (Matrix.reindexLinearEquiv ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv) (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv,
    Matrix.coe_reindexLinearEquiv, F.reindex_sectorCoordinateBond,
    F.reindex_swapPairMatrix_sectorCoordinateBond,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr
  funext kh
  exact F.fixedSectorBond_crossed_comm kh.1 kh.2

/-- The physical pair bond commutes with the same bond in the opposite site
order. -/
private theorem physicalPairBond_swap_comm
    (F : PhysicalSectorFactorization K) :
    F.physicalPairBond * swapPairMatrix F.physicalPairBond =
      swapPairMatrix F.physicalPairBond * F.physicalPairBond := by
  have hswap :
      swapPairMatrix
          (sandwichMap F.physicalCoordinateMatrixTwoᴴ F.sectorCoordinateBond) =
        sandwichMap F.physicalCoordinateMatrixTwoᴴ
          (swapPairMatrix F.sectorCoordinateBond) := by
    simpa only [physicalCoordinateMatrixTwo] using
      swapPairMatrix_sandwich_kronecker_self
        F.physicalCoordinateMatrix F.sectorCoordinateBond
  rw [physicalPairBond, hswap]
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    _ = F.physicalCoordinateMatrixTwoᴴ * F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixTwo * F.physicalCoordinateMatrixTwoᴴ) *
        swapPairMatrix F.sectorCoordinateBond *
        F.physicalCoordinateMatrixTwo := by simp only [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixTwoᴴ *
        (F.sectorCoordinateBond * swapPairMatrix F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixTwo := by
      rw [F.physicalCoordinateMatrixTwo_coisometry]
      simp [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixTwoᴴ *
        (swapPairMatrix F.sectorCoordinateBond * F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixTwo := by
      rw [F.sectorCoordinateBond_swap_comm]
    _ = F.physicalCoordinateMatrixTwoᴴ *
        swapPairMatrix F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixTwo * F.physicalCoordinateMatrixTwoᴴ) *
        F.sectorCoordinateBond * F.physicalCoordinateMatrixTwo := by
      rw [F.physicalCoordinateMatrixTwo_coisometry]
      simp [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- On the two-site periodic chain, the translate beginning at site zero is
the original pair matrix after identifying configurations with ordered pairs.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8.  The source does not
separately state the crossed finite-size case. -/
private theorem reindex_embedLocalOperator_two_zero
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2) F.physicalBond) =
      F.physicalPairBond := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 2)
      ((finTwoArrowEquiv (Fin d)).symm σ)
      ((finTwoArrowEquiv (Fin d)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp [physicalBond, MPSTensor.extractWindow, finTwoArrowEquiv]

/-- On the two-site periodic chain, the translate beginning at site one is
the pair matrix with its two tensor factors exchanged.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8.  The source does not
separately state the crossed finite-size case. -/
private theorem reindex_embedLocalOperator_two_one
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2) F.physicalBond) =
      swapPairMatrix F.physicalPairBond := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 2)
      ((finTwoArrowEquiv (Fin d)).symm σ)
      ((finTwoArrowEquiv (Fin d)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp [swapPairMatrix, physicalBond, MPSTensor.extractWindow,
    finTwoArrowEquiv]
  rfl

/-- The two oppositely ordered translates of the physical bond commute on the
periodic chain of length two.

In sector coordinates `(k,h)`, the translate beginning at site zero acts on
$R_k \otimes L_h$, while the translate beginning at site one acts on
$R_h \otimes L_k$.  No positivity, strong-area-law, zero-correlation-length,
or injectivity hypothesis is used.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8.  The source proves
commutativity of translated bonds but does not discuss this crossed two-site
ordering separately.

**Local finite-size clarification:** The opposite cyclic ordering at length
two is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem physicalBond_two_zero_one_comm (F : PhysicalSectorFactorization K) :
    embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2) F.physicalBond *
        embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2) F.physicalBond =
      embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2) F.physicalBond *
        embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2) F.physicalBond := by
  apply (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))) (_ * _) =
    (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))) (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)),
    Matrix.coe_reindexLinearEquiv, F.reindex_embedLocalOperator_two_zero,
    F.reindex_embedLocalOperator_two_one, F.physicalPairBond_swap_comm]

/-- Every pair of translated copies of the physical-sector bond commutes on
every periodic chain of length at least two.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem physicalBond_translates_comm (F : PhysicalSectorFactorization K)
    {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) :
    embedLocalOperator (d := d) 2 N hN i F.physicalBond *
        embedLocalOperator (d := d) 2 N hN j F.physicalBond =
      embedLocalOperator (d := d) 2 N hN j F.physicalBond *
        embedLocalOperator (d := d) 2 N hN i F.physicalBond := by
  by_cases hN2 : N = 2
  · subst N
    fin_cases i <;> fin_cases j
    · rfl
    · exact F.physicalBond_two_zero_one_comm
    · exact F.physicalBond_two_zero_one_comm.symm
    · rfl
  · have hN3 : 3 ≤ N := by omega
    by_cases hoverlap : MPSTensor.cyclicWindowsOverlap N 2 i j
    · rcases MPSTensor.cyclicWindowsOverlap_twoSite_cases hoverlap with
        rfl | rfl | hi
      · rfl
      · simpa [MPSTensor.cyclicForwardSite, finRotate_apply,
          Fin.add_def] using F.physicalBond_adjacent_comm hN3 i
      · subst i
        simpa [MPSTensor.cyclicForwardSite, finRotate_apply,
          Fin.add_def] using (F.physicalBond_adjacent_comm hN3 j).symm
    · exact F.physicalBond_disjoint_comm hN hoverlap

end MPOTensor.PhysicalSectorFactorization
