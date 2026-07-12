/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBondCommutativity

/-!
# Transport of adjacent physical-sector bonds

This file transports the fixed-sector adjacent-bond calculation through the
dependent direct sum of three physical sectors and then to the original
three-site physical coordinates.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1589--1593
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The first two sites extracted from the inverse three-site regrouping have
the expected two-site outer and neighboring coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    F.twoSiteGlobalRegroupEquiv
        ((F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).1,
          (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.1) =
      ⟨(k, l), ((x.1.1, x.2.2.1), x.2.1)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The third site extracted from the inverse three-site regrouping consists
of the last neighboring left factor and the outer right factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem threeSiteGlobalRegroupEquiv_symm_third
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.2 =
      F.sectorFinEquiv.symm ⟨h, (x.2.2.2, x.1.2)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The last two sites extracted from the inverse three-site regrouping have
the expected two-site outer and neighboring coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    F.twoSiteGlobalRegroupEquiv
        ((F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.1,
          (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.2) =
      ⟨(l, h), ((x.2.1.2, x.1.2), x.2.2)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The first site extracted from the inverse three-site regrouping consists
of the outer left factor and the first neighboring right factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem threeSiteGlobalRegroupEquiv_symm_first_apply
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).1 =
      F.sectorFinEquiv.symm ⟨k, (x.1.1, x.2.1.1)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The dependent direct sum obtained by regrouping all three-sector
summands into their outer and two neighboring factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private abbrev ThreeSiteSectorBondIndex (F : PhysicalSectorFactorization K) :=
  Σ klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount),
    BoundaryIndex F klh.1 klh.2.2 ×
      (NeighborIndex F klh.1 klh.2.1 × NeighborIndex F klh.2.1 klh.2.2)

/-- The first adjacent bond on the dependent direct sum of three physical
sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def threeSiteSectorLeftBond (F : PhysicalSectorFactorization K) :
    Matrix (ThreeSiteSectorBondIndex F) (ThreeSiteSectorBondIndex F) ℂ :=
  Matrix.blockDiagonal' fun klh ↦
    (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
      (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
        (F.neighboringOperator klh.1 klh.2.1 ⊗ₖ
          (1 : Matrix (NeighborIndex F klh.2.1 klh.2.2)
            (NeighborIndex F klh.2.1 klh.2.2) ℂ))

/-- The second adjacent bond on the dependent direct sum of three physical
sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def threeSiteSectorRightBond (F : PhysicalSectorFactorization K) :
    Matrix (ThreeSiteSectorBondIndex F) (ThreeSiteSectorBondIndex F) ℂ :=
  Matrix.blockDiagonal' fun klh ↦
    (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
      (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
        ((1 : Matrix (NeighborIndex F klh.1 klh.2.1)
          (NeighborIndex F klh.1 klh.2.1) ℂ) ⊗ₖ
            F.neighboringOperator klh.2.1 klh.2.2)

/-- The two adjacent bonds commute on the dependent direct sum of all
three-sector summands.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem threeSiteSectorBonds_comm (F : PhysicalSectorFactorization K) :
    F.threeSiteSectorLeftBond * F.threeSiteSectorRightBond =
      F.threeSiteSectorRightBond * F.threeSiteSectorLeftBond := by
  rw [threeSiteSectorLeftBond, threeSiteSectorRightBond,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr
  funext klh
  exact F.adjacentSectorBonds_comm klh.1 klh.2.1 klh.2.2

/-- Regrouping the lift of the first two-site sector bond gives the dependent
direct sum of its fixed-sector actions.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem reindex_leftPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (leftPairMatrix F.sectorCoordinateBond) =
      F.threeSiteSectorLeftBond := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, leftPairMatrix]
  simp only [Matrix.kroneckerMap_apply, Equiv.prodAssoc_symm_apply]
  simp only [sectorCoordinateBond, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm]
  rw [twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm,
    twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm,
    threeSiteGlobalRegroupEquiv_symm_third,
    threeSiteGlobalRegroupEquiv_symm_third]
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hk : k = p
  · subst p
    by_cases hl : l = q
    · subst q
      by_cases hh : h = r
      · subst r
        simp [threeSiteSectorLeftBond, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hh,
          Matrix.one_apply]
    · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hl]
  · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hk]

/-- Regrouping the lift of the last two-site sector bond gives the dependent
direct sum of its fixed-sector actions.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem reindex_rightPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (rightPairMatrix F.sectorCoordinateBond) =
      F.threeSiteSectorRightBond := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rightPairMatrix,
    Matrix.kroneckerMap_apply]
  simp only [sectorCoordinateBond, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  rw [twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm,
    twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm,
    threeSiteGlobalRegroupEquiv_symm_first_apply,
    threeSiteGlobalRegroupEquiv_symm_first_apply]
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hl : l = q
  · subst q
    by_cases hh : h = r
    · subst r
      by_cases hk : k = p
      · subst p
        simp [threeSiteSectorRightBond, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hk,
          Matrix.one_apply]
    · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hh]
  · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hl]

/-- The first and second lifts of the complete two-site bond commute in
physical-sector coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem sectorCoordinatePairMatrices_comm
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.sectorCoordinateBond *
        rightPairMatrix F.sectorCoordinateBond =
      rightPairMatrix F.sectorCoordinateBond *
        leftPairMatrix F.sectorCoordinateBond := by
  apply (Matrix.reindex F.threeSiteGlobalRegroupEquiv
    F.threeSiteGlobalRegroupEquiv).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv)
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) =
    (Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv)
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv,
    Matrix.coe_reindexLinearEquiv,
    F.reindex_leftPairMatrix_sectorCoordinateBond,
    F.reindex_rightPairMatrix_sectorCoordinateBond,
    F.threeSiteSectorBonds_comm]

/-- The right-associated three-site product of the physical coordinate
matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def physicalCoordinateMatrixThree
    (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin d × (Fin d × Fin d)) ℂ :=
  F.physicalCoordinateMatrix ⊗ₖ
    (F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrix)

/-- The three-site physical coordinate matrix is a coisometry.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem physicalCoordinateMatrixThree_coisometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ = 1 := by
  simp [physicalCoordinateMatrixThree, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_coisometry]

/-- The second lifted physical bond is the three-site unitary transport of
the corresponding sector-coordinate lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem rightPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    rightPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (rightPairMatrix F.sectorCoordinateBond) := by
  simp [rightPairMatrix, physicalPairBond, sandwichMap_apply,
    physicalCoordinateMatrixTwo, physicalCoordinateMatrixThree,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    F.physicalCoordinateMatrix_isometry, Matrix.mul_assoc]

/-- The first lifted physical bond is the three-site unitary transport of
the corresponding sector-coordinate lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem leftPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (leftPairMatrix F.sectorCoordinateBond) := by
  ext x y
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  simp only [leftPairMatrix, physicalPairBond, physicalCoordinateMatrixTwo,
    physicalCoordinateMatrixThree, Matrix.conjTranspose_kronecker,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [sandwichMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [Matrix.one_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  let S : ℂ := ∑ a, ∑ b,
    (∑ c, ∑ e,
      star (F.physicalCoordinateMatrix c x.1) *
          star (F.physicalCoordinateMatrix e x.2.1) *
        F.sectorCoordinateBond (c, e) (a, b)) *
      (F.physicalCoordinateMatrix a y.1 *
        F.physicalCoordinateMatrix b y.2.1)
  have hthird :
      (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
        F.physicalCoordinateMatrix s y.2.2) =
        if x.2.2 = y.2.2 then 1 else 0 := by
    have h := congrFun (congrFun F.physicalCoordinateMatrix_isometry x.2.2) y.2.2
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hfactor :
      (∑ a, ∑ b, ∑ s,
        (∑ c, ∑ e,
          star (F.physicalCoordinateMatrix c x.1) *
              (star (F.physicalCoordinateMatrix e x.2.1) *
                star (F.physicalCoordinateMatrix s x.2.2)) *
            F.sectorCoordinateBond (c, e) (a, b)) *
          (F.physicalCoordinateMatrix a y.1 *
            (F.physicalCoordinateMatrix b y.2.1 *
              F.physicalCoordinateMatrix s y.2.2))) =
        S * (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
          F.physicalCoordinateMatrix s y.2.2) := by
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro e _
    ring
  change (if x.2.2 = y.2.2 then S else 0) = _
  calc
    _ = S * (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
        F.physicalCoordinateMatrix s y.2.2) := by
      rw [hthird]
      by_cases hxy : x.2.2 = y.2.2 <;> simp [hxy]
    _ = _ := hfactor.symm

/-- The first and second lifts of the transported two-site bond commute on
the three-site physical tensor product.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem physicalPairBonds_comm (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond * rightPairMatrix F.physicalPairBond =
      rightPairMatrix F.physicalPairBond * leftPairMatrix F.physicalPairBond := by
  rw [F.leftPairMatrix_physicalPairBond, F.rightPairMatrix_physicalPairBond]
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    _ = F.physicalCoordinateMatrixThreeᴴ *
        leftPairMatrix F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ) *
        rightPairMatrix F.sectorCoordinateBond *
        F.physicalCoordinateMatrixThree := by simp only [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixThree := by
      rw [F.sectorCoordinatePairMatrices_comm]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        rightPairMatrix F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ) *
        leftPairMatrix F.sectorCoordinateBond *
        F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The two adjacent translates of the physical bond commute on a three-site
window.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem physicalBond_zero_one_comm (F : PhysicalSectorFactorization K) :
    embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond =
      embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond := by
  apply (Matrix.reindex (finThreeArrowEquiv (Fin d))
    (finThreeArrowEquiv (Fin d))).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d))) (_ * _) =
    (Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d))) (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d)),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d)),
    Matrix.coe_reindexLinearEquiv, F.reindex_embedLocalOperator_zero,
    F.reindex_embedLocalOperator_one, F.physicalPairBonds_comm]

end MPOTensor.PhysicalSectorFactorization
