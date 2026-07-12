/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorPositiveBond
import TNLean.MPS.MPDO.CommutingForm

/-!
# Commutativity of adjacent physical-sector bonds

This file proves the fixed-sector Kronecker-product calculation underlying
commutativity of two adjacent physical-sector bonds.  For sectors `k, l, h`,
the first bond acts on the neighboring factor $R_k \otimes L_l$, while the
second acts on $R_l \otimes L_h$.  It also identifies the two translated
bonds on three sites with the corresponding left and right tensor-product
lifts.  The two lifts are regrouped simultaneously over sector triples,
transported back to physical coordinates, and shown to commute on three
sites.

## Main results

* `reindex_leftPairMatrix_sectorCoordinateBond` and
  `reindex_rightPairMatrix_sectorCoordinateBond` identify the two regrouped
  sector-coordinate lifts.
* `sectorCoordinateBond_adjacent_comm_three` assembles the fixed-sector
  commutators over all sector triples.
* `leftPairMatrix_physicalPairBond` and `rightPairMatrix_physicalPairBond`
  give the exact three-site coordinate congruences.
* `physicalBond_adjacent_comm_three` proves commutativity of the two adjacent
  physical bonds on a three-site chain.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1589--1593
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Lift a two-site matrix to the first two factors of a right-associated
three-site tensor product.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
noncomputable def leftPairMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix (n × n) (n × n) ℂ) :
    Matrix (n × (n × n)) (n × (n × n)) ℂ :=
  Matrix.reindex (Equiv.prodAssoc n n n) (Equiv.prodAssoc n n n)
    (B ⊗ₖ (1 : Matrix n n ℂ))

/-- Lift a two-site matrix to the last two factors of a right-associated
three-site tensor product.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
noncomputable def rightPairMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix (n × n) (n × n) ℂ) :
    Matrix (n × (n × n)) (n × (n × n)) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ B

/-- On a three-site chain, embedding a two-site operator at the first site is
its left tensor-product lift after identifying configurations with triples.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem reindex_embedLocalOperator_zero (F : PhysicalSectorFactorization K) :
    Matrix.reindex (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond) =
      leftPairMatrix F.physicalPairBond := by
  ext σ τ
  have hAgree :
      AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3)
          ((finThreeArrowEquiv (Fin d)).symm σ)
          ((finThreeArrowEquiv (Fin d)).symm τ) ↔
        τ.2.2 = σ.2.2 := by
    constructor
    · intro ha
      have h := congrFun ha (2 : Fin 3)
      simpa [AgreesOutsideWindow, finThreeArrowEquiv,
        MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
    · intro ha
      funext i
      fin_cases i <;>
        simp [finThreeArrowEquiv,
          MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]
  by_cases h : τ.2.2 = σ.2.2
  · have ha := hAgree.mpr h
    simp [Matrix.reindex_apply, embedLocalOperator_apply, ha, leftPairMatrix,
      physicalBond, MPSTensor.extractWindow, h]
    simp [finThreeArrowEquiv]
  · have ha : ¬ AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3)
        ((finThreeArrowEquiv (Fin d)).symm σ)
        ((finThreeArrowEquiv (Fin d)).symm τ) := fun ha ↦ h (hAgree.mp ha)
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    simp only [leftPairMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply]
    change 0 = F.physicalPairBond (σ.1, σ.2.1) (τ.1, τ.2.1) *
      (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [if_neg (fun hs ↦ h hs.symm), mul_zero]

/-- On a three-site chain, embedding a two-site operator at the second site is
its right tensor-product lift after identifying configurations with triples.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem reindex_embedLocalOperator_one (F : PhysicalSectorFactorization K) :
    Matrix.reindex (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond) =
      rightPairMatrix F.physicalPairBond := by
  ext σ τ
  have hAgree :
      AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3)
          ((finThreeArrowEquiv (Fin d)).symm σ)
          ((finThreeArrowEquiv (Fin d)).symm τ) ↔
        τ.1 = σ.1 := by
    constructor
    · intro ha
      have h := congrFun ha (0 : Fin 3)
      simpa [finThreeArrowEquiv, MPSTensor.replaceWindow,
        MPSTensor.extractWindow] using h
    · intro ha
      funext i
      fin_cases i <;>
        simp [finThreeArrowEquiv, MPSTensor.replaceWindow,
          MPSTensor.extractWindow, ha]
  by_cases h : τ.1 = σ.1
  · have ha := hAgree.mpr h
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_pos ha]
    change F.physicalPairBond σ.2 τ.2 =
      (if σ.1 = τ.1 then 1 else 0) * F.physicalPairBond σ.2 τ.2
    rw [if_pos h.symm, one_mul]
  · have ha : ¬ AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3)
        ((finThreeArrowEquiv (Fin d)).symm σ)
        ((finThreeArrowEquiv (Fin d)).symm τ) := fun ha ↦ h (hAgree.mp ha)
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    simp only [rightPairMatrix, Matrix.kroneckerMap_apply]
    change 0 = (if σ.1 = τ.1 then 1 else 0) * F.physicalPairBond σ.2 τ.2
    rw [if_neg (fun hs ↦ h hs.symm), zero_mul]

/-- After three-site regrouping, the first translated sector-coordinate bond
is block diagonal. On the sector triple `(k, l, h)` it is the identity on the
outer boundary, followed by `ηₖₗ` and the identity on the second neighboring
factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem reindex_leftPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (leftPairMatrix F.sectorCoordinateBond) =
      Matrix.blockDiagonal' fun
          klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount) ↦
        (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
          (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
            (F.neighboringOperator klh.1 klh.2.1 ⊗ₖ
              (1 : Matrix (NeighborIndex F klh.2.1 klh.2.2)
                (NeighborIndex F klh.2.1 klh.2.2) ℂ)) := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hp : (k, (l, h)) = (p, (q, r))
  · cases hp
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, leftPairMatrix,
      Matrix.kroneckerMap_apply, Equiv.prodAssoc_symm_apply]
    simp only [sectorCoordinateBond, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_left,
      twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_left]
    rw [Matrix.blockDiagonal'_apply_eq]
    rw [threeSiteGlobalRegroupEquiv_symm_last,
      threeSiteGlobalRegroupEquiv_symm_last]
    by_cases ha : x.1.1 = y.1.1
    <;> by_cases hb : x.1.2 = y.1.2
    <;> by_cases hc : x.2.2.1 = y.2.2.1
    <;> by_cases hd : x.2.2.2 = y.2.2.2
    <;> simp [Matrix.one_apply, Prod.ext_iff,
      ha, hb, hc, hd]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, leftPairMatrix,
      Matrix.kroneckerMap_apply, Equiv.prodAssoc_symm_apply]
    simp only [sectorCoordinateBond, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_left,
      twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_left]
    by_cases hpairs : (k, l) = (p, q)
    · cases hpairs
      have hhr : h ≠ r := by
        intro hhr
        cases hhr
        exact hp rfl
      rw [Matrix.blockDiagonal'_apply_eq]
      rw [threeSiteGlobalRegroupEquiv_symm_last,
        threeSiteGlobalRegroupEquiv_symm_last]
      simp [Matrix.one_apply, hhr]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpairs, zero_mul]

/-- After three-site regrouping, the second translated sector-coordinate bond
is block diagonal. On the sector triple `(k, l, h)` it is the identity on the
outer boundary and on the first neighboring factor, followed by `ηₗₕ`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem reindex_rightPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (rightPairMatrix F.sectorCoordinateBond) =
      Matrix.blockDiagonal' fun
          klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount) ↦
        (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
          (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
            ((1 : Matrix (NeighborIndex F klh.1 klh.2.1)
              (NeighborIndex F klh.1 klh.2.1) ℂ) ⊗ₖ
                F.neighboringOperator klh.2.1 klh.2.2) := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hp : (k, (l, h)) = (p, (q, r))
  · cases hp
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rightPairMatrix,
      Matrix.kroneckerMap_apply]
    simp only [sectorCoordinateBond, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_right,
      twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_right]
    rw [Matrix.blockDiagonal'_apply_eq]
    rw [threeSiteGlobalRegroupEquiv_symm_first,
      threeSiteGlobalRegroupEquiv_symm_first]
    by_cases ha : x.1.1 = y.1.1
    <;> by_cases hb : x.1.2 = y.1.2
    <;> by_cases hc : x.2.1.1 = y.2.1.1
    <;> by_cases hd : x.2.1.2 = y.2.1.2
    <;> simp [Matrix.one_apply, Prod.ext_iff, ha, hb, hc, hd]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rightPairMatrix,
      Matrix.kroneckerMap_apply]
    simp only [sectorCoordinateBond, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_right,
      twoSiteGlobalRegroupEquiv_threeSiteGlobalRegroupEquiv_symm_right]
    by_cases hpairs : (l, h) = (q, r)
    · cases hpairs
      have hkp : k ≠ p := by
        intro hkp
        cases hkp
        exact hp rfl
      rw [Matrix.blockDiagonal'_apply_eq]
      rw [threeSiteGlobalRegroupEquiv_symm_first,
        threeSiteGlobalRegroupEquiv_symm_first]
      simp [Matrix.one_apply, hkp]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpairs, mul_zero]

/-- The right three-site lift of the physical bond is the transport of the
right lift of the sector-coordinate bond by the three-site coordinate
matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem rightPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    rightPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (rightPairMatrix F.sectorCoordinateBond) := by
  simp only [rightPairMatrix, physicalPairBond, sandwichMap_apply]
  rw [← F.physicalCoordinateMatrix_isometry]
  simp only [physicalCoordinateMatrixThree,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (F.physicalCoordinateMatrixᴴ ⊗ₖ
          (F.physicalCoordinateMatrixTwoᴴ * F.sectorCoordinateBond)) *
        (F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrixTwo) :=
      Matrix.mul_kronecker_mul _ _ _ _
    _ = ((F.physicalCoordinateMatrixᴴ *
          (1 : Matrix (Fin (Fintype.card (SectorSiteIndex F)))
            (Fin (Fintype.card (SectorSiteIndex F))) ℂ)) ⊗ₖ
          (F.physicalCoordinateMatrixTwoᴴ * F.sectorCoordinateBond)) *
        (F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrixTwo) := by
      simp
    _ = ((F.physicalCoordinateMatrixᴴ ⊗ₖ
          F.physicalCoordinateMatrixTwoᴴ) *
            ((1 : Matrix (Fin (Fintype.card (SectorSiteIndex F)))
              (Fin (Fintype.card (SectorSiteIndex F))) ℂ) ⊗ₖ
                F.sectorCoordinateBond)) *
        (F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrixTwo) := by
      rw [Matrix.mul_kronecker_mul]
    _ = _ := rfl

/-- The left three-site lift of the physical bond is the transport of the
left lift of the sector-coordinate bond by the three-site coordinate matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem leftPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (leftPairMatrix F.sectorCoordinateBond) := by
  simp only [leftPairMatrix, physicalPairBond, sandwichMap_apply]
  rw [← F.physicalCoordinateMatrix_isometry]
  simp only [physicalCoordinateMatrixTwo, physicalCoordinateMatrixThree,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_kronecker_mul]
  have hfactor :
      (((F.physicalCoordinateMatrixᴴ ⊗ₖ F.physicalCoordinateMatrixᴴ) *
          F.sectorCoordinateBond) ⊗ₖ F.physicalCoordinateMatrixᴴ) =
        (((F.physicalCoordinateMatrixᴴ ⊗ₖ F.physicalCoordinateMatrixᴴ) ⊗ₖ
          F.physicalCoordinateMatrixᴴ) *
            (F.sectorCoordinateBond ⊗ₖ
              (1 : Matrix (Fin (Fintype.card (SectorSiteIndex F)))
                (Fin (Fintype.card (SectorSiteIndex F))) ℂ))) := by
    calc
      _ = (((F.physicalCoordinateMatrixᴴ ⊗ₖ F.physicalCoordinateMatrixᴴ) *
            F.sectorCoordinateBond) ⊗ₖ
          (F.physicalCoordinateMatrixᴴ *
            (1 : Matrix (Fin (Fintype.card (SectorSiteIndex F)))
              (Fin (Fintype.card (SectorSiteIndex F))) ℂ))) := by
        simp
      _ = _ := Matrix.mul_kronecker_mul _ _ _ _
  rw [hfactor]
  let eP := Equiv.prodAssoc (Fin d) (Fin d) (Fin d)
  let eS := Equiv.prodAssoc
    (Fin (Fintype.card (SectorSiteIndex F)))
    (Fin (Fintype.card (SectorSiteIndex F)))
    (Fin (Fintype.card (SectorSiteIndex F)))
  have hreindex_outer
      (A : Matrix ((Fin d × Fin d) × Fin d)
        ((Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))) ×
            Fin (Fintype.card (SectorSiteIndex F))) ℂ)
      (B : Matrix ((Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))) ×
            Fin (Fintype.card (SectorSiteIndex F)))
        ((Fin d × Fin d) × Fin d) ℂ) :
      Matrix.reindex eP eP (A * B) =
        Matrix.reindex eP eS A * Matrix.reindex eS eP B := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv_mul ℂ ℂ eP eS eP A B).symm
  have hreindex_inner
      (A : Matrix ((Fin d × Fin d) × Fin d)
        ((Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))) ×
            Fin (Fintype.card (SectorSiteIndex F))) ℂ)
      (B : Matrix ((Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))) ×
            Fin (Fintype.card (SectorSiteIndex F)))
        ((Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))) ×
            Fin (Fintype.card (SectorSiteIndex F))) ℂ) :
      Matrix.reindex eP eS (A * B) =
        Matrix.reindex eP eS A * Matrix.reindex eS eS B := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv_mul ℂ ℂ eP eS eS A B).symm
  simp only [eP, eS] at hreindex_outer hreindex_inner
  calc
    _ = Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin d) (Fin d))
          (Equiv.prodAssoc
            (Fin (Fintype.card (SectorSiteIndex F)))
            (Fin (Fintype.card (SectorSiteIndex F)))
            (Fin (Fintype.card (SectorSiteIndex F))))
            ((F.physicalCoordinateMatrixᴴ ⊗ₖ F.physicalCoordinateMatrixᴴ) ⊗ₖ
              F.physicalCoordinateMatrixᴴ) *
        Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
          (F.sectorCoordinateBond ⊗ₖ
            (1 : Matrix (Fin (Fintype.card (SectorSiteIndex F)))
              (Fin (Fintype.card (SectorSiteIndex F))) ℂ)) *
        Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
          ((F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrix) ⊗ₖ
            F.physicalCoordinateMatrix) := by
      rw [hreindex_outer, hreindex_inner]
    _ = _ := by
      rw [Matrix.kronecker_assoc, Matrix.kronecker_assoc]

/-- On fixed physical sectors `(k, l, h)`, the two adjacent bonds commute.
The first neighboring operator acts on $R_k \otimes L_l$ and the second on
$R_l \otimes L_h$; all other tensor factors carry the identity.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem adjacentSectorBonds_comm (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount) :
    ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        (F.neighboringOperator k l ⊗ₖ
          (1 : Matrix (NeighborIndex F l h) (NeighborIndex F l h) ℂ))) *
      ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        ((1 : Matrix (NeighborIndex F k l) (NeighborIndex F k l) ℂ) ⊗ₖ
          F.neighboringOperator l h)) =
    ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        ((1 : Matrix (NeighborIndex F k l) (NeighborIndex F k l) ℂ) ⊗ₖ
          F.neighboringOperator l h)) *
      ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        (F.neighboringOperator k l ⊗ₖ
          (1 : Matrix (NeighborIndex F l h) (NeighborIndex F l h) ℂ))) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The two adjacent lifts of the sector-coordinate bond commute on three
sites. This assembles the fixed-sector calculation over the direct sum of
sector triples.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem sectorCoordinateBond_adjacent_comm_three
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.sectorCoordinateBond *
        rightPairMatrix F.sectorCoordinateBond =
      rightPairMatrix F.sectorCoordinateBond *
        leftPairMatrix F.sectorCoordinateBond := by
  apply (Matrix.reindex F.threeSiteGlobalRegroupEquiv
    F.threeSiteGlobalRegroupEquiv).injective
  change Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) =
    Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv]
  change Matrix.reindex F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv (leftPairMatrix F.sectorCoordinateBond) *
        Matrix.reindex F.threeSiteGlobalRegroupEquiv
          F.threeSiteGlobalRegroupEquiv
            (rightPairMatrix F.sectorCoordinateBond) =
    Matrix.reindex F.threeSiteGlobalRegroupEquiv
        F.threeSiteGlobalRegroupEquiv
          (rightPairMatrix F.sectorCoordinateBond) *
      Matrix.reindex F.threeSiteGlobalRegroupEquiv
        F.threeSiteGlobalRegroupEquiv (leftPairMatrix F.sectorCoordinateBond)
  rw [
    F.reindex_leftPairMatrix_sectorCoordinateBond,
    F.reindex_rightPairMatrix_sectorCoordinateBond,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext klh
  exact F.adjacentSectorBonds_comm klh.1 klh.2.1 klh.2.2

/-- The first and second lifts of the physical pair bond commute on three
sites.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem physicalPairBond_adjacent_comm_three
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond * rightPairMatrix F.physicalPairBond =
      rightPairMatrix F.physicalPairBond * leftPairMatrix F.physicalPairBond := by
  rw [F.leftPairMatrix_physicalPairBond,
    F.rightPairMatrix_physicalPairBond]
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    _ = F.physicalCoordinateMatrixThreeᴴ *
        leftPairMatrix F.sectorCoordinateBond *
          (F.physicalCoordinateMatrixThree *
            F.physicalCoordinateMatrixThreeᴴ) *
              rightPairMatrix F.sectorCoordinateBond *
                F.physicalCoordinateMatrixThree := by
      simp only [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) *
            F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond) *
            F.physicalCoordinateMatrixThree := by
      rw [F.sectorCoordinateBond_adjacent_comm_three]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        rightPairMatrix F.sectorCoordinateBond *
          (F.physicalCoordinateMatrixThree *
            F.physicalCoordinateMatrixThreeᴴ) *
              leftPairMatrix F.sectorCoordinateBond *
                F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The physical bond translated to the first and second positions of a
three-site chain commutes:
\[
  B_{01}B_{12}=B_{12}B_{01}.
\]

This is the three-site assertion only. Commutativity of all translates on an
arbitrary periodic chain, including the crossed two-site ordering, remains a
separate result.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem physicalBond_adjacent_comm_three
    (F : PhysicalSectorFactorization K) :
    embedLocalOperator (d := d) 2 3 (by omega) (0 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by omega) (1 : Fin 3) F.physicalBond =
      embedLocalOperator (d := d) 2 3 (by omega) (1 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by omega) (0 : Fin 3) F.physicalBond := by
  apply (Matrix.reindex (finThreeArrowEquiv (Fin d))
    (finThreeArrowEquiv (Fin d))).injective
  change Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d)) (_ * _) =
    Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d)) (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d)),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin d))
      (finThreeArrowEquiv (Fin d))]
  have hzero :
      Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
          (finThreeArrowEquiv (Fin d))
            (embedLocalOperator (d := d) 2 3 (by omega) (0 : Fin 3)
              F.physicalBond) =
        leftPairMatrix F.physicalPairBond := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      F.reindex_embedLocalOperator_zero
  have hone :
      Matrix.reindexLinearEquiv ℂ ℂ (finThreeArrowEquiv (Fin d))
          (finThreeArrowEquiv (Fin d))
            (embedLocalOperator (d := d) 2 3 (by omega) (1 : Fin 3)
              F.physicalBond) =
        rightPairMatrix F.physicalPairBond := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      F.reindex_embedLocalOperator_one
  rw [hzero, hone, F.physicalPairBond_adjacent_comm_three]

end MPOTensor.PhysicalSectorFactorization
