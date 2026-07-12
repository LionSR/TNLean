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
lifts.  Their simultaneous transport through the sector decomposition is a
subsequent step.

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

end MPOTensor.PhysicalSectorFactorization
