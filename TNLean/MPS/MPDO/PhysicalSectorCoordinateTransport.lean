/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBlockedRFP

/-!
# Physical-coordinate transport of sector closures

This file identifies the two-site and four-site closures in the physical
sector coordinates of Proposition C.7 with unitary congruences of the
corresponding closures in the original physical coordinates.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, direction (iv) implies (v), and Appendix C.2, lines 1510--1563
  and 1821--1825

**Scope restriction (active physical support compression):** the explicit
`changePhysicalBasis` operation and the two-site/four-site closure transport
identities do not appear as standalone constructions in CPSV16.  The source
uses the physical isometry $U$ from Lemma `propSN` to transport closures
implicitly inside the proof of Theorem 4.9; this file isolates the transport
as a reusable algebraic construction.  It is independent of the active
factor-support compression.  Recorded in
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The equivalence between the original physical indices and the finite
encoding of the sector-coordinate indices. -/
noncomputable def physicalFinEquiv
    (F : PhysicalSectorFactorization K) :
    Fin d ≃ Fin (Fintype.card (SectorSiteIndex F)) :=
  F.sectorEquiv.trans F.sectorFinEquiv.symm

/-- The physical isometry with its output index written in the finite
sector-coordinate encoding. -/
noncomputable def physicalCoordinateMatrix
    (F : PhysicalSectorFactorization K) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F))) (Fin d) ℂ :=
  Matrix.reindex F.physicalFinEquiv (Equiv.refl (Fin d)) F.physicalIsometry

theorem physicalIsometry_mul_conjTranspose
    (F : PhysicalSectorFactorization K) :
    F.physicalIsometry * F.physicalIsometryᴴ = 1 := by
  have hmem : F.physicalIsometry ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact F.physicalIsometry_isometry
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hmem)

theorem physicalCoordinateMatrix_isometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixᴴ * F.physicalCoordinateMatrix = 1 := by
  ext i j
  simp only [physicalCoordinateMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply]
  rw [← F.physicalFinEquiv.sum_comp (fun x ↦
    star (F.physicalIsometry (F.physicalFinEquiv.symm x) i) *
      F.physicalIsometry (F.physicalFinEquiv.symm x) j)]
  simpa only [Equiv.symm_apply_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using
    congrFun (congrFun F.physicalIsometry_isometry i) j

theorem physicalCoordinateMatrix_coisometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrix * F.physicalCoordinateMatrixᴴ = 1 := by
  ext i j
  simpa only [physicalCoordinateMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Matrix.one_apply,
    Equiv.apply_eq_iff_eq] using
    congrFun (congrFun F.physicalIsometry_mul_conjTranspose
      (F.physicalFinEquiv.symm i)) (F.physicalFinEquiv.symm j)

/-- Change the physical coordinates of an MPO tensor by a rectangular matrix. -/
noncomputable def changePhysicalBasis {e : ℕ}
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D) : MPOTensor e D :=
  fun i j beta alpha ↦ (V * physicalSlice M beta alpha * Vᴴ) i j

/-- Successive changes of physical coordinates multiply their coordinate
matrices. -/
theorem changePhysicalBasis_changePhysicalBasis
    {a b : ℕ} (U : Matrix (Fin a) (Fin b) ℂ)
    (V : Matrix (Fin b) (Fin d) ℂ) (M : MPOTensor d D) :
    changePhysicalBasis U (changePhysicalBasis V M) =
      changePhysicalBasis (U * V) M := by
  ext i j beta alpha
  change (U * (V * physicalSlice M beta alpha * Vᴴ) * Uᴴ) i j =
    ((U * V) * physicalSlice M beta alpha * (U * V)ᴴ) i j
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A physical coordinate change commutes with a scalar multiplying every
local MPO matrix. -/
theorem changePhysicalBasis_smul
    {e : ℕ} (V : Matrix (Fin e) (Fin d) ℂ) (c : ℂ) (M : MPOTensor d D) :
    changePhysicalBasis V (c • M) = c • changePhysicalBasis V M := by
  ext i j beta alpha
  simp only [changePhysicalBasis, physicalSlice, Pi.smul_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sectorCoordinateTensor_eq_changePhysicalBasis
    (F : PhysicalSectorFactorization K) :
    F.sectorCoordinateTensor = changePhysicalBasis F.physicalCoordinateMatrix K := by
  ext i j beta alpha
  simp [sectorCoordinateTensor_apply, transformedPhysicalSlice,
    changePhysicalBasis, physicalCoordinateMatrix, physicalFinEquiv,
    Matrix.reindex_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The two-site product of the physical coordinate matrix. -/
noncomputable def physicalCoordinateMatrixTwo
    (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin d × Fin d) ℂ :=
  Matrix.kroneckerMap (· * ·)
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix

/-- The right-associated four-site product of the physical coordinate matrix. -/
noncomputable def physicalCoordinateMatrixFour
    (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F)))))
      (Fin d × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.kroneckerMap (· * ·) F.physicalCoordinateMatrix
    (Matrix.kroneckerMap (· * ·) F.physicalCoordinateMatrix
      (Matrix.kroneckerMap (· * ·)
        F.physicalCoordinateMatrix F.physicalCoordinateMatrix))

theorem physicalCoordinateMatrixTwo_isometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixTwoᴴ * F.physicalCoordinateMatrixTwo = 1 := by
  rw [physicalCoordinateMatrixTwo, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_isometry]
  exact Matrix.one_kronecker_one

theorem physicalCoordinateMatrixTwo_coisometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixTwo * F.physicalCoordinateMatrixTwoᴴ = 1 := by
  rw [physicalCoordinateMatrixTwo, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_coisometry]
  exact Matrix.one_kronecker_one

theorem physicalCoordinateMatrixFour_isometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixFourᴴ * F.physicalCoordinateMatrixFour = 1 := by
  simp only [physicalCoordinateMatrixFour, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_isometry]
  repeat' rw [Matrix.one_kronecker_one]

theorem physicalCoordinateMatrixFour_coisometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixFour * F.physicalCoordinateMatrixFourᴴ = 1 := by
  simp only [physicalCoordinateMatrixFour, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_coisometry]
  repeat' rw [Matrix.one_kronecker_one]

theorem changePhysicalBasis_apply_eq_sum {e : ℕ}
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D)
    (i j : Fin e) :
    changePhysicalBasis V M i j =
      ∑ p : Fin d × Fin d,
        (V i p.1 * star (V j p.2)) • M p.1 p.2 := by
  ext beta alpha
  simp only [changePhysicalBasis, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, Fintype.sum_prod_type, physicalSlice]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  ring

/-- The two-site closure transforms by the two-site physical coordinate
matrix. -/
theorem physicalCoordinateMatrixTwo_physClose2
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap F.physicalCoordinateMatrixTwo (physClose2 K X) =
      physClose2 F.sectorCoordinateTensor X := by
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [physClose2_apply]
  simp_rw [changePhysicalBasis_apply_eq_sum]
  simp only [singleKrausMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalCoordinateMatrixTwo, Matrix.kroneckerMap_apply, physClose2_apply,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, star_mul']
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  let e : ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      ((Fin d × Fin d) × (Fin d × Fin d)) := {
    toFun := fun p : ((Fin d × Fin d) × (Fin d × Fin d)) ↦
      ((p.2.2, p.1.2), (p.2.1, p.1.1))
    invFun := fun p : ((Fin d × Fin d) × (Fin d × Fin d)) ↦
      ((p.2.2, p.1.2), (p.2.1, p.1.1))
    left_inv _ := rfl
    right_inv _ := rfl }
  have h := Fintype.sum_equiv e
      (fun p ↦
        F.physicalCoordinateMatrix i₁ p.2.1 *
          F.physicalCoordinateMatrix i₂ p.2.2 *
          Matrix.trace (K p.2.1 p.1.1 * K p.2.2 p.1.2 * X) *
          (star (F.physicalCoordinateMatrix j₁ p.1.1) *
            star (F.physicalCoordinateMatrix j₂ p.1.2)))
      (fun p ↦
        F.physicalCoordinateMatrix i₂ p.1.1 *
          star (F.physicalCoordinateMatrix j₂ p.1.2) *
          (F.physicalCoordinateMatrix i₁ p.2.1 *
            star (F.physicalCoordinateMatrix j₁ p.2.2) *
            Matrix.trace (K p.2.1 p.2.2 * K p.1.1 p.1.2 * X)))
      (fun _ ↦ by dsimp [e]; ring)
  rw [Fintype.sum_prod_type] at h
  conv at h =>
    rhs
    rw [Fintype.sum_prod_type]
  exact h

/-- The four-site closure transforms by the four-site physical coordinate
matrix. -/
theorem physicalCoordinateMatrixFour_physClose4
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap F.physicalCoordinateMatrixFour (physClose4 K X) =
      physClose4 F.sectorCoordinateTensor X := by
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩
  simp only [physClose4_apply]
  simp_rw [changePhysicalBasis_apply_eq_sum]
  simp only [singleKrausMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalCoordinateMatrixFour, Matrix.kroneckerMap_apply, physClose4_apply,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, star_mul']
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  let e :
      ((Fin d × (Fin d × (Fin d × Fin d))) ×
        (Fin d × (Fin d × (Fin d × Fin d)))) ≃
      ((((Fin d × Fin d) × (Fin d × Fin d)) × (Fin d × Fin d)) ×
        (Fin d × Fin d)) := {
    toFun := fun p ↦
      ((((p.2.2.2.2, p.1.2.2.2), (p.2.2.2.1, p.1.2.2.1)),
        (p.2.2.1, p.1.2.1)), (p.2.1, p.1.1))
    invFun := fun p ↦
      ((p.2.2, (p.1.2.2, (p.1.1.2.2, p.1.1.1.2))),
        (p.2.1, (p.1.2.1, (p.1.1.2.1, p.1.1.1.1))))
    left_inv _ := rfl
    right_inv _ := rfl }
  have h := Fintype.sum_equiv e
      (fun p ↦
        F.physicalCoordinateMatrix i₁ p.2.1 *
          (F.physicalCoordinateMatrix i₂ p.2.2.1 *
            (F.physicalCoordinateMatrix i₃ p.2.2.2.1 *
              F.physicalCoordinateMatrix i₄ p.2.2.2.2)) *
          Matrix.trace
            (K p.2.1 p.1.1 * K p.2.2.1 p.1.2.1 *
              K p.2.2.2.1 p.1.2.2.1 * K p.2.2.2.2 p.1.2.2.2 * X) *
          (star (F.physicalCoordinateMatrix j₁ p.1.1) *
            (star (F.physicalCoordinateMatrix j₂ p.1.2.1) *
              (star (F.physicalCoordinateMatrix j₃ p.1.2.2.1) *
                star (F.physicalCoordinateMatrix j₄ p.1.2.2.2)))))
      (fun p ↦
        F.physicalCoordinateMatrix i₄ p.1.1.1.1 *
          star (F.physicalCoordinateMatrix j₄ p.1.1.1.2) *
          (F.physicalCoordinateMatrix i₃ p.1.1.2.1 *
            star (F.physicalCoordinateMatrix j₃ p.1.1.2.2) *
            (F.physicalCoordinateMatrix i₂ p.1.2.1 *
              star (F.physicalCoordinateMatrix j₂ p.1.2.2) *
              (F.physicalCoordinateMatrix i₁ p.2.1 *
                star (F.physicalCoordinateMatrix j₁ p.2.2) *
                Matrix.trace
                  (K p.2.1 p.2.2 * K p.1.2.1 p.1.2.2 *
                    K p.1.1.2.1 p.1.1.2.2 * K p.1.1.1.1 p.1.1.1.2 * X)))))
      (fun _ ↦ by dsimp [e]; ring)
  rw [Fintype.sum_prod_type] at h
  conv at h =>
    rhs
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
  exact h

theorem physicalCoordinateMatrixTwo_conjTranspose_physClose2
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap F.physicalCoordinateMatrixTwoᴴ
        (physClose2 F.sectorCoordinateTensor X) =
      physClose2 K X := by
  rw [← F.physicalCoordinateMatrixTwo_physClose2]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc, F.physicalCoordinateMatrixTwo_isometry,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, F.physicalCoordinateMatrixTwo_isometry, Matrix.mul_one]

theorem physicalCoordinateMatrixFour_conjTranspose_physClose4
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap F.physicalCoordinateMatrixFourᴴ
        (physClose4 F.sectorCoordinateTensor X) =
      physClose4 K X := by
  rw [← F.physicalCoordinateMatrixFour_physClose4]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc, F.physicalCoordinateMatrixFour_isometry,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, F.physicalCoordinateMatrixFour_isometry, Matrix.mul_one]

end MPOTensor.PhysicalSectorFactorization
