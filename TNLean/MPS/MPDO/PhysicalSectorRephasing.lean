/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Circle
import TNLean.Algebra.KroneckerFactorPositivity
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition
import TNLean.MPS.MPDO.PhysicalSectorSupportRecurrence

/-!
# Rephasing a physical-sector factorization

Multiplying the left tensor in sector `k` by a unit complex number `z_k` and
the right tensor by `z_k⁻¹` leaves the physical-slice factorization
unchanged. The neighboring operator from sector `k` to sector `h` is then
multiplied by `z_k⁻¹ z_h`.

This is the sector rephasing used in the positive-choice argument for the
neighboring operators in Appendix C.2 of arXiv:1606.00608.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1441--1450
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Rephase the left and right tensors of each physical sector by reciprocal
unit complex scalars. The reciprocal scalars preserve every same-sector
Kronecker factorization.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
noncomputable def rephase (F : PhysicalSectorFactorization K)
    (z : Fin F.sectorCount → Circle) : PhysicalSectorFactorization K where
  sectorCount := F.sectorCount
  leftDim := F.leftDim
  rightDim := F.rightDim
  leftDim_pos := F.leftDim_pos
  rightDim_pos := F.rightDim_pos
  sectorEquiv := F.sectorEquiv
  physicalIsometry := F.physicalIsometry
  physicalIsometry_isometry := F.physicalIsometry_isometry
  leftTensor := fun k beta ↦ (z k : ℂ) • F.leftTensor k beta
  rightTensor := fun k alpha ↦ ((z k : ℂ)⁻¹) • F.rightTensor k alpha
  factorization := by
    intro beta alpha
    rw [F.factorization beta alpha]
    congr 1
    funext k
    exact (Matrix.smul_kronecker_smul_inv_eq
      (F.leftTensor k beta) (F.rightTensor k alpha) (Circle.coe_ne_zero (z k))).symm

/-- Rephasing the sector tensors multiplies the neighboring operator from
sector `k` to sector `h` by the vertex-phase ratio `z_k⁻¹ z_h`.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem rephase_neighboringOperator (F : PhysicalSectorFactorization K)
    (z : Fin F.sectorCount → Circle) (k h : Fin F.sectorCount) :
    (F.rephase z).neighboringOperator k h =
      ((((z k)⁻¹ * z h : Circle) : ℂ) • F.neighboringOperator k h) := by
  ext x y
  simp only [neighboringOperator_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (((z k : ℂ)⁻¹) * F.rightTensor k a x.1 y.1) *
      ((z h : ℂ) * F.leftTensor h a x.2 y.2) = _
  simp only [Circle.coe_mul, Circle.coe_inv]
  ring

/-- Reciprocal sector rephasing leaves each sector virtual matrix unchanged.

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1450. -/
@[simp] theorem rephase_sectorVirtualMatrix (F : PhysicalSectorFactorization K)
    (z : Fin F.sectorCount → Circle) (k : Fin F.sectorCount)
    (x y : F.SectorIndex k) :
    (F.rephase z).sectorVirtualMatrix k x y =
      F.sectorVirtualMatrix k x y := by
  ext beta alpha
  simp only [sectorVirtualMatrix, rephase, Matrix.smul_apply, smul_eq_mul]
  field_simp [Circle.coe_ne_zero]

/-- Reciprocal sector rephasing preserves the nonzero neighboring support.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem rephase_neighboringOperator_ne_zero_iff
    (F : PhysicalSectorFactorization K) (z : Fin F.sectorCount → Circle)
    (k h : Fin F.sectorCount) :
    (F.rephase z).neighboringOperator k h ≠ 0 ↔
      F.neighboringOperator k h ≠ 0 := by
  rw [F.rephase_neighboringOperator]
  exact smul_ne_zero_iff_right
    (mul_ne_zero (Circle.coe_ne_zero ((z k)⁻¹)) (Circle.coe_ne_zero (z h)))

/-- Reciprocal sector rephasing leaves every complete cyclic product of
neighboring operators unchanged.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem rephase_cyclicNeighboringProduct (F : PhysicalSectorFactorization K)
    (z : Fin F.sectorCount → Circle) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    (F.rephase z).cyclicNeighboringProduct k = F.cyclicNeighboringProduct k := by
  rw [← (F.rephase z).mpo_submatrix_sector_eq_cyclicNeighboringProduct k,
    ← F.mpo_submatrix_sector_eq_cyclicNeighboringProduct k]
  rfl

end MPOTensor.PhysicalSectorFactorization
