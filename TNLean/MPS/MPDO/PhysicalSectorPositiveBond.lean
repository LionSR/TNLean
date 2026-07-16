/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import TNLean.MPS.MPDO.PhysicalSectorClosureGlobal
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport

/-!
# Positive two-site bond from physical sectors

This file constructs the two-site bond associated with a physical-sector
factorization.  In regrouped sector coordinates, its block on sectors
`(k, h)` is the identity on the two outer factors tensored with the
neighboring operator `η_{k,h}`.  The bond is then transported to the original
two-site physical space and reindexed by two-site configurations.

The positivity proofs use only positivity of the neighboring operators.

## Main definitions

* `PhysicalSectorFactorization.sectorCoordinateBond`: the bond in the
  two-site sector coordinates.
* `PhysicalSectorFactorization.physicalPairBond`: the same bond on the
  original pair of physical indices.
* `PhysicalSectorFactorization.physicalBond`: the bond indexed by two-site
  physical configurations.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1581--1593
-/

open scoped Matrix ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The two-site bond in sector coordinates.  On the summand labeled by
`(k, h)`, it is the identity on the outer space
$B_k^L \otimes B_h^R$ tensored with the neighboring operator
$\eta_{k,h}$ on $B_k^R \otimes B_h^L$.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1581--1593. -/
noncomputable def sectorCoordinateBond (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.reindex F.twoSiteGlobalRegroupEquiv.symm
    F.twoSiteGlobalRegroupEquiv.symm
    (Matrix.blockDiagonal' fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
      (1 : Matrix (BoundaryIndex F kh.1 kh.2)
        (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ F.neighboringOperator kh.1 kh.2)

/-- The sector-coordinate bond is positive semidefinite whenever each
neighboring operator is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450 and Proposition C.8
(`3to4`), lines 1581--1593. -/
theorem sectorCoordinateBond_pos (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    F.sectorCoordinateBond.PosSemidef := by
  have hblock :
      (Matrix.blockDiagonal' fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
        (1 : Matrix (BoundaryIndex F kh.1 kh.2)
          (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ
            F.neighboringOperator kh.1 kh.2).PosSemidef := by
    apply Matrix.PosSemidef.blockDiagonal'
    intro kh
    exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one (hη kh.1 kh.2)
  simpa only [sectorCoordinateBond, Matrix.reindex_apply,
    Equiv.symm_symm] using hblock.submatrix F.twoSiteGlobalRegroupEquiv

/-- The two-site bond transported from sector coordinates to the original
pair of physical indices.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1581--1593. -/
noncomputable def physicalPairBond (F : PhysicalSectorFactorization K) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  singleKrausMap F.physicalCoordinateMatrixTwoᴴ F.sectorCoordinateBond

/-- The transported bond on the original pair of physical indices is positive
semidefinite whenever each neighboring operator is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450 and Proposition C.8
(`3to4`), lines 1581--1593. -/
theorem physicalPairBond_pos (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    F.physicalPairBond.PosSemidef := by
  exact (F.sectorCoordinateBond_pos hη).mul_mul_conjTranspose_same
    F.physicalCoordinateMatrixTwoᴴ

/-- The transported two-site bond, indexed by configurations
`Fin 2 → Fin d`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1581--1593. -/
noncomputable def physicalBond (F : PhysicalSectorFactorization K) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
    (finTwoArrowEquiv (Fin d)).symm F.physicalPairBond

/-- The transported bond on two-site physical configurations is positive
semidefinite whenever each neighboring operator is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450 and Proposition C.8
(`3to4`), lines 1581--1593. -/
theorem physicalBond_pos (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    F.physicalBond.PosSemidef := by
  simpa only [physicalBond, Matrix.reindex_apply, Equiv.symm_symm] using
    (F.physicalPairBond_pos hη).submatrix (finTwoArrowEquiv (Fin d))

end MPOTensor.PhysicalSectorFactorization
