/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorClosureBlocks
import TNLean.MPS.MPDO.PhysicalSectorRefinementAction

/-!
# Refinement identity for physical-sector closures

This file proves the fixed-point calculation for the refinement channel of
Proposition C.7. The first two stages replace the neighboring factor in each
outer-sector block of the two-site closure by its three-site counterpart. The
last stage returns from the prepared coordinates to three physical sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1510--1516 and 1522--1545
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The refinement channel sends the two-site physical closure to the
three-site physical closure for every virtual boundary matrix.

**Local fix (zero-weight quotient):** the preparation density is completed on
zero-weight outer-sector pairs. The factor produced by the first stage and
the corresponding three-site neighboring operator both vanish there, so the
completion does not change the identity. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545. -/
theorem NeighboringTraceFactorization.tMap_twoSiteClosure_eq_threeSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.tMap
        (Matrix.reindex F.twoSiteSectorCoordinateEquiv
          F.twoSiteSectorCoordinateEquiv
          (physClose2 F.sectorCoordinateTensor X)) =
      Matrix.reindex F.threeSiteSectorCoordinateEquiv
        F.threeSiteSectorCoordinateEquiv
        (physClose3 F.sectorCoordinateTensor X) := by
  let Z₂ := Matrix.reindex F.twoSiteSectorCoordinateEquiv
    F.twoSiteSectorCoordinateEquiv
    (physClose2 F.sectorCoordinateTensor X)
  let Z₃ := Matrix.reindex F.threeSiteSectorCoordinateEquiv
    F.threeSiteSectorCoordinateEquiv
    (physClose3 F.sectorCoordinateTensor X)
  have hprepared :
      H.t1Map (F.t0Map Z₂) = Matrix.equivReindexMap F.s0RegroupEquiv Z₃ := by
    ext ⟨kh, a, u⟩ ⟨pq, b, v⟩
    by_cases hp : kh = pq
    · subst pq
      have h₀ := H.t0Map_block_eq_smul Z₂ kh.1 kh.2
        (F.boundaryOperator kh.1 kh.2 X)
        (F.t0Regrouped_twoSiteClosure_block_eq X kh.1 kh.2)
      have h₁ := H.t1Map_block_eq_kronecker (F.t0Map Z₂) kh.1 kh.2
        (F.boundaryOperator kh.1 kh.2 X) h₀
      have hl := congrFun (congrFun h₁ (a, u)) (b, v)
      have hr := congrFun
        (congrFun (F.s0Regrouped_threeSiteClosure_block_eq X kh.1 kh.2)
          (a, u)) (b, v)
      simpa [Z₂, Z₃, Matrix.submatrix_apply] using hl.trans hr.symm
    · have hl := H.t1Map_apply_of_ne (F.t0Map Z₂) hp a u b v
      have hr := F.s0Regrouped_threeSiteClosure_apply_of_outer_ne X hp a u b v
      exact hl.trans hr.symm
  change F.t2Map (H.t1Map (F.t0Map Z₂)) = Z₃
  rw [hprepared]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ F.s0RegroupEquiv F.s0RegroupEquiv).symm
        ((Matrix.reindexLinearEquiv ℂ ℂ F.s0RegroupEquiv F.s0RegroupEquiv) Z₃) = Z₃
  exact
    (Matrix.reindexLinearEquiv ℂ ℂ F.s0RegroupEquiv F.s0RegroupEquiv).symm_apply_apply Z₃

end MPOTensor.PhysicalSectorFactorization
