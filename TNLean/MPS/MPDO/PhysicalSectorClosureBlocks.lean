/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorClosureCoordinates
import TNLean.MPS.MPDO.PhysicalSectorOmegaPreparation

/-!
# Outer-sector blocks of the three-site closure

This file expresses the regrouped three-site physical closure in blocks
indexed by its two outer sectors. Each diagonal block is the boundary
operator tensored with the three-site neighboring operator, and every entry
between distinct outer-sector pairs vanishes.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1435--1448 and 1510--1516
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- On an outer-sector pair, the regrouped three-site physical closure is
the boundary operator tensored with the three-site neighboring operator.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448 and 1510--1516. -/
theorem s0Regrouped_threeSiteClosure_block_eq
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ)
    (k h : Fin F.sectorCount) :
    (Matrix.equivReindexMap F.s0RegroupEquiv
      (Matrix.reindex F.threeSiteSectorCoordinateEquiv
        F.threeSiteSectorCoordinateEquiv
        (physClose3 F.sectorCoordinateTensor X))).submatrix
          (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      F.boundaryOperator k h X ⊗ₖ F.threeSiteNeighboringOperator k h := by
  ext ⟨a, l, u⟩ ⟨b, m, v⟩
  by_cases hlm : l = m
  · subst m
    have hg := congrFun (congrFun (F.threeSiteSectorClosure_eq k l h X)
      (a, u)) (b, v)
    simpa [Matrix.equivReindexMap, Matrix.reindex_apply, Matrix.submatrix_apply,
      s0RegroupEquiv, threeSiteSectorCoordinateEquiv,
      threeSiteSectorClosure, threeSiteSectorEmbedding,
      threeSiteNeighboringOperator,
      Matrix.blockDiagonal'_apply] using hg
  · have hz : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨l, (u.1.2, u.2.1)⟩)
        (F.sectorFinEquiv.symm ⟨m, (v.1.2, v.2.1)⟩) = 0 := by
      ext beta alpha
      exact sectorCoordinateTensor_apply_ne F hlm _ _ beta alpha
    change Matrix.trace
      (F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨k, (a.1, u.1.1)⟩)
          (F.sectorFinEquiv.symm ⟨k, (b.1, v.1.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨l, (u.1.2, u.2.1)⟩)
          (F.sectorFinEquiv.symm ⟨m, (v.1.2, v.2.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨h, (u.2.2, a.2)⟩)
          (F.sectorFinEquiv.symm ⟨h, (v.2.2, b.2)⟩) * X) =
      F.boundaryOperator k h X a b *
        F.threeSiteNeighboringOperator k h ⟨l, u⟩ ⟨m, v⟩
    rw [hz]
    simp [threeSiteNeighboringOperator, Matrix.blockDiagonal'_apply, hlm]

/-- Between distinct outer-sector pairs, the regrouped three-site physical
closure vanishes.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1448. -/
theorem s0Regrouped_threeSiteClosure_apply_of_outer_ne
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ)
    {kh pq : Fin F.sectorCount × Fin F.sectorCount} (hne : kh ≠ pq)
    (a : BoundaryIndex F kh.1 kh.2)
    (u : ThreeSiteMiddleIndex F kh.1 kh.2)
    (b : BoundaryIndex F pq.1 pq.2)
    (v : ThreeSiteMiddleIndex F pq.1 pq.2) :
    Matrix.equivReindexMap F.s0RegroupEquiv
        (Matrix.reindex F.threeSiteSectorCoordinateEquiv
          F.threeSiteSectorCoordinateEquiv
          (physClose3 F.sectorCoordinateTensor X))
        ⟨kh, (a, u)⟩ ⟨pq, (b, v)⟩ = 0 := by
  rcases u with ⟨l, u⟩
  rcases v with ⟨m, v⟩
  have houter : kh.1 ≠ pq.1 ∨ kh.2 ≠ pq.2 := by
    exact not_and_or.mp (fun h ↦ hne (Prod.ext h.1 h.2))
  rcases houter with hfirst | hthird
  · have hz : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨kh.1, (a.1, u.1.1)⟩)
        (F.sectorFinEquiv.symm ⟨pq.1, (b.1, v.1.1)⟩) = 0 := by
      ext beta alpha
      exact sectorCoordinateTensor_apply_ne F hfirst _ _ beta alpha
    change Matrix.trace
      (F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨kh.1, (a.1, u.1.1)⟩)
          (F.sectorFinEquiv.symm ⟨pq.1, (b.1, v.1.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨l, (u.1.2, u.2.1)⟩)
          (F.sectorFinEquiv.symm ⟨m, (v.1.2, v.2.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨kh.2, (u.2.2, a.2)⟩)
          (F.sectorFinEquiv.symm ⟨pq.2, (v.2.2, b.2)⟩) * X) = 0
    rw [hz]
    simp
  · have hz : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨kh.2, (u.2.2, a.2)⟩)
        (F.sectorFinEquiv.symm ⟨pq.2, (v.2.2, b.2)⟩) = 0 := by
      ext beta alpha
      exact sectorCoordinateTensor_apply_ne F hthird _ _ beta alpha
    change Matrix.trace
      (F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨kh.1, (a.1, u.1.1)⟩)
          (F.sectorFinEquiv.symm ⟨pq.1, (b.1, v.1.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨l, (u.1.2, u.2.1)⟩)
          (F.sectorFinEquiv.symm ⟨m, (v.1.2, v.2.1)⟩) *
        F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨kh.2, (u.2.2, a.2)⟩)
          (F.sectorFinEquiv.symm ⟨pq.2, (v.2.2, b.2)⟩) * X) = 0
    rw [hz]
    simp

end MPOTensor.PhysicalSectorFactorization
