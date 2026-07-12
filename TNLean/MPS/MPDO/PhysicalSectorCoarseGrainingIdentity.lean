/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorCoarseGrainingAction
import TNLean.MPS.MPDO.PhysicalSectorClosureBlocks

/-!
# Coarse-graining identity for physical-sector closures

This file proves the fixed-point calculation for the coarse-graining channel
of Proposition C.7.  Both physical closures are first expressed in the sector
coordinates of the factorized tensor.  The three stages of the channel then
trace the four middle subspins, prepare the neighboring operator, and regroup
the remaining factors into two physical sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1547--1563
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The preparation stage annihilates entries between distinct pairs of
outer sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem NeighboringTraceFactorization.s1Map_apply_of_ne
    (H : NeighboringTraceFactorization F)
    (Y : Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ)
    {kh pq : Fin F.sectorCount × Fin F.sectorCount} (hne : kh ≠ pq)
    (a : BoundaryIndex F kh.1 kh.2) (u : NeighborIndex F kh.1 kh.2)
    (b : BoundaryIndex F pq.1 pq.2) (v : NeighborIndex F pq.1 pq.2) :
    H.s1Map Y ⟨kh, (a, u)⟩ ⟨pq, (b, v)⟩ = 0 := by
  classical
  rw [NeighboringTraceFactorization.s1Map,
    NeighboringTraceFactorization.completedNeighboringControlledMap,
    Matrix.controlledKrausMap_apply_of_ne _ _ Y hne]

/-- The coarse-graining channel sends the three-site physical closure to the
two-site physical closure for every virtual boundary matrix.

Source: arXiv:1606.00608, Proposition C.7, lines 1547--1563. -/
theorem NeighboringTraceFactorization.sMap_threeSiteClosure_eq_twoSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.sMap
        (Matrix.reindex F.threeSiteSectorCoordinateEquiv
          F.threeSiteSectorCoordinateEquiv
          (physClose3 F.sectorCoordinateTensor X)) =
      Matrix.reindex F.twoSiteSectorCoordinateEquiv F.twoSiteSectorCoordinateEquiv
        (physClose2 F.sectorCoordinateTensor X) := by
  ext ⟨⟨k, x⟩, h, y⟩ ⟨⟨p, z⟩, q, w⟩
  let Z := Matrix.reindex F.threeSiteSectorCoordinateEquiv
    F.threeSiteSectorCoordinateEquiv
    (physClose3 F.sectorCoordinateTensor X)
  by_cases hkp : k = p
  · subst p
    by_cases hhq : h = q
    · subst q
      have h0 := H.s0Map_block_eq_smul Z k h (F.boundaryOperator k h X)
        (F.s0Regrouped_threeSiteClosure_block_eq X k h)
      have h1 := H.s1Map_block_eq_kronecker (F.s0Map Z) k h
        (F.boundaryOperator k h X) h0
      have hs := congrFun (congrFun h1
        ((x.1, y.2), (x.2, y.1))) ((z.1, w.2), (z.2, w.1))
      have h2 := congrFun (congrFun (F.twoSiteSectorClosure_eq k h X)
        ((x.1, y.2), (x.2, y.1))) ((z.1, w.2), (z.2, w.1))
      simpa [Z, NeighboringTraceFactorization.sMap, LinearMap.comp_apply,
        s2Map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        twoSiteSectorCoordinateEquiv, twoSiteSectorClosure,
        twoSiteSectorEmbedding, twoSiteRegroupEquiv,
        s2ShiftEquiv] using hs.trans h2.symm
    · have hpair : (k, h) ≠ (k, q) := fun hp ↦ hhq (Prod.mk.inj hp).2
      have hs := H.s1Map_apply_of_ne (F.s0Map Z) hpair
        (x.1, y.2) (x.2, y.1) (z.1, w.2) (z.2, w.1)
      have hlhs : H.sMap Z (⟨k, x⟩, ⟨h, y⟩) (⟨k, z⟩, ⟨q, w⟩) = 0 := by
        simpa [NeighboringTraceFactorization.sMap, LinearMap.comp_apply,
          s2Map_apply, s2ShiftEquiv] using hs
      rw [hlhs]
      have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm ⟨h, y⟩)
          (F.sectorFinEquiv.symm ⟨q, w⟩) = 0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hhq y w beta alpha
      change 0 = physClose2 F.sectorCoordinateTensor X
        (F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨h, y⟩)
        (F.sectorFinEquiv.symm ⟨k, z⟩, F.sectorFinEquiv.symm ⟨q, w⟩)
      rw [physClose2_apply]
      rw [hz]
      simp
  · have hpair : (k, h) ≠ (p, q) := fun hp ↦ hkp (Prod.mk.inj hp).1
    have hs := H.s1Map_apply_of_ne (F.s0Map Z) hpair
      (x.1, y.2) (x.2, y.1) (z.1, w.2) (z.2, w.1)
    have hlhs : H.sMap Z (⟨k, x⟩, ⟨h, y⟩) (⟨p, z⟩, ⟨q, w⟩) = 0 := by
      simpa [NeighboringTraceFactorization.sMap, LinearMap.comp_apply,
        s2Map_apply, s2ShiftEquiv] using hs
    rw [hlhs]
    have hz : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨k, x⟩)
        (F.sectorFinEquiv.symm ⟨p, z⟩) = 0 := by
      ext beta alpha
      exact sectorCoordinateTensor_apply_ne F hkp x z beta alpha
    change 0 = physClose2 F.sectorCoordinateTensor X
      (F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨h, y⟩)
      (F.sectorFinEquiv.symm ⟨p, z⟩, F.sectorFinEquiv.symm ⟨q, w⟩)
    rw [physClose2_apply, hz]
    simp

end MPOTensor.PhysicalSectorFactorization
