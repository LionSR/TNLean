/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.PhysicalSector.PhysicalSectorCoarseGraining
import TNLean.MPS.Operator.PhysicalSector.PhysicalSectorOmegaPreparation
import TNLean.MPS.Operator.PhysicalSector.PhysicalSectorRefinementAction

/-!
# Action of the physical-sector coarse-graining maps

This file computes the diagonal-sector action of the three maps in the
coarse-graining channel of Proposition C.7.  The four middle subspins of a
three-site sector carry

\[
  \Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h}).
\]

The first map traces this matrix and gives the coefficient \(a_kb_h\).  The
second map adjoins the normalized neighboring operator.  The coefficient
cancels the normalization on active sectors; on zero-weight sectors both
sides vanish.  The third map only relabels the remaining subspins as two
complete physical sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1547--1563

## Coarse-graining identity for physical-sector closures

This file proves the fixed-point calculation for the coarse-graining channel
of Proposition C.7.  Both physical closures are first expressed in the sector
coordinates of the factorized tensor.  The three stages of the channel then
trace the four middle subspins, prepare the neighboring operator, and regroup
the remaining factors into two physical sites.

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1547--1563
-/

section

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- On a diagonal outer-sector pair, \(\mathcal S_0\) is the partial trace
of the corresponding regrouped block.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
theorem s0Map_sameBlock_apply (F : PhysicalSectorFactorization K)
    (X : Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
      (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ)
    (k h : Fin F.sectorCount) (a b : BoundaryIndex F k h) :
    F.s0Map X ⟨(k, h), a⟩ ⟨(k, h), b⟩ =
      Matrix.partialTraceRight
        ((Matrix.equivReindexMap F.s0RegroupEquiv X).submatrix
          (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p)) a b := by
  rw [s0Map, LinearMap.comp_apply,
    Matrix.controlledPartialTraceRightLM_sameBlock_apply]

/-- If a regrouped diagonal block is
\(B\otimes\Omega_{k,h}\), then \(\mathcal S_0\) maps it to
\((a_kb_h)B\).

Source: arXiv:1606.00608, Appendix C.2, lines 1547--1555. -/
theorem NeighboringTraceFactorization.s0Map_block_eq_smul
    (H : NeighboringTraceFactorization F)
    (X : Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
      (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ)
    (k h : Fin F.sectorCount) (B : Matrix (BoundaryIndex F k h)
      (BoundaryIndex F k h) ℂ)
    (hblock :
      (Matrix.equivReindexMap F.s0RegroupEquiv X).submatrix
        (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p) =
          B ⊗ₖ F.threeSiteNeighboringOperator k h) :
    (F.s0Map X).submatrix (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      ((H.a k * H.b h : ℝ) : ℂ) • B := by
  ext a b
  rw [Matrix.submatrix_apply, F.s0Map_sameBlock_apply, hblock,
    Matrix.partialTraceRight_kronecker,
    H.trace_threeSiteNeighboringOperator, Matrix.smul_apply]

/-- Multiplying a boundary matrix by \(a_kb_h\) and then adjoining the
completed normalized neighboring density gives exactly
\(B\otimes\eta_{k,h}\).  This includes zero-weight sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem NeighboringTraceFactorization.completedNeighboringPreparationMap_smul
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (B : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) :
    H.completedNeighboringPreparationMap F.neighborIndex_nonempty k h
        (((H.a k * H.b h : ℝ) : ℂ) • B) =
      B ⊗ₖ F.neighboringOperator k h := by
  classical
  by_cases hactive : H.a k * H.b h ≠ 0
  · rw [H.completedNeighboringPreparationMap_eq_normalized
      F.neighborIndex_nonempty k h hactive]
    ext p q
    change Matrix.kroneckerMap (· * ·)
        (((H.a k * H.b h : ℝ) : ℂ) • B)
        ((((H.a k * H.b h)⁻¹ : ℝ) : ℂ) • F.neighboringOperator k h) p q = _
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    have hcancel :
        ((H.a k * H.b h : ℝ) : ℂ) * (((H.a k * H.b h)⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hactive
    calc
      _ = (((H.a k * H.b h : ℝ) : ℂ) *
            (((H.a k * H.b h)⁻¹ : ℝ) : ℂ)) *
          (B p.1 q.1 * F.neighboringOperator k h p.2 q.2) := by ring
      _ = _ := by rw [hcancel, one_mul]
  · have hzero : H.a k * H.b h = 0 := not_ne_iff.mp hactive
    rw [hzero]
    simp [H.neighboringOperator_eq_zero_of_mul_eq_zero k h hzero]

/-- If a diagonal input block is \((a_kb_h)B\), then \(\mathcal S_1\)
maps it to \(B\otimes\eta_{k,h}\).

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem NeighboringTraceFactorization.s1Map_block_eq_kronecker
    (H : NeighboringTraceFactorization F)
    (X : Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ)
    (k h : Fin F.sectorCount)
    (B : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ)
    (hblock : X.submatrix (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      ((H.a k * H.b h : ℝ) : ℂ) • B) :
    (H.s1Map X).submatrix
        (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p) =
      B ⊗ₖ F.neighboringOperator k h := by
  ext p q
  rcases p with ⟨a, u⟩
  rcases q with ⟨b, v⟩
  rw [Matrix.submatrix_apply, NeighboringTraceFactorization.s1Map,
    H.completedNeighboringControlledMap_sameBlock_apply]
  change H.completedNeighboringPreparationMap F.neighborIndex_nonempty k h
      (X.submatrix (fun x ↦ Sigma.mk (k, h) x) (fun x ↦ Sigma.mk (k, h) x))
        (a, u) (b, v) = _
  rw [hblock, H.completedNeighboringPreparationMap_smul]

/-- The map \(\mathcal S_2\) sends the regrouped matrix
\(B\otimes\eta_{k,h}\) to the corresponding two-site diagonal sector by
relabeling its indices.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
theorem s2Map_apply (F : PhysicalSectorFactorization K)
    (X : Matrix (S2PreparationIndex F) (S2PreparationIndex F) ℂ)
    (p q : SectorSiteIndex F × SectorSiteIndex F) :
    F.s2Map X p q = X (F.s2ShiftEquiv.symm p) (F.s2ShiftEquiv.symm q) := by
  rfl

end MPOTensor.PhysicalSectorFactorization

end

section

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
          (F.sectorFinEquiv.symm ⟨h, y⟩, F.sectorFinEquiv.symm ⟨q, w⟩) = 0 := by
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
        (F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨p, z⟩) = 0 := by
      ext beta alpha
      exact sectorCoordinateTensor_apply_ne F hkp x z beta alpha
    change 0 = physClose2 F.sectorCoordinateTensor X
      (F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨h, y⟩)
      (F.sectorFinEquiv.symm ⟨p, z⟩, F.sectorFinEquiv.symm ⟨q, w⟩)
    rw [physClose2_apply, hz]
    simp

end MPOTensor.PhysicalSectorFactorization

end
