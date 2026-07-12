/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorClosureCoordinates
import TNLean.MPS.MPDO.PhysicalSectorClosureTwo
import TNLean.MPS.MPDO.PhysicalSectorRefinement

/-!
# Action of the physical-sector refinement maps

This file computes the sector-block action of the three maps in the
refinement channel of Proposition C.7. The two-site closure first regroups as
a boundary operator tensored with a neighboring operator. The first map
traces the neighboring factor, the second adjoins the completed normalized
three-site neighboring operator, and the third reindexes the resulting
subspins as three physical sites.

Only the action of the three constituent maps is proved here. The equality
between the refined two-site closure and the three-site closure is a separate
statement.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1522--1545
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- On an outer-sector pair, the regrouped two-site physical closure is the
boundary operator tensored with the neighboring operator.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450 and 1521--1524. -/
theorem t0Regrouped_twoSiteClosure_block_eq
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ)
    (k h : Fin F.sectorCount) :
    (Matrix.equivReindexMap F.t0RegroupEquiv
      (Matrix.reindex F.twoSiteSectorCoordinateEquiv
        F.twoSiteSectorCoordinateEquiv
        (physClose2 F.sectorCoordinateTensor X))).submatrix
          (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      F.boundaryOperator k h X ⊗ₖ F.neighboringOperator k h := by
  ext ⟨a, u⟩ ⟨b, v⟩
  have hg := congrFun (congrFun (F.twoSiteSectorClosure_eq k h X)
    (a, u)) (b, v)
  simpa [Matrix.equivReindexMap, Matrix.reindex_apply, Matrix.submatrix_apply,
    t0RegroupEquiv, twoSiteSectorCoordinateEquiv, twoSiteSectorClosure,
    twoSiteSectorEmbedding, twoSiteRegroupEquiv, s2ShiftEquiv] using hg

/-- On a diagonal outer-sector pair, \(\mathcal T_0\) is the partial trace
of the corresponding regrouped two-site block.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1524. -/
theorem t0Map_sameBlock_apply (F : PhysicalSectorFactorization K)
    (X : Matrix (SectorSiteIndex F × SectorSiteIndex F)
      (SectorSiteIndex F × SectorSiteIndex F) ℂ)
    (k h : Fin F.sectorCount) (a b : BoundaryIndex F k h) :
    F.t0Map X ⟨(k, h), a⟩ ⟨(k, h), b⟩ =
      Matrix.partialTraceRight
        ((Matrix.equivReindexMap F.t0RegroupEquiv X).submatrix
          (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p)) a b := by
  rw [t0Map, LinearMap.comp_apply,
    Matrix.controlledPartialTraceRightLM_sameBlock_apply]

/-- If a regrouped diagonal block is
\(B\otimes\eta_{k,h}\), then \(\mathcal T_0\) maps it to
\((a_kb_h)B\).

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1535. -/
theorem NeighboringTraceFactorization.t0Map_block_eq_smul
    (H : NeighboringTraceFactorization F)
    (X : Matrix (SectorSiteIndex F × SectorSiteIndex F)
      (SectorSiteIndex F × SectorSiteIndex F) ℂ)
    (k h : Fin F.sectorCount) (B : Matrix (BoundaryIndex F k h)
      (BoundaryIndex F k h) ℂ)
    (hblock :
      (Matrix.equivReindexMap F.t0RegroupEquiv X).submatrix
        (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p) =
          B ⊗ₖ F.neighboringOperator k h) :
    (F.t0Map X).submatrix (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      ((H.a k * H.b h : ℝ) : ℂ) • B := by
  ext a b
  rw [Matrix.submatrix_apply, F.t0Map_sameBlock_apply, hblock,
    Matrix.partialTraceRight_kronecker,
    H.trace_neighboringOperator, Matrix.smul_apply]

/-- Multiplying a boundary matrix by \(a_kb_h\) and then adjoining the
completed normalized three-site neighboring density gives exactly
\(B\otimes\Omega_{k,h}\), including on zero-weight sector pairs.

**Local fix (zero-weight quotient):** the inactive branch is harmless because
both the input coefficient and \(\Omega_{k,h}\) vanish. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.completedThreeSitePreparationMap_smul
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (B : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) :
    H.completedThreeSitePreparationMap k h
        (((H.a k * H.b h : ℝ) : ℂ) • B) =
      B ⊗ₖ F.threeSiteNeighboringOperator k h := by
  classical
  by_cases hactive : H.a k * H.b h ≠ 0
  · rw [H.completedThreeSitePreparationMap_eq_normalized k h hactive]
    ext p q
    change Matrix.kroneckerMap (· * ·)
        (((H.a k * H.b h : ℝ) : ℂ) • B)
        ((((H.a k * H.b h)⁻¹ : ℝ) : ℂ) •
          F.threeSiteNeighboringOperator k h) p q = _
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    have hcancel :
        ((H.a k * H.b h : ℝ) : ℂ) *
          (((H.a k * H.b h)⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hactive
    calc
      _ = (((H.a k * H.b h : ℝ) : ℂ) *
            (((H.a k * H.b h)⁻¹ : ℝ) : ℂ)) *
          (B p.1 q.1 * F.threeSiteNeighboringOperator k h p.2 q.2) := by ring
      _ = _ := by rw [hcancel, one_mul]
  · have hzero : H.a k * H.b h = 0 := not_ne_iff.mp hactive
    rw [hzero]
    simp [H.threeSiteNeighboringOperator_eq_zero_of_mul_eq_zero k h hzero]

/-- If a diagonal input block is \((a_kb_h)B\), then \(\mathcal T_1\)
maps it to \(B\otimes\Omega_{k,h}\).

**Local fix (zero-weight quotient):** on an inactive pair the input block and
the target neighboring operator both vanish, independently of the chosen
density. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.t1Map_block_eq_kronecker
    (H : NeighboringTraceFactorization F)
    (X : Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ)
    (k h : Fin F.sectorCount)
    (B : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ)
    (hblock : X.submatrix (Sigma.mk (k, h)) (Sigma.mk (k, h)) =
      ((H.a k * H.b h : ℝ) : ℂ) • B) :
    (H.t1Map X).submatrix
        (fun p ↦ Sigma.mk (k, h) p) (fun p ↦ Sigma.mk (k, h) p) =
      B ⊗ₖ F.threeSiteNeighboringOperator k h := by
  ext p q
  rcases p with ⟨a, u⟩
  rcases q with ⟨b, v⟩
  rw [Matrix.submatrix_apply, NeighboringTraceFactorization.t1Map,
    H.completedThreeSiteControlledMap_sameBlock_apply]
  change H.completedThreeSitePreparationMap k h
      (X.submatrix (fun x ↦ Sigma.mk (k, h) x)
        (fun x ↦ Sigma.mk (k, h) x)) (a, u) (b, v) = _
  rw [hblock, H.completedThreeSitePreparationMap_smul]

/-- The preparation stage annihilates entries between distinct pairs of
outer sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.t1Map_apply_of_ne
    (H : NeighboringTraceFactorization F)
    (Y : Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ)
    {kh pq : Fin F.sectorCount × Fin F.sectorCount} (hne : kh ≠ pq)
    (a : BoundaryIndex F kh.1 kh.2)
    (u : ThreeSiteMiddleIndex F kh.1 kh.2)
    (b : BoundaryIndex F pq.1 pq.2)
    (v : ThreeSiteMiddleIndex F pq.1 pq.2) :
    H.t1Map Y ⟨kh, (a, u)⟩ ⟨pq, (b, v)⟩ = 0 := by
  classical
  rw [NeighboringTraceFactorization.t1Map,
    NeighboringTraceFactorization.completedThreeSiteControlledMap,
    Matrix.controlledKrausMap_apply_of_ne _ _ Y hne]

/-- The map \(\mathcal T_2\) sends the prepared matrix to the corresponding
three-site sector matrix by relabeling its indices.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1545. -/
theorem t2Map_apply (F : PhysicalSectorFactorization K)
    (X : Matrix (S0PreparationIndex F) (S0PreparationIndex F) ℂ)
    (p q : SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) :
    F.t2Map X p q = X (F.t2ShiftEquiv.symm p) (F.t2ShiftEquiv.symm q) := by
  rfl

end MPOTensor.PhysicalSectorFactorization
