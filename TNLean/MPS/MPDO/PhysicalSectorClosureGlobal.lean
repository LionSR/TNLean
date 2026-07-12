/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorClosureTwo
import TNLean.MPS.MPDO.PhysicalSectorClosureThree

/-!
# Global physical-sector closure decompositions

This file combines the fixed-sector closure identities of Appendix C.2 of
arXiv:1606.00608 into direct-sum decompositions of the complete two- and
three-site physical closures.  The physical indices are first written as
sector tuples, and the factors within each tuple are then regrouped into the
outer boundary factor and the neighboring factors.

The diagonal blocks are the fixed-sector Kronecker products.  Every block
between distinct sector tuples vanishes.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `etarl`, lines 1381--1450, and
  Proposition C.7, lines 1510--1563
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private def sigmaPairEquiv {I J : Type*} {A : I → Type*} {B : J → Type*} :
    (Sigma A × Sigma B) ≃ Σ ij : I × J, A ij.1 × B ij.2 where
  toFun x := ⟨(x.1.1, x.2.1), (x.1.2, x.2.2)⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv := by rintro ⟨⟨i, x⟩, j, y⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, x, y⟩; rfl

private def sigmaTripleEquiv {I J L : Type*} {A : I → Type*} {B : J → Type*}
    {C : L → Type*} :
    (Sigma A × (Sigma B × Sigma C)) ≃
      Σ ijl : I × (J × L), A ijl.1 × (B ijl.2.1 × C ijl.2.2) where
  toFun x := ⟨(x.1.1, (x.2.1.1, x.2.2.1)), (x.1.2, (x.2.1.2, x.2.2.2))⟩
  invFun x := (⟨x.1.1, x.2.1⟩, (⟨x.1.2.1, x.2.2.1⟩, ⟨x.1.2.2, x.2.2.2⟩))
  left_inv := by rintro ⟨⟨i, x⟩, ⟨j, y⟩, l, z⟩; rfl
  right_inv := by rintro ⟨⟨i, j, l⟩, x, y, z⟩; rfl

/-- The complete two-site physical space, indexed by a sector pair and
regrouped into its outer and neighboring factors.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450. -/
noncomputable def twoSiteGlobalRegroupEquiv (F : PhysicalSectorFactorization K) :
    (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)) ×
      Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k))) ≃
      Σ kh : Fin F.sectorCount × Fin F.sectorCount,
        BoundaryIndex F kh.1 kh.2 × NeighborIndex F kh.1 kh.2 :=
  ((Equiv.prodCongr F.sectorFinEquiv F.sectorFinEquiv).trans sigmaPairEquiv).trans
    (Equiv.sigmaCongrRight fun kh ↦ F.twoSiteRegroupEquiv kh.1 kh.2)

@[simp] theorem twoSiteGlobalRegroupEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (x : BoundaryIndex F k h × NeighborIndex F k h) :
    F.twoSiteGlobalRegroupEquiv.symm ⟨(k, h), x⟩ =
      F.twoSiteSectorEmbedding k h ((F.twoSiteRegroupEquiv k h).symm x) :=
  rfl

/-- The complete three-site physical space, indexed by a sector triple and
regrouped into its outer and two neighboring factors.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450; the order of factors is that of Proposition C.7,
lines 1510--1522. -/
noncomputable def threeSiteGlobalRegroupEquiv (F : PhysicalSectorFactorization K) :
    (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)) ×
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)) ×
        Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)))) ≃
      Σ klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount),
        BoundaryIndex F klh.1 klh.2.2 ×
          (NeighborIndex F klh.1 klh.2.1 × NeighborIndex F klh.2.1 klh.2.2) :=
  ((Equiv.prodCongr F.sectorFinEquiv
      (Equiv.prodCongr F.sectorFinEquiv F.sectorFinEquiv)).trans sigmaTripleEquiv).trans
    (Equiv.sigmaCongrRight fun klh ↦
      F.threeSiteRegroupEquiv klh.1 klh.2.1 klh.2.2)

@[simp] theorem threeSiteGlobalRegroupEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩ =
      F.threeSiteSectorEmbedding k l h ((F.threeSiteRegroupEquiv k l h).symm x) :=
  rfl

/-- After global regrouping, the complete two-site closure is the direct sum
over sector pairs of the outer boundary operator tensored with the neighboring
operator.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450, and the two-site operator in Proposition C.7,
lines 1510--1516. -/
theorem twoSiteGlobalClosure_eq (F : PhysicalSectorFactorization K)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
        (physClose2 F.sectorCoordinateTensor X) =
      Matrix.blockDiagonal' fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
        F.boundaryOperator kh.1 kh.2 X ⊗ₖ F.neighboringOperator kh.1 kh.2 := by
  ext ⟨kh, x⟩ ⟨pq, y⟩
  by_cases hp : kh = pq
  · subst pq
    rw [Matrix.blockDiagonal'_apply_eq]
    change physClose2 F.sectorCoordinateTensor X
      (F.twoSiteGlobalRegroupEquiv.symm ⟨kh, x⟩)
      (F.twoSiteGlobalRegroupEquiv.symm ⟨kh, y⟩) = _
    rw [twoSiteGlobalRegroupEquiv_symm_apply,
      twoSiteGlobalRegroupEquiv_symm_apply]
    have h := congrFun (congrFun (F.twoSiteSectorClosure_eq kh.1 kh.2 X) x) y
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      twoSiteSectorClosure] using h
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp]
    have hne : kh.1 ≠ pq.1 ∨ kh.2 ≠ pq.2 := by
      exact not_and_or.mp (fun h ↦ hp (Prod.ext h.1 h.2))
    change physClose2 F.sectorCoordinateTensor X
      (F.twoSiteGlobalRegroupEquiv.symm ⟨kh, x⟩)
      (F.twoSiteGlobalRegroupEquiv.symm ⟨pq, y⟩) = 0
    rw [twoSiteGlobalRegroupEquiv_symm_apply,
      twoSiteGlobalRegroupEquiv_symm_apply]
    simp only [twoSiteSectorEmbedding, physClose2_apply]
    rcases hne with hne | hne
    · have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm
            ⟨kh.1, ((F.twoSiteRegroupEquiv kh.1 kh.2).symm x).1⟩)
          (F.sectorFinEquiv.symm
            ⟨pq.1, ((F.twoSiteRegroupEquiv pq.1 pq.2).symm y).1⟩) = 0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hne _ _ beta alpha
      rw [hz]
      simp
    · have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm
            ⟨kh.2, ((F.twoSiteRegroupEquiv kh.1 kh.2).symm x).2⟩)
          (F.sectorFinEquiv.symm
            ⟨pq.2, ((F.twoSiteRegroupEquiv pq.1 pq.2).symm y).2⟩) = 0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hne _ _ beta alpha
      rw [hz]
      simp

/-- After global regrouping, the complete three-site closure is the direct
sum over sector triples of the outer boundary operator tensored with the two
neighboring operators.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450, and the three-site operator in Proposition C.7,
lines 1510--1516. -/
theorem threeSiteGlobalClosure_eq (F : PhysicalSectorFactorization K)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (physClose3 F.sectorCoordinateTensor X) =
      Matrix.blockDiagonal' fun
          klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount) ↦
        F.boundaryOperator klh.1 klh.2.2 X ⊗ₖ
          (F.neighboringOperator klh.1 klh.2.1 ⊗ₖ
            F.neighboringOperator klh.2.1 klh.2.2) := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  by_cases hp : klh = pqr
  · subst pqr
    rw [Matrix.blockDiagonal'_apply_eq]
    change physClose3 F.sectorCoordinateTensor X
      (F.threeSiteGlobalRegroupEquiv.symm ⟨klh, x⟩)
      (F.threeSiteGlobalRegroupEquiv.symm ⟨klh, y⟩) = _
    rw [threeSiteGlobalRegroupEquiv_symm_apply,
      threeSiteGlobalRegroupEquiv_symm_apply]
    have h := congrFun
      (congrFun (F.threeSiteSectorClosure_eq klh.1 klh.2.1 klh.2.2 X) x) y
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      threeSiteSectorClosure] using h
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp]
    have hne : klh.1 ≠ pqr.1 ∨ klh.2.1 ≠ pqr.2.1 ∨ klh.2.2 ≠ pqr.2.2 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hp (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    change physClose3 F.sectorCoordinateTensor X
      (F.threeSiteGlobalRegroupEquiv.symm ⟨klh, x⟩)
      (F.threeSiteGlobalRegroupEquiv.symm ⟨pqr, y⟩) = 0
    rw [threeSiteGlobalRegroupEquiv_symm_apply,
      threeSiteGlobalRegroupEquiv_symm_apply]
    simp only [threeSiteSectorEmbedding, physClose3_apply]
    rcases hne with hne | hne | hne
    · have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm
            ⟨klh.1, ((F.threeSiteRegroupEquiv klh.1 klh.2.1 klh.2.2).symm x).1⟩)
          (F.sectorFinEquiv.symm
            ⟨pqr.1, ((F.threeSiteRegroupEquiv pqr.1 pqr.2.1 pqr.2.2).symm y).1⟩) = 0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hne _ _ beta alpha
      rw [hz]
      simp
    · have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm
            ⟨klh.2.1, ((F.threeSiteRegroupEquiv klh.1 klh.2.1 klh.2.2).symm x).2.1⟩)
          (F.sectorFinEquiv.symm
            ⟨pqr.2.1, ((F.threeSiteRegroupEquiv pqr.1 pqr.2.1 pqr.2.2).symm y).2.1⟩) =
            0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hne _ _ beta alpha
      rw [hz]
      simp
    · have hz : F.sectorCoordinateTensor
          (F.sectorFinEquiv.symm
            ⟨klh.2.2, ((F.threeSiteRegroupEquiv klh.1 klh.2.1 klh.2.2).symm x).2.2⟩)
          (F.sectorFinEquiv.symm
            ⟨pqr.2.2, ((F.threeSiteRegroupEquiv pqr.1 pqr.2.1 pqr.2.2).symm y).2.2⟩) =
            0 := by
        ext beta alpha
        exact sectorCoordinateTensor_apply_ne F hne _ _ beta alpha
      rw [hz]
      simp

end MPOTensor.PhysicalSectorFactorization
