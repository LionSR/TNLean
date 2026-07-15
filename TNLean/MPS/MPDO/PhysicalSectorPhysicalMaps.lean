/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.LocalizedKrausCPTP
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.PhysicalSectorCoarseGrainingIdentity
import TNLean.MPS.MPDO.PhysicalSectorRefinementIdentity

/-!
# Physical-coordinate refinement and coarse-graining channels

This file transports the sector-coordinate channels of Proposition C.7 to
the ordinary, right-associated physical coordinates of the sector tensor.
It also localizes the transported channels on the first tensor factors while
leaving the last physical site unchanged.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1510--1516 and 1522--1563
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The refinement channel in the ordinary right-associated physical
coordinates of the sector tensor.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545. -/
noncomputable def NeighboringTraceFactorization.physicalTMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F)))) ℂ :=
  Matrix.equivReindexMap F.threeSiteSectorCoordinateEquiv.symm ∘ₗ
    H.tMap ∘ₗ Matrix.equivReindexMap F.twoSiteSectorCoordinateEquiv

/-- The physical-coordinate refinement channel is trace-preserving and
completely positive.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1522--1545. -/
theorem NeighboringTraceFactorization.physicalTMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.physicalTMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP F.twoSiteSectorCoordinateEquiv)
      H.tMap_isKrausCPTP)
    (Matrix.equivReindexMap_isKrausCPTP F.threeSiteSectorCoordinateEquiv.symm)

/-- The physical-coordinate refinement channel sends the two-site closure of
the sector tensor to its three-site closure.

**Local fix (zero-weight quotient):** this identity inherits the completed
zero-weight preparation branch of the sector-coordinate refinement channel.
Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545. -/
theorem NeighboringTraceFactorization.physicalTMap_twoSiteClosure_eq_threeSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.physicalTMap (physClose2 F.sectorCoordinateTensor X) =
      physClose3 F.sectorCoordinateTensor X := by
  change
    Matrix.reindex F.threeSiteSectorCoordinateEquiv.symm
        F.threeSiteSectorCoordinateEquiv.symm
        (H.tMap
          (Matrix.reindex F.twoSiteSectorCoordinateEquiv
            F.twoSiteSectorCoordinateEquiv
            (physClose2 F.sectorCoordinateTensor X))) =
      physClose3 F.sectorCoordinateTensor X
  rw [H.tMap_twoSiteClosure_eq_threeSiteClosure]
  exact (Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteSectorCoordinateEquiv
    F.threeSiteSectorCoordinateEquiv).symm_apply_apply
      (physClose3 F.sectorCoordinateTensor X)

/-- The coarse-graining channel in the ordinary right-associated physical
coordinates of the sector tensor.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1547--1563. -/
noncomputable def NeighboringTraceFactorization.physicalSMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F)))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.equivReindexMap F.twoSiteSectorCoordinateEquiv.symm ∘ₗ
    H.sMap ∘ₗ Matrix.equivReindexMap F.threeSiteSectorCoordinateEquiv

/-- The physical-coordinate coarse-graining channel is trace-preserving and
completely positive.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1547--1563. -/
theorem NeighboringTraceFactorization.physicalSMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.physicalSMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP F.threeSiteSectorCoordinateEquiv)
      H.sMap_isKrausCPTP)
    (Matrix.equivReindexMap_isKrausCPTP F.twoSiteSectorCoordinateEquiv.symm)

/-- The physical-coordinate coarse-graining channel sends the three-site
closure of the sector tensor to its two-site closure.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1547--1563. -/
theorem NeighboringTraceFactorization.physicalSMap_threeSiteClosure_eq_twoSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.physicalSMap (physClose3 F.sectorCoordinateTensor X) =
      physClose2 F.sectorCoordinateTensor X := by
  change
    Matrix.reindex F.twoSiteSectorCoordinateEquiv.symm
        F.twoSiteSectorCoordinateEquiv.symm
        (H.sMap
          (Matrix.reindex F.threeSiteSectorCoordinateEquiv
            F.threeSiteSectorCoordinateEquiv
            (physClose3 F.sectorCoordinateTensor X))) =
      physClose2 F.sectorCoordinateTensor X
  rw [H.sMap_threeSiteClosure_eq_twoSiteClosure]
  exact (Matrix.reindexLinearEquiv ℂ ℂ F.twoSiteSectorCoordinateEquiv
    F.twoSiteSectorCoordinateEquiv).symm_apply_apply
      (physClose2 F.sectorCoordinateTensor X)

/-! ### Localization on the first physical sites -/

/-- Reassociate three right-associated sites so that the first two form the
first tensor factor and the last site is unchanged. -/
def threeSiteFirstTwoEquiv (α : Type*) : α × (α × α) ≃ (α × α) × α where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reassociate four right-associated sites so that the first three form the
first tensor factor and the last site is unchanged. -/
def fourSiteFirstThreeEquiv (α : Type*) :
    α × (α × (α × α)) ≃ (α × (α × α)) × α where
  toFun x := ((x.1, (x.2.1, x.2.2.1)), x.2.2.2)
  invFun x := (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The refinement channel acting on the first two sites of a right-associated
three-site matrix, with the last physical site unchanged.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545; Theorem 4.9, lines 851--856. -/
noncomputable def NeighboringTraceFactorization.localizedPhysicalTMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F)))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F)))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F))))) ℂ :=
  Matrix.equivReindexMap
      (fourSiteFirstThreeEquiv
        (Fin (Fintype.card (SectorSiteIndex F)))).symm ∘ₗ
    Matrix.tensorMapIdLM
      (δ := Fin (Fintype.card (SectorSiteIndex F))) H.physicalTMap ∘ₗ
    Matrix.equivReindexMap
      (threeSiteFirstTwoEquiv (Fin (Fintype.card (SectorSiteIndex F))))

/-- The localized physical-coordinate refinement channel is trace-preserving
and completely positive.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545; Theorem 4.9, lines 851--856. -/
theorem NeighboringTraceFactorization.localizedPhysicalTMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) :
    IsKrausCPTP H.localizedPhysicalTMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP
        (threeSiteFirstTwoEquiv (Fin (Fintype.card (SectorSiteIndex F)))))
      (Matrix.tensorMapIdLM_isKrausCPTP H.physicalTMap_isKrausCPTP))
    (Matrix.equivReindexMap_isKrausCPTP
      (fourSiteFirstThreeEquiv
        (Fin (Fintype.card (SectorSiteIndex F)))).symm)

/-- Applying the refinement channel to the first two sites of a three-site
closure produces the four-site closure, while the last physical site is left
unchanged.

**Local fix (zero-weight quotient):** this action inherits the completed
zero-weight preparation branch of the refinement channel. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1522--1545; Theorem 4.9, lines 851--856. -/
theorem NeighboringTraceFactorization.localizedPhysicalTMap_threeSiteClosure_eq_fourSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.localizedPhysicalTMap (physClose3 F.sectorCoordinateTensor X) =
      physClose4 F.sectorCoordinateTensor X := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩
  change H.physicalTMap
      (Matrix.bipartiteSlice
        (Matrix.reindex (threeSiteFirstTwoEquiv
          (Fin (Fintype.card (SectorSiteIndex F))))
          (threeSiteFirstTwoEquiv
            (Fin (Fintype.card (SectorSiteIndex F))))
          (physClose3 F.sectorCoordinateTensor X)) i₄ j₄)
      (i₁, (i₂, i₃)) (j₁, (j₂, j₃)) =
    physClose4 F.sectorCoordinateTensor X
      (i₁, (i₂, (i₃, i₄))) (j₁, (j₂, (j₃, j₄)))
  rw [show Matrix.bipartiteSlice
      (Matrix.reindex (threeSiteFirstTwoEquiv
        (Fin (Fintype.card (SectorSiteIndex F))))
        (threeSiteFirstTwoEquiv
          (Fin (Fintype.card (SectorSiteIndex F))))
        (physClose3 F.sectorCoordinateTensor X))
      i₄ j₄ =
      physClose2 F.sectorCoordinateTensor
        (F.sectorCoordinateTensor i₄ j₄ * X) by
      ext a b
      simp [Matrix.bipartiteSlice, threeSiteFirstTwoEquiv,
        Matrix.reindex_apply, Matrix.mul_assoc]]
  rw [H.physicalTMap_twoSiteClosure_eq_threeSiteClosure]
  simp [physClose3_apply, physClose4_apply, Matrix.mul_assoc]

/-- The coarse-graining channel acting on the first three sites of a
right-associated four-site matrix, with the last physical site unchanged.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1547--1563; Theorem 4.9, lines 851--856. -/
noncomputable def NeighboringTraceFactorization.localizedPhysicalSMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F)))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F))))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F)))) ℂ :=
  Matrix.equivReindexMap
      (threeSiteFirstTwoEquiv
        (Fin (Fintype.card (SectorSiteIndex F)))).symm ∘ₗ
    Matrix.tensorMapIdLM
      (δ := Fin (Fintype.card (SectorSiteIndex F))) H.physicalSMap ∘ₗ
    Matrix.equivReindexMap
      (fourSiteFirstThreeEquiv (Fin (Fintype.card (SectorSiteIndex F))))

/-- The localized physical-coordinate coarse-graining channel is
trace-preserving and completely positive.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1547--1563; Theorem 4.9, lines 851--856. -/
theorem NeighboringTraceFactorization.localizedPhysicalSMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) :
    IsKrausCPTP H.localizedPhysicalSMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP
        (fourSiteFirstThreeEquiv (Fin (Fintype.card (SectorSiteIndex F)))))
      (Matrix.tensorMapIdLM_isKrausCPTP H.physicalSMap_isKrausCPTP))
    (Matrix.equivReindexMap_isKrausCPTP
      (threeSiteFirstTwoEquiv
        (Fin (Fintype.card (SectorSiteIndex F)))).symm)

/-- Applying the coarse-graining channel to the first three sites of a
four-site closure recovers the three-site closure, while the last physical
site is left unchanged.

Source: arXiv:1606.00608, Proposition C.7, Appendix C.2, lines 1510--1516 and
1547--1563; Theorem 4.9, lines 851--856. -/
theorem NeighboringTraceFactorization.localizedPhysicalSMap_fourSiteClosure_eq_threeSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.localizedPhysicalSMap (physClose4 F.sectorCoordinateTensor X) =
      physClose3 F.sectorCoordinateTensor X := by
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩
  change H.physicalSMap
      (Matrix.bipartiteSlice
        (Matrix.reindex (fourSiteFirstThreeEquiv
          (Fin (Fintype.card (SectorSiteIndex F))))
          (fourSiteFirstThreeEquiv
            (Fin (Fintype.card (SectorSiteIndex F))))
          (physClose4 F.sectorCoordinateTensor X)) i₃ j₃)
      (i₁, i₂) (j₁, j₂) =
    physClose3 F.sectorCoordinateTensor X
      (i₁, (i₂, i₃)) (j₁, (j₂, j₃))
  rw [show Matrix.bipartiteSlice
      (Matrix.reindex (fourSiteFirstThreeEquiv
        (Fin (Fintype.card (SectorSiteIndex F))))
        (fourSiteFirstThreeEquiv
          (Fin (Fintype.card (SectorSiteIndex F))))
        (physClose4 F.sectorCoordinateTensor X))
      i₃ j₃ =
      physClose3 F.sectorCoordinateTensor
        (F.sectorCoordinateTensor i₃ j₃ * X) by
      ext a b
      simp [Matrix.bipartiteSlice, fourSiteFirstThreeEquiv,
        Matrix.reindex_apply, physClose4_apply, Matrix.mul_assoc]]
  rw [H.physicalSMap_threeSiteClosure_eq_twoSiteClosure]
  simp [physClose2_apply, physClose3_apply, Matrix.mul_assoc]

end MPOTensor.PhysicalSectorFactorization
