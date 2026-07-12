/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorSubspinMaps

/-!
# Physical-sector coordinates for two- and three-site closures

This file identifies the physical indices of two and three sites with the
corresponding direct sums of physical sectors. These coordinates are shared
by the refinement and coarse-graining identities of Proposition C.7.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1381--1388 and 1510--1563
-/

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Express two physical sites in the direct sum of physical sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1381--1388 and 1555--1559. -/
noncomputable def twoSiteSectorCoordinateEquiv (F : PhysicalSectorFactorization K) :
    (Fin (Fintype.card (SectorSiteIndex F)) ×
      Fin (Fintype.card (SectorSiteIndex F))) ≃
      SectorSiteIndex F × SectorSiteIndex F :=
  Equiv.prodCongr F.sectorFinEquiv F.sectorFinEquiv

/-- Express three physical sites in the direct sum of physical sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1381--1388 and 1547--1559. -/
noncomputable def threeSiteSectorCoordinateEquiv (F : PhysicalSectorFactorization K) :
    (Fin (Fintype.card (SectorSiteIndex F)) ×
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))) ≃
      SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F) :=
  Equiv.prodCongr F.sectorFinEquiv
    (Equiv.prodCongr F.sectorFinEquiv F.sectorFinEquiv)

@[simp] theorem twoSiteSectorCoordinateEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (x : SectorIndex F k) (y : SectorIndex F h) :
    F.twoSiteSectorCoordinateEquiv.symm (⟨k, x⟩, ⟨h, y⟩) =
      (F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨h, y⟩) :=
  rfl

@[simp] theorem threeSiteSectorCoordinateEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (k l h : Fin F.sectorCount)
    (x : SectorIndex F k) (y : SectorIndex F l) (z : SectorIndex F h) :
    F.threeSiteSectorCoordinateEquiv.symm (⟨k, x⟩, (⟨l, y⟩, ⟨h, z⟩)) =
      (F.sectorFinEquiv.symm ⟨k, x⟩,
        (F.sectorFinEquiv.symm ⟨l, y⟩, F.sectorFinEquiv.symm ⟨h, z⟩)) :=
  rfl

end MPOTensor.PhysicalSectorFactorization
