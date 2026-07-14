/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NormalizedGroupedSectors
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalCoisometry

/-!
# Vertical canonical form of a horizontally canonical MPDO

This file completes the vertical canonical-form construction for a matrix
product density operator in horizontal canonical form.  The vertical sectors
are grouped by their matrix-product-vector phase classes, their gauge matrices
are absorbed into normalized physical isometries, and the resulting orthogonal
sector family is assembled into the vertical coisometry.

## Main result

* `MPOTensor.verticalCF_of_horizontalCF`: a horizontally canonical tensor
  generating matrix product density operators is vertically canonical.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A horizontally canonical tensor generating matrix product density
operators is in vertical canonical form.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M := by
  classical
  obtain ⟨r, dim, μ, blocks, V, hdimPos, _hμPos, hNormal, hIso, _hOrth,
    _hInter, hInterStar, _hCorner, hReconstruct, hGrouped⟩ :=
    hHorizontal.exists_verticalBNTGrouping_with_isometry M hM
  obtain ⟨hdim, X, ζ, _hζNorm, _hζNe, hXDist, _hζDist, _hGauge,
    hBasis, _hNotGauge, _hCoeffNe, _hSector, _hCompression, hCoeffPos,
    hIsoGrouped, hOrthGrouped, hInterGrouped, _hInterStarGrouped,
    hCornerGrouped, hReconstructGrouped⟩ := hGrouped
  have hBNT := hHorizontal.isBNT_verticalTensor_of_grouping M μ blocks V
    hdimPos hIso hInterStar hReconstruct hBasis
  obtain ⟨_omega, W, _homega, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    hM.exists_normalized_grouped_sector_maps blocks hHorizontal μ V
      hdimPos hNormal hdim X ζ hXDist hCoeffPos hIsoGrouped hOrthGrouped
      hInterGrouped hCornerGrouped hReconstructGrouped
  let C := MPSTensor.mpvPhaseClassData blocks
  refine isVerticalCF_of_grouped_orthogonal_sectors M
    (fun j ↦ dim (C.repr j)) C.copies C.copies_pos
    (fun j q ↦ μ (C.enum j q) * ζ j q) hCoeffPos
    (fun j ↦ blocks (C.repr j)) hBNT W hWIso hWOrth hWInter ?_
  intro v
  rw [hWReconstruct v]
  let f : ((j : Fin C.g) × Fin (C.copies j)) →
      Matrix (Fin d) (Fin d) ℂ := fun p ↦
    W p * ((μ (C.enum p.1 p.2) * ζ p.1 p.2) •
      blocks (C.repr p.1) v) * (W p)ᴴ
  change (∑ j, ∑ q, f ⟨j, q⟩) =
    ∑ q, f (finSigmaFinEquiv.symm q)
  rw [Equiv.sum_comp finSigmaFinEquiv.symm f, Fintype.sum_sigma]

end MPOTensor
