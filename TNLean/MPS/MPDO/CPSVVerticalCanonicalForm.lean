/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVNormalizedGroupedSectors
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalCoisometry

/-!
# Vertical canonical form from literal CPSV canonical form

The literal CPSV canonical-form decomposition groups the normal vertical
corners by matrix-product-vector phase class.  The grouped Figure 8 identity
normalizes their internal gauges, after which the orthogonal physical sector
maps assemble into the coisometry of the vertical canonical form.

## Main result

* `MPOTensor.verticalCF_of_cpsvCanonicalForm`: every matrix product density
  operator in literal CPSV canonical form is in vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in literal CPSV canonical form is also
in vertical canonical form.

The literal grouped decomposition supplies a basis of normal representatives
and positive grouped coefficients.  Gram normalization gives orthogonal
isometric physical sector maps.  Their block row is the required coisometry,
with orientation $U U^\dagger=I$, and the two direct-sum identities follow from
the exact letterwise reconstruction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_cpsvCanonicalForm (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    IsVerticalCF M := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ :=
      hCanonical.exists_verticalBNTGrouping_with_isometry M hM
  let C := MPSTensor.mpvPhaseClassData blocks
  have hBNT : MPSTensor.IsBNT (verticalTensor M) C.g
      (fun j ↦ dim (C.repr j)) (fun j ↦ blocks (C.repr j)) :=
    isBNT_verticalTensor_of_grouping M mu blocks V hIso
      hInterStar hReconstruct hSpectralBNT
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    hCanonical.exists_normalized_grouped_sector_maps blocks hM mu V hDimPos
      hNormal hdim X zeta hXDist hCoeffPos hGroupedIso hGroupedOrth
      hGroupedInter hGroupedCorner hGroupedReconstruct
  apply isVerticalCF_of_grouped_orthogonal_sectors M
    (fun j ↦ dim (C.repr j)) C.copies C.copies_pos
    (fun j q ↦ mu (C.enum j q) * zeta j q) hCoeffPos
    (fun j ↦ blocks (C.repr j)) hBNT W hWIso hWOrth hWInter
  intro v
  rw [hWReconstruct v]
  let f : ((j : Fin C.g) × Fin (C.copies j)) → Matrix (Fin d) (Fin d) ℂ :=
    fun p ↦ W p *
      ((mu (C.enum p.1 p.2) * zeta p.1 p.2) • blocks (C.repr p.1) v) *
      (W p)ᴴ
  change (∑ j, ∑ q, f ⟨j, q⟩) = ∑ q, f (finSigmaFinEquiv.symm q)
  exact (Fintype.sum_finSigmaFinEquiv f).symm

end MPOTensor
