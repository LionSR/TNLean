/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NormalizedGroupedSectors
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalCoisometry

/-!
# Vertical canonical form of matrix product density operators

The grouped vertical decomposition of a matrix product density operator in
normalized BNT-refined horizontal form supplies a basis of normal tensors and
normalized physical sector maps. The resulting positive weights and sector
maps give the coisometry and the two exact block-diagonal identities of the
vertical canonical form.

## Main result

* `MPOTensor.verticalCF_of_horizontalCF`: every matrix product density operator
  in normalized BNT-refined horizontal form is in vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in normalized BNT-refined horizontal form
is also in vertical canonical form.

The same grouped vertical decomposition supplies both the algebraic basis of
normal tensors and the normalized physical sector maps.  Their positive
weights, orthogonal isometric ranges, intertwinings, and exact reconstruction
then combine to give the vertical coisometry.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form assumed by Proposition 4.13.
The source-faithful literal implication is proved independently by
`verticalCF_of_cpsvCanonicalForm`; this theorem retains the stronger horizontal
interface for its existing consumers.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ :=
      hHorizontal.exists_verticalBNTGrouping_with_isometry M hM
  let C := MPSTensor.mpvPhaseClassData blocks
  have hBNT : MPSTensor.IsBNT (verticalTensor M) C.g
      (fun j ↦ dim (C.repr j)) (fun j ↦ blocks (C.repr j)) :=
    isBNT_verticalTensor_of_grouping M mu blocks V hIso
      hInterStar hReconstruct hSpectralBNT
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    hM.exists_normalized_grouped_sector_maps blocks hHorizontal mu V hDimPos
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
  calc
    _ = ∑ p, f p := (Fintype.sum_sigma f).symm
    _ = _ := (Equiv.sum_comp finSigmaFinEquiv.symm f).symm

end MPOTensor
