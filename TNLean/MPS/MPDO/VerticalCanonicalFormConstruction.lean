/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GroupedSectorGram
import TNLean.MPS.MPDO.NormalizedGroupedSectorMaps
import TNLean.MPS.MPDO.VerticalBNT
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalCoisometry

/-!
# Predicate-neutral vertical canonical form

A grouped vertical BNT decomposition and pairwise grouped-corner Gram dressing
supply all data needed for vertical canonical form. The grouped representatives
form a BNT, Gram rigidity normalizes the physical sector maps, and their block
row gives the required coisometry and exact reconstruction.

## Main results

* `MPOTensor.verticalCF_of_grouping_and_gramDressing`: grouped vertical BNT
  data and the pairwise Figure 8 hypothesis imply vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Grouped vertical BNT data with pairwise Figure 8 comparison determine a
vertical canonical form.

The grouping contains the normal representatives, positive grouped weights,
orthogonal physical corners, and exact reconstruction. The Gram-dressing
hypothesis is the only canonical-form-specific input.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_grouping_and_gramDressing (M : MPOTensor d D)
    (hGrouping : HasVerticalBNTGroupingWithIsometry M)
    (hDressing : HasGroupedCornerGramDressing M) :
    IsVerticalCF M := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ := hGrouping
  let C := MPSTensor.mpvPhaseClassData blocks
  have hBNT : MPSTensor.IsBNT (verticalTensor M) C.g
      (fun j ↦ dim (C.repr j)) (fun j ↦ blocks (C.repr j)) :=
    isBNT_verticalTensor_of_grouping M mu blocks V hIso
      hInterStar hReconstruct hSpectralBNT
  have hGram : ∀ j q, ∃ omega : ℝ, 0 < omega ∧
      (X j q : Matrix (Fin (dim (C.enum j q))) (Fin (dim (C.enum j q))) ℂ)ᴴ *
          X j q = (omega : ℂ) • 1 := by
    intro j q
    apply grouped_sector_gram_eq_pos_smul_one_of_dressing blocks
      (M := M) (μ := mu) (V := V) (_hDimPos := hDimPos) (hdim := hdim)
        (X := X) (ζ := zeta) (hXDist := hXDist) (hCoeffPos := hCoeffPos)
        (hCorner := hGroupedCorner) (j := j) (q := q)
    · exact hDressing
    · intro l p
      exact ((MPSTensor.isNormalTensor_cast_iff (hdim l p)
        (blocks (C.repr l))).2 (hNormal (C.repr l))).isNormal
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    exists_normalized_grouped_sector_maps_of_gram blocks mu V hdim X zeta
      hGram hGroupedIso hGroupedOrth hGroupedInter hGroupedReconstruct
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
