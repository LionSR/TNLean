/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBlocking
import TNLean.MPS.MPDO.CPSVNormalizedGroupedSectors
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.RFPPositiveFusionDecomposition

/-!
# Vertical decomposition from literal CPSV canonical form

Literal CPSV canonical form and matrix-product-density-operator positivity give
one-site and two-site vertical decompositions retaining the source basis of
normal tensors.

## Main results

* `MPSTensor.IsCPSVCanonicalForm.exists_cpsvVerticalDecomposition`
* `MPSTensor.IsCPSVCanonicalForm.exists_cpsvVerticalDecomposition_blockTwo`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13 and Appendix C.4, lines 1951--1956.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

/-- Literal CPSV canonical form and MPDO positivity furnish a vertical
canonical decomposition retaining the CPSV basis-of-normal-tensors predicate.

The decomposition has positive diagonal weights, mutually orthogonal physical
sector maps, and exact forward and reverse identities.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem exists_cpsvVerticalDecomposition
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : MPOTensor.IsMPDO M) :
    Nonempty (MPOTensor.CPSVVerticalDecomposition M) := by
  classical
  obtain ⟨r, dim, mu, blocks, V, hDimPos, _, hNormal, hIso, _, _, hInterStar,
    _, hReconstruct, hdim, X, zeta, _, _, hXDist, _, _, hSpectralBNT, _, _, _, _,
    hCoeffPos, hGroupedIso, hGroupedOrth, hGroupedInter, _, hGroupedCorner,
    hGroupedReconstruct⟩ :=
      hCanonical.exists_verticalBNTGrouping_with_isometry M hM
  let C := MPSTensor.mpvPhaseClassData blocks
  have hSame : MPSTensor.SameMPV₂Pos (MPOTensor.verticalTensor M)
      (MPSTensor.toTensorFromBlocks (d := D * D) (μ := mu) blocks) :=
    MPSTensor.sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
      (MPOTensor.verticalTensor M) mu blocks V hIso hInterStar hReconstruct
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (MPOTensor.verticalTensor M)
      (fun j ↦ ⟨dim (C.repr j), blocks (C.repr j)⟩) :=
    hSpectralBNT.of_sameMPV₂Pos hSame.symm
  obtain ⟨_, W, _, hWIso, hWOrth, hWInter, hWReconstruct⟩ :=
    hCanonical.exists_normalized_grouped_sector_maps blocks hM mu V hDimPos
      hNormal hdim X zeta hXDist hCoeffPos hGroupedIso hGroupedOrth
      hGroupedInter hGroupedCorner hGroupedReconstruct
  have hWReconstructFlat : ∀ ab, MPOTensor.verticalTensor M ab =
      ∑ q : Fin (∑ j, C.copies j),
        MPOTensor.flattenGroupedSectorMap (fun j ↦ dim (C.repr j)) C.copies W q *
          ((MPOTensor.verticalCopyWeights C.copies
              (fun j q ↦ mu (C.enum j q) * zeta j q) q) •
            MPOTensor.verticalCopyBlocks (fun j ↦ dim (C.repr j)) C.copies
              (fun j ↦ blocks (C.repr j)) q ab) *
          (MPOTensor.flattenGroupedSectorMap
            (fun j ↦ dim (C.repr j)) C.copies W q)ᴴ := by
    intro ab
    rw [hWReconstruct ab]
    let f : ((j : Fin C.g) × Fin (C.copies j)) →
        Matrix (Fin d) (Fin d) ℂ := fun p ↦
      W p * ((mu (C.enum p.1 p.2) * zeta p.1 p.2) •
        blocks (C.repr p.1) ab) * (W p)ᴴ
    change (∑ j, ∑ q, f ⟨j, q⟩) =
      ∑ q, f (finSigmaFinEquiv.symm q)
    exact (Fintype.sum_finSigmaFinEquiv f).symm
  exact MPOTensor.cpsvVerticalDecomposition_of_grouped_orthogonal_sectors M
    (fun j ↦ dim (C.repr j)) C.copies C.copies_pos
    (fun j q ↦ mu (C.enum j q) * zeta j q) hCoeffPos
    (fun j ↦ blocks (C.repr j)) hBNT W hWIso hWOrth hWInter
    hWReconstructFlat

/-- The concrete two-site block of a literal CPSV canonical MPDO has a
vertical canonical decomposition retaining the CPSV basis predicate.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem exists_cpsvVerticalDecomposition_blockTwo
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : MPOTensor.IsMPDO M) :
    Nonempty (MPOTensor.CPSVVerticalDecomposition (MPOTensor.blockTwo M)) := by
  have hBlocked :=
    MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical
  exact hBlocked.exists_cpsvVerticalDecomposition (MPOTensor.blockTwo M) hM.blockTwo

end MPSTensor.IsCPSVCanonicalForm
