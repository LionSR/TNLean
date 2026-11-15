/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTRefinement
import TNLean.MPS.CanonicalForm.CPSVAfterBlocking
import TNLean.MPS.CanonicalForm.CPSVCanonicalFormII

/-!
# Inequivalent normal sectors of an arbitrary blocked tensor

Every tensor admits, after a fixed positive blocking, an exact positive-length
representation by normal left-canonical sectors. Repeated gauge-phase-equivalent
blocks are grouped, retaining their nonzero complex copy weights and multiplicities.
The representatives are eventually linearly independent and pairwise inequivalent.

The sector family may be empty, in which case all positive-length vectors of the
blocked tensor vanish. No normalization or nonvanishing assumption on the input
tensor is needed, and no assertion is made about lengths outside the blocking period.

## Main statements

* `exists_normal_leftCanonical_sectors_after_blocking`: arbitrary-input sector
  decomposition, with exact positive-length coefficients.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Proposition 2.4,
  Proposition 2.7, eqs. (20)--(22), and Appendix A, canonical form II.
* Malz--Styliaris--Wei--Cirac, arXiv:2307.01696, Supplemental Material, eq. (S2).
-/

namespace MPSTensor

/-- Every tensor has inequivalent normal left-canonical sectors after a fixed positive
blocking. The coefficients at every positive blocked length are exactly the sector
power sums, including all multiplicities and phases. The family may be empty.

Source: arXiv:1606.00608, Proposition 2.4, Proposition 2.7, eqs. (20)--(22), and
Appendix A, eqs. `TP` and `Lambda`. This is the algebraic canonicalization used before
arXiv:2307.01696, Supplemental Material, eq. (S2); it is not a preparation theorem
on the original physical sites. -/
theorem exists_normal_leftCanonical_sectors_after_blocking
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ P : SectorDecomposition (blockPhysDim d p),
      SameMPV₂Pos (blockTensor A p) P.toTensor ∧
      (∀ j, IsNormalTensor (P.basis j)) ∧
      (∀ j, IsLeftCanonical (P.basis j)) ∧
      HasBNTSectorData P ∧ BlocksNotGaugePhaseEquiv P.basis := by
  obtain ⟨p, hp, D', B, hB, hAB⟩ :=
    exists_cpsvCanonicalForm_representative_after_blocking A
  obtain ⟨C, dataC, hBC, _⟩ := hB.data.exists_gaugeEquiv_canonicalFormIIData
  let data := dataC.toCPSVCanonicalFormData
  let ref := data.bntRefinement
  refine ⟨p, hp, ref.representativeSectorDecomposition, ?_,
    ref.representativeNormal, ?_, ref.representativesBNT.eventually_li,
    ref.representativesNotEquiv⟩
  · exact (hAB.trans hBC.sameMPV.toSameMPV₂Pos).trans
      (ref.source_sameMPV₂Pos_groupedTensor.trans
        ref.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition)
  · intro j
    exact dataC.blocks_left_canonical (data.representativeIndex j)

end MPSTensor
