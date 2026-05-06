/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.ZeroTailTransport
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Conditional sector comparison after blocking

This module contains the final sector-comparison consequence used after
structural common-period blocking.  It keeps only the overlap-span-to-sector
matching step; the older common-block wrappers are superseded by the
zero-tail/block-span and BNT-cover routes in the surrounding assembly modules.
-/

namespace MPSTensor

section FundamentalTheoremAfterBlocking

/-- **After-blocking sector comparison from primitive overlap-span hypotheses.**

Assume that a common positive blocking period gives sector decompositions for
the two blocked tensors, that both sector decompositions carry BNT data, and
that their bases satisfy the primitive overlap-span hypotheses. These
hypotheses construct the sector-basis matching, and the two-basis sector
comparison theorem then gives the matched sector-weight conclusion.

Thus the matched sector-weight conclusion is derived from primitive overlap-span
data, rather than from an assumed `SectorBasisMatching` or an assumed
permutation with copy-count equalities. -/
theorem fundamentalTheorem_after_blocking_sector_of_bntPair_overlapSpan
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (bntSectorPair :
      ∃ p : ℕ, 0 < p ∧
      ∃ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
        SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
        HasBNTSectorData P ∧ HasBNTSectorData Q ∧
        SectorBasisOverlapSpanHypotheses P Q) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt, hOverlapSpan⟩ := bntSectorPair
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

end FundamentalTheoremAfterBlocking

end MPSTensor
