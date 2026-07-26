/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Blocking
import TNLean.MPS.MPDO.HorizontalBNT
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Normalized BNT-refined horizontal form under two-site blocking

Two-site physical blocking preserves normalized BNT-refined horizontal form. The sector
representatives and copy weights are blocked, the physical alphabet is
relabeled by the canonical ket--bra equivalence, and every copy retains its
original virtual gauge.

This is the blocking fact used when Proposition 4.13 is applied both to an MPO
tensor and to its two-site blocked tensor in Appendix C.4 of
arXiv:1606.00608, lines 1951--1956.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Two-site physical blocking preserves normalized BNT-refined horizontal
form.

The proof blocks the BNT sector decomposition, transports it through the
canonical ket--bra physical-index equivalence, and uses the same block-diagonal
virtual gauge on every blocked word.

**Scope restriction (BNT-refined horizontal form):** This theorem starts from
`IsHorizontalCF`, not from literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem IsHorizontalCF.blockTwo {M : MPOTensor d D}
    (hHorizontal : IsHorizontalCF M) :
    IsHorizontalCF (MPOTensor.blockTwo M) := by
  classical
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  let e := twoSiteDoubledIndexEquiv d
  let S' := (S.blockTensor 2).reindexPhysical e
  have hCF' : MPSTensor.IsBNTCanonicalForm S' :=
    MPSTensor.SectorDecomposition.IsBNTCanonicalForm.reindexPhysical
      (MPSTensor.SectorDecomposition.IsBNTCanonicalForm.blockTensor hCF (by omega)) e
  refine ⟨S', hCF', ?_⟩
  refine ⟨by rfl, ?_⟩
  simp only [S', MPSTensor.SectorDecomposition.reindexPhysical_totalCopies,
    MPSTensor.SectorDecomposition.blockTensor_totalCopies,
    MPSTensor.SectorDecomposition.reindexPhysical_flatDim,
    MPSTensor.SectorDecomposition.blockTensor_flatDim,
    MPSTensor.SectorDecomposition.reindexPhysical_toTensor,
    MPSTensor.reindexPhysical]
  rw [← MPSTensor.SectorDecomposition.blockTensor_toTensor]
  refine ⟨Xcopy, ?_⟩
  let X := MPSTensor.globalGaugeOfBlocks Xcopy
  have hGauge : ∀ i : Fin (d * d),
      M.toMPSTensor i =
        (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
          (((X)⁻¹ : GL (Fin S.totalDim) ℂ) :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    intro i
    simpa [X] using hX i
  intro i
  rw [toMPSTensor_blockTwo]
  change MPSTensor.blockTensor M.toMPSTensor 2 (e i) =
    (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
      MPSTensor.blockTensor S.toTensor 2 (e i) *
        (((X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)
  exact MPSTensor.evalWord_gauge X hGauge
    (MPSTensor.wordOfBlock (d * d) 2 (e i))

end MPOTensor
