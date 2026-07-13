/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.MPDO.RepresentativeGroupedLemmaL

/-!
# Representative separation after injective blocking

For a BNT canonical-form sector decomposition whose representative tensors are
already injective, the representative word tuples span the full product matrix
algebra at every sufficiently large length.  Pairwise separation gives a fixed
selector suffix, while one-site injectivity gives a full matrix-algebra prefix
at every positive remaining length.

This is the post-blocking form of the block-injectivity input in
arXiv:1606.00608, lines 318--345.  In particular, line 332 supplies the
injectivity hypothesis after blocking.  No right-unital normalization or
period-window hypothesis is used.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- The minimal BNT representatives have full simultaneous word-tuple span at
every sufficiently large length once they have already been made injective by
blocking.

The fixed selector suffix is obtained from the direct-sum separation argument
at the lengths (1), (2), and (6).  For a total length beyond the selector
suffix, injectivity supplies the remaining positive-length prefix.

**Scope restriction (already injectively blocked representatives):** the
hypothesis `∀ j, IsInjective (P.basis j)` is the conclusion of the blocking
step in arXiv:1606.00608, line 332.  This theorem does not transport an
unblocked first-site action through that blocking.  See
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`. -/
theorem eventuallyRepresentativeWordTupleSpan_of_basis_injective
    (hCF : IsBNTCanonicalForm P)
    (hInj : ∀ j, IsInjective (P.basis j)) :
    P.EventuallyRepresentativeWordTupleSpan := by
  classical
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  have hBlkPos : ∀ (j : Fin P.basisCount) (n : ℕ), 0 < n →
      IsNBlkInjective (P.basis j) n := by
    intro j n hn
    exact (wordSpan_eq_top_iff_isNBlkInjective (P.basis j) n).mp
      (wordSpan_eq_top_of_isInjective (hInj j) hn)
  have hIrr : HasIrreducibleBlocks (d := d) P.basis :=
    HasIrreducibleBlocks.ofForall hCF.basis_irreducible
  have hLeft : IsLeftCanonicalBlockFamily (d := d) P.basis :=
    IsLeftCanonicalBlockFamily.ofForall hCF.basis_left_canonical
  have hOverlap : HasNormalizedSelfOverlap (d := d) P.basis :=
    HasNormalizedSelfOverlap.ofForall hCF.basis_normalized_self_overlap
  have hBlocks : BlocksNotGaugePhaseEquiv (d := d) P.basis :=
    hCF.basis_distinct
  have hPair : HasPairBlockSeparatingWords P.basis 6 := by
    simpa using
      (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
        P.basis hIrr hLeft hOverlap hBlocks
        (fun j ↦ hBlkPos j 1 (by omega))
        (fun j ↦ hBlkPos j 2 (by omega))
        (fun j ↦ hBlkPos j 6 (by omega))
        (by omega : 0 < 1))
  let selectorLength := (P.basisCount - 1) * 6
  have hSelectors : HasBlockSelectorWords P.basis selectorLength := by
    simpa [selectorLength] using
      hasBlockSelectorWords_of_pairBlockSeparatingWords P.basis hPair
  change ∃ L₀ : ℕ, ∀ L ≥ L₀, WordTupleSpanTop P.basis L
  refine ⟨selectorLength + 1, ?_⟩
  intro L hL
  have hSelectorLength_le : selectorLength ≤ L := by omega
  have hPrefixPos : 0 < L - selectorLength := by omega
  have hSpan := wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    P.basis (fun j ↦ hBlkPos j (L - selectorLength) hPrefixPos) hSelectors
  simpa [Nat.sub_add_cancel hSelectorLength_le] using hSpan

/-- Representative-grouped Lemma L for an already injectively blocked BNT
canonical form.

This removes the explicit word-tuple-span hypothesis from the grouped theorem,
but retains the post-blocking injectivity conclusion of arXiv:1606.00608,
line 332.  The grouping and power-sum argument is Appendix C.3, lines
1835--1858. -/
theorem insertedTensor_basis_eq_of_firstSiteActionAgree_of_basis_injective
    (hCF : IsBNTCanonicalForm P)
    (hInj : ∀ j, IsInjective (P.basis j))
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree P.toTensor Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact P.insertedTensor_basis_eq_of_firstSiteActionAgree
    (hCF.eventuallyRepresentativeWordTupleSpan_of_basis_injective hInj) hAct

/-- Same-MPV transport of representative-grouped Lemma L for an already
injectively blocked BNT canonical form.

The original tensor and the sector-decomposition tensor have the same complete
MPV family; the finite representative separation is supplied by the
post-blocking canonical-form hypotheses above. -/
theorem insertedTensor_basis_eq_of_sameMPV₂_firstSiteActionAgree_of_basis_injective
    {D : ℕ} (A : MPSTensor d D)
    (hCF : IsBNTCanonicalForm P)
    (hInj : ∀ j, IsInjective (P.basis j))
    (hAP : SameMPV₂ A P.toTensor)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact hCF.insertedTensor_basis_eq_of_firstSiteActionAgree_of_basis_injective
    hInj (hAct.of_sameMPV hAP)

end MPSTensor.IsBNTCanonicalForm
