/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.FundamentalTheorem.SectorBNT.Blocking
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.MPDO.BiCFDerivation.Blocking
import TNLean.MPS.MPDO.RepresentativeGroupedLemmaL
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Representative separation after injective blocking

For a BNT canonical-form sector decomposition whose representative tensors are
already injective, the representative word tuples span the full product matrix
algebra at every sufficiently large length.  Pairwise separation gives a fixed
selector suffix, while one-site injectivity gives a full matrix-algebra prefix
at every positive remaining length.

The file also derives the corresponding statement from an unblocked BNT
canonical form and a positive blocking length at which every representative
becomes injective.  Pair separation is proved before blocking at a divisible
word length and transported exactly to the blocked representatives; no
preservation theorem for the full canonical-form structure is assumed.

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

/-- Physical blocking transports the BNT hypotheses needed for simultaneous
representative separation, without asserting preservation of the entire
canonical-form structure.

Suppose `p > 0` and every `p`-blocked representative is injective.  Pair
separation is first obtained for the original representatives at length
`6 * p`, using Condition C1 at length `2 * p - 1`, and is then transported to
length `6` for the blocked representatives.  The resulting selector suffix,
together with injectivity of the blocked representatives, gives simultaneous
word-tuple span at every sufficiently large blocked length.

This is the representative-level form of the blocking and block-injectivity
argument in arXiv:1606.00608, lines 318--344, used in Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem eventuallyRepresentativeWordTupleSpan_blockTensor
    (hCF : IsBNTCanonicalForm P) (p : ℕ) (hp : 0 < p)
    (hInj : ∀ j, IsInjective (MPSTensor.blockTensor (P.basis j) p)) :
    (P.blockTensor p).EventuallyRepresentativeWordTupleSpan := by
  classical
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  have hAtP : ∀ j : Fin P.basisCount, IsNBlkInjective (P.basis j) p := by
    intro j
    exact (isNBlkInjective_iff_blockTensor_isInjective (P.basis j) p).2 (hInj j)
  have hAtLeastP : ∀ (j : Fin P.basisCount) (n : ℕ), p ≤ n →
      IsNBlkInjective (P.basis j) n := by
    intro j n hpn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpn
    clear hpn
    induction k with
    | zero => simpa using hAtP j
    | succ k ih =>
        simpa [Nat.add_assoc] using
          (isNBlkInjective_succ_of_isNBlkInjective
            (P.basis j) (Nat.add_pos_left hp k) ih)
  let L₀ := 2 * p - 1
  have hBlk0 : ∀ j : Fin P.basisCount, IsNBlkInjective (P.basis j) L₀ := by
    intro j
    apply hAtLeastP j
    dsimp [L₀]
    omega
  have hBlk1 : ∀ j : Fin P.basisCount, IsNBlkInjective (P.basis j) (L₀ + 1) := by
    intro j
    apply hAtLeastP j
    dsimp [L₀]
    omega
  have hBlk3 : ∀ j : Fin P.basisCount,
      IsNBlkInjective (P.basis j) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
    intro j
    apply hAtLeastP j
    dsimp [L₀]
    omega
  have hIrr : HasIrreducibleBlocks (d := d) P.basis :=
    HasIrreducibleBlocks.ofForall hCF.basis_irreducible
  have hLeft : IsLeftCanonicalBlockFamily (d := d) P.basis :=
    IsLeftCanonicalBlockFamily.ofForall hCF.basis_left_canonical
  have hOverlap : HasNormalizedSelfOverlap (d := d) P.basis :=
    HasNormalizedSelfOverlap.ofForall hCF.basis_normalized_self_overlap
  have hBlocks : BlocksNotGaugePhaseEquiv (d := d) P.basis :=
    hCF.basis_distinct
  have hL₀ : 0 < L₀ := by
    dsimp [L₀]
    omega
  have hSepOriginalRaw :=
    forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      P.basis hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀
  have hLength : (L₀ + 1) + ((L₀ + 1) + (L₀ + 1)) = 6 * p := by
    dsimp [L₀]
    omega
  have hSepOriginal : ∀ k j : Fin P.basisCount, j ≠ k →
      PairTraceSeparatingAt (P.basis k) (P.basis j) (6 * p) := by
    intro k j hjk
    rw [← hLength]
    exact hSepOriginalRaw k j hjk
  have hSepBlocked : ∀ k j : Fin P.basisCount, j ≠ k →
      PairTraceSeparatingAt
        (MPSTensor.blockTensor (P.basis k) p)
        (MPSTensor.blockTensor (P.basis j) p) 6 := by
    intro k j hjk
    exact pairTraceSeparatingAt_blockTensor
      (P.basis k) (P.basis j) p 6 (hSepOriginal k j hjk)
  have hPair : HasPairBlockSeparatingWords (P.blockTensor p).basis 6 := by
    change HasPairBlockSeparatingWords
      (fun j ↦ MPSTensor.blockTensor (P.basis j) p) 6
    exact hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt
      (fun j ↦ MPSTensor.blockTensor (P.basis j) p) hSepBlocked
  let selectorLength := (P.basisCount - 1) * 6
  have hSelectors : HasBlockSelectorWords (P.blockTensor p).basis selectorLength := by
    change HasBlockSelectorWords (P.blockTensor p).basis ((P.basisCount - 1) * 6)
    exact hasBlockSelectorWords_of_pairBlockSeparatingWords (P.blockTensor p).basis hPair
  have hBlkPos : ∀ (j : Fin P.basisCount) (n : ℕ), 0 < n →
      IsNBlkInjective ((P.blockTensor p).basis j) n := by
    intro j n hn
    change IsNBlkInjective (MPSTensor.blockTensor (P.basis j) p) n
    exact (wordSpan_eq_top_iff_isNBlkInjective
      (MPSTensor.blockTensor (P.basis j) p) n).mp
      (wordSpan_eq_top_of_isInjective (hInj j) hn)
  change ∃ L₁ : ℕ, ∀ L ≥ L₁, WordTupleSpanTop (P.blockTensor p).basis L
  refine ⟨selectorLength + 1, ?_⟩
  intro L hL
  have hSelectorLength_le : selectorLength ≤ L := by omega
  have hPrefixPos : 0 < L - selectorLength := by omega
  have hSpan := wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    (P.blockTensor p).basis
    (fun j ↦ hBlkPos j (L - selectorLength) hPrefixPos) hSelectors
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
