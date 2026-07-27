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
import TNLean.MPS.MPDO.FirstSiteBlocking
import TNLean.MPS.MPDO.RepresentativeGroupedLemmaL
import TNLean.MPS.Periodic.NormalizedSelfOverlap
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

namespace MPSTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- Fixed block selectors and block injectivity at one positive length give simultaneous
word-tuple span at every sufficiently large length. -/
theorem eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    (A : (k : Fin g) → MPSTensor d (dim k))
    {s p : ℕ} (hSel : HasBlockSelectorWords A s) (hp : 0 < p)
    (hAtP : ∀ k, IsNBlkInjective (A k) p) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, WordTupleSpanTop A L := by
  refine ⟨s + p, ?_⟩
  intro L hL
  have hs_le : s ≤ L := by omega
  have hp_le : p ≤ L - s := by omega
  have hSpan := wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords A
    (fun k => isNBlkInjective_of_le hp (hAtP k) hp_le) hSel
  simpa [Nat.sub_add_cancel hs_le] using hSpan

end MPSTensor

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
  exact eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    P.basis (p := 1) hSelectors (by omega) (fun j => hBlkPos j 1 (by omega))

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
    exact isNBlkInjective_of_le hp (hAtP j) hpn
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
  exact eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    (P.blockTensor p).basis (p := 1) hSelectors (by omega)
      (fun j => hBlkPos j 1 (by omega))

/-- The representatives of a BNT canonical form have eventual simultaneous word-tuple span.

Choose a common positive block-injectivity length `p`.  Block injectivity propagates to every
length at least `p`.  The three-block separation argument then gives pairwise separating words
of length `6 * p`; multiplying them gives one selector for each representative.  Appending a
long enough block-injective prefix spans the full product of representative matrix algebras.

Source: arXiv:1606.00608, lines 318--344 and Appendix C.3, lines 1848--1858. -/
theorem eventuallyRepresentativeWordTupleSpan
    (hCF : IsBNTCanonicalForm P) :
    P.EventuallyRepresentativeWordTupleSpan := by
  classical
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  obtain ⟨p, hp, hAtP⟩ := hCF.exists_common_basis_isNBlkInjective
  have hAtLeastP : ∀ (j : Fin P.basisCount) (n : ℕ), p ≤ n →
      IsNBlkInjective (P.basis j) n := by
    intro j n hpn
    exact isNBlkInjective_of_le hp (hAtP j) hpn
  let L₀ := 2 * p - 1
  have hBlk0 : ∀ j : Fin P.basisCount, IsNBlkInjective (P.basis j) L₀ := by
    intro j
    apply hAtLeastP j
    dsimp [L₀]
    omega
  have hBlk1 : ∀ j : Fin P.basisCount,
      IsNBlkInjective (P.basis j) (L₀ + 1) := by
    intro j
    apply hAtLeastP j
    dsimp [L₀]
    omega
  have hBlk3 : ∀ j : Fin P.basisCount,
      IsNBlkInjective (P.basis j)
        ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
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
  have hSepRaw :=
    forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      P.basis hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀
  have hLength : (L₀ + 1) + ((L₀ + 1) + (L₀ + 1)) = 6 * p := by
    dsimp [L₀]
    omega
  have hSep : ∀ k j : Fin P.basisCount, j ≠ k →
      PairTraceSeparatingAt (P.basis k) (P.basis j) (6 * p) := by
    intro k j hjk
    rw [← hLength]
    exact hSepRaw k j hjk
  have hPair : HasPairBlockSeparatingWords P.basis (6 * p) :=
    hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt P.basis hSep
  let selectorLength := (P.basisCount - 1) * (6 * p)
  have hSelectors : HasBlockSelectorWords P.basis selectorLength := by
    simpa [selectorLength] using
      hasBlockSelectorWords_of_pairBlockSeparatingWords P.basis hPair
  change ∃ L₁ : ℕ, ∀ L ≥ L₁, WordTupleSpanTop P.basis L
  exact eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    P.basis hSelectors hp hAtP

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

/-- Transport of representative-grouped Lemma L from an equal positive-length
MPV family for an already injectively blocked BNT canonical form.

The original tensor and the sector-decomposition tensor have the same
positive-length MPV family; the finite representative separation is supplied
by the post-blocking canonical-form hypotheses above.

Source: arXiv:1606.00608, lines 318--344 and Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree_of_basis_injective
    {D : ℕ} (A : MPSTensor d D)
    (hCF : IsBNTCanonicalForm P)
    (hInj : ∀ j, IsInjective (P.basis j))
    (hAP : SameMPV₂Pos A P.toTensor)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact hCF.insertedTensor_basis_eq_of_firstSiteActionAgree_of_basis_injective
    hInj (hAct.of_sameMPVPos hAP)

/-- Representative-grouped Lemma L before physical blocking.

Suppose that every representative has full word span at one common positive
length `L`.  Blocking `L + 1` sites makes every representative injective,
while leaving a length-`L` tail after the first-site insertion.  Representative
separation on the blocked tensors gives equality of the induced insertions;
the length-`L` word span then recovers equality of the original insertions.

This is the blocking step of arXiv:1606.00608, lines 318--344, composed with
Appendix C.3, Lemma L, lines 1835--1858.

The common positive length is explicit in this auxiliary theorem.  It is
derived from the BNT canonical-form hypotheses by
`IsBNTCanonicalForm.exists_common_basis_isNBlkInjective` and eliminated in
`insertedTensor_basis_eq_of_firstSiteActionAgree` below. -/
theorem insertedTensor_basis_eq_of_firstSiteActionAgree_of_common_blockInjective
    (hCF : IsBNTCanonicalForm P) (L : ℕ) (hL : 0 < L)
    (hInj : ∀ j, IsNBlkInjective (P.basis j) L)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree P.toTensor Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  have hInjSucc : ∀ j, IsInjective (blockTensor (P.basis j) (L + 1)) := by
    intro j
    exact (isNBlkInjective_iff_blockTensor_isInjective (P.basis j) (L + 1)).1
      (isNBlkInjective_succ_of_isNBlkInjective (P.basis j) hL (hInj j))
  have hSpan := hCF.eventuallyRepresentativeWordTupleSpan_blockTensor
    (L + 1) (by omega) hInjSucc
  have hActBlocked : FirstSiteActionAgree (P.blockTensor (L + 1)).toTensor
      (firstSiteActionOnBlock L Y) (firstSiteActionOnBlock L Z) :=
    (hAct.blockTensor L).of_sameMPV (P.sameMPV₂_blockTensor_toTensor (L + 1))
  have hEq := (P.blockTensor (L + 1)).insertedTensor_basis_eq_of_firstSiteActionAgree
    hSpan hActBlocked
  intro j
  apply insertedTensor_eq_of_firstSiteActionOnBlock_blockTensor_eq
    (P.basis j) L (hInj j)
  have hEqj := hEq j
  change insertedTensor (firstSiteActionOnBlock L Y) (blockTensor (P.basis j) (L + 1)) =
    insertedTensor (firstSiteActionOnBlock L Z) (blockTensor (P.basis j) (L + 1)) at hEqj
  exact hEqj

/-- Same-MPV transport of representative-grouped Lemma L before physical
blocking.

The common block-injectivity length is the input supplied by the canonical-form
blocking step in arXiv:1606.00608, lines 318--344.  The representative
conclusion is Appendix C.3, Lemma L, lines 1835--1858.

The common positive length is explicit in this auxiliary transport theorem and
is eliminated in
`insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree` below.

Source: arXiv:1606.00608, lines 318--344 and Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree_of_common_blockInjective
    {D : ℕ} (A : MPSTensor d D) (hCF : IsBNTCanonicalForm P)
    (L : ℕ) (hL : 0 < L) (hInj : ∀ j, IsNBlkInjective (P.basis j) L)
    (hAP : SameMPV₂Pos A P.toTensor)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact hCF.insertedTensor_basis_eq_of_firstSiteActionAgree_of_common_blockInjective
    L hL hInj (hAct.of_sameMPVPos hAP)

/-- Representative-grouped Lemma L for an unblocked BNT canonical form.

Irreducibility, left-canonicality, and normalized self-overlap force each basis
representative to have period one and hence to be normal.  A common positive
block-injectivity length for the finite representative family then supplies
the blocking hypothesis of the preceding theorem.

Source: arXiv:1606.00608, lines 318--344 and Appendix C.3, Lemma L,
lines 1835--1858; the period-one characterization is the non-periodic
canonical-form condition of arXiv:2011.12127, lines 1815--1837. -/
theorem insertedTensor_basis_eq_of_firstSiteActionAgree
    (hCF : IsBNTCanonicalForm P)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree P.toTensor Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  obtain ⟨L, hL, hInj⟩ := hCF.exists_common_basis_isNBlkInjective
  exact hCF.insertedTensor_basis_eq_of_firstSiteActionAgree_of_common_blockInjective
    L hL hInj hAct

/-- Same-MPV transport of representative-grouped Lemma L for an unblocked BNT
canonical form.

Source: arXiv:1606.00608, lines 318--344 and Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree
    {D : ℕ} (A : MPSTensor d D) (hCF : IsBNTCanonicalForm P)
    (hAP : SameMPV₂Pos A P.toTensor)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct : FirstSiteActionAgree A Y Z) :
    ∀ j, insertedTensor Y (P.basis j) = insertedTensor Z (P.basis j) := by
  exact hCF.insertedTensor_basis_eq_of_firstSiteActionAgree (hAct.of_sameMPVPos hAP)

end MPSTensor.IsBNTCanonicalForm
