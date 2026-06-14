/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum

/-!
# BNT block-separation hypotheses for PGVWC block intersections

This file connects the already-injective BNT block-separation product span to the
PGVWC07 one-step block-intersection identity.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 2blocks.2 and the
  direct-sum lemma used there.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- Already-injective BNT block-separation conditions give the PGVWC one-step
block-intersection identity at the resulting product-span length.

The internal word length is
\[
  n=L+(r-1)(L+(L+L)).
\]
At this length the block-separation theorem supplies the common blockwise word
span required in the PGVWC07 restriction-intersection argument. -/
theorem pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    {n : ℕ} (hn : n = L + (r - 1) * (L + (L + L)))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  subst n
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)
    hUnital

/-- Condition-C1 form of the PGVWC one-step block-intersection identity.

Under a common Condition C1 length \(L_0\), the source length is \(L_0+1\).
Writing \(S_m=\bigvee_j G_m(A_j)\), the identity is
\[
  \mathbb C^d\otimes S_m\cap S_m\otimes\mathbb C^d=S_{m+1}.
\]
This is the equation used in PGVWC07, Theorem 2blocks.2, proof lines
1430--1452.

**Unfaithful:** This proof relies on
`wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1`, which
transitively uses the boundary-closing coordinate comparison rather than
deriving it from arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented
in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hBlk1 : ∀ k : Fin r, IsNBlkInjective (A k) (L₀ + 1))
    (hBlk3 : ∀ k : Fin r,
      IsNBlkInjective (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))))
    (hL₀ : 0 < L₀)
    {n : ℕ}
    (hn : n =
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  subst n
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀)
    hUnital

/-- Homogeneous span propagation gives the BNT product span at every
sufficiently large length.

If the blocks are normalized by
\[
  \sum_a A^j_aA^{j\dagger}_a=I
\]
and \(S_L(A^j)=M_{D_j}(\mathbb C)\) for each block, then
\(S_m(A^j)=M_{D_j}(\mathbb C)\) for every \(m\ge L\).  Combining this with
block-separating equations of length \(S\) gives
\[
  \operatorname{span}\{(A^1_w,\ldots,A^r_w):|w|=n\}
    =\prod_j M_{D_j}(\mathbb C)
\]
for \(n\ge L+(r-1)S\). -/
theorem wordTupleSpanTop_of_ge_of_common_blockInjective_of_unital_of_pairBlockSeparatingWords
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S n : ℕ}
    (hInj : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hUnital : ∀ k : Fin r, ∑ a : Fin d, A k a * (A k a)ᴴ = 1)
    (hPair : HasPairBlockSeparatingWords A S)
    (hn : L + (r - 1) * S ≤ n) :
    WordTupleSpanTop A n := by
  let q : ℕ := (r - 1) * S
  have hInjTail : ∀ k : Fin r, IsNBlkInjective (A k) (n - q) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hInj k) (by omega)
  have hSpan :
      WordTupleSpanTop A ((n - q) + (r - 1) * S) :=
    wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords
      A hInjTail hPair
  have hlen : (n - q) + (r - 1) * S = n := by
    omega
  rwa [hlen] at hSpan

/-- BNT block-separation conditions and PGVWC07 normalization give the
simultaneous product span at every length above the BNT block-separation bound.

With \(S=L+(L+L)\), the conclusion is
\[
  \operatorname{span}\{(A^1_w,\ldots,A^r_w):|w|=n\}
    =\prod_j M_{D_j}(\mathbb C)
\]
for \(n\ge L+(r-1)S\). -/
theorem wordTupleSpanTop_of_ge_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ} (hn : L + (r - 1) * (L + (L + L)) ≤ n) :
    WordTupleSpanTop A n := by
  let S : ℕ := L + (L + L)
  have hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) S := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk k) (by omega)
  have hPair : HasPairBlockSeparatingWords A S := by
    simpa [S] using
      (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv
        A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)
  exact wordTupleSpanTop_of_ge_of_common_blockInjective_of_unital_of_pairBlockSeparatingWords
    A hBlk hUnital hPair (by simpa [S] using hn)

/-- Condition-C1 form of the BNT product span at all sufficiently large lengths.

Assume Condition C1 for every block at the common length \(L_0\) and the
normalization
\[
  \sum_a A^j_aA^{j\dagger}_a=I.
\]
The normalization propagates Condition C1 from \(L_0\) to \(L_0+1\) and
\(3(L_0+1)\). The BNT direct-sum argument at the source length \(L_0+1\)
then gives the simultaneous product span for every
\[
  n\ge (L_0+1)+(r-1)\,3(L_0+1).
\]

**Unfaithful:** This proof relies on
`hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1`, which
transitively uses the boundary-closing coordinate comparison rather than
deriving it from arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented
in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    WordTupleSpanTop A n := by
  let S : ℕ := (L₀ + 1) + ((L₀ + 1) + (L₀ + 1))
  have hBlk1 : ∀ k : Fin r, IsNBlkInjective (A k) (L₀ + 1) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) S := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hPair : HasPairBlockSeparatingWords A S := by
    simpa [S] using
      (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
        A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 (by simpa [S] using hBlk3) hL₀)
  exact wordTupleSpanTop_of_ge_of_common_blockInjective_of_unital_of_pairBlockSeparatingWords
    A hBlk1 hUnital hPair (by simpa [S] using hn)

/-- Under the normalized BNT block-separation hypotheses, the local spaces
\(G_n(A^j)\) form an internal direct sum.

Let \(S=L+(L+L)\).  If \(n\ge L+(r-1)S\), then
\[
  G_n(A^1)+\cdots+G_n(A^r)
\]
is an internal direct sum: whenever \(\phi_j\in G_n(A^j)\) and
\(\sum_j\phi_j=0\), all \(\phi_j\) vanish. -/
theorem groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ} (hn : L + (r - 1) * (L + (L + L)) ≤ n) :
    iSupIndep fun j : Fin r => groundSpace (A j) n :=
  groundSpace_iSupIndep_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital hn)

/-- Condition-C1 form of the internal-direct-sum conclusion for the block local
spaces.

**Unfaithful:** This proof relies on
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1`, which transitively uses
the boundary-closing coordinate comparison rather than deriving it from
arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    iSupIndep fun j : Fin r => groundSpace (A j) n :=
  groundSpace_iSupIndep_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn)

/-- BNT block-separation conditions and PGVWC07 normalization give the one-step
block-intersection identity at every length above the BNT block-separation
bound.

For \(S=L+(L+L)\), if \(n\ge L+(r-1)S\), then, writing
\[
  S_n=\bigvee_jG_{n+1}(A^j),
\]
one has
\[
  \left(\bigcap_b\operatorname{Res}_{-,b}^{-1}S_n\right)
  \cap
  \left(\bigcap_a\operatorname{Res}_{a,-}^{-1}S_n\right)
  =
  \bigvee_jG_{n+2}(A^j).
\] -/
theorem pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ} (hn : L + (r - 1) * (L + (L + L)) ≤ n) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital hn)
    hUnital

/-- Condition-C1 form of the one-step block-intersection identity at every
length above the BNT block-separation bound.

**Unfaithful:** This proof relies on
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1`, which transitively uses
the boundary-closing coordinate comparison rather than deriving it from
arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn)
    hUnital

/-- Normalized BNT block-separation hypotheses give the large-length block
intersection as an internal direct sum.

For \(S=L+(L+L)\), if \(n\ge L+(r-1)S\), then the sums
\[
  \bigvee_jG_{n+1}(A^j),
  \qquad
  \bigvee_jG_{n+2}(A^j)
\]
are internal direct sums, and the PGVWC one-step intersection identity holds
with these local spaces:
\[
  \left(\bigcap_b\operatorname{Res}_{-,b}^{-1}
    \bigvee_jG_{n+1}(A^j)\right)
  \cap
  \left(\bigcap_a\operatorname{Res}_{a,-}^{-1}
    \bigvee_jG_{n+1}(A^j)\right)
  =
  \bigvee_jG_{n+2}(A^j).
\] -/
theorem pgvwc07_directSum_restriction_intersection_of_ge_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ} (hn : L + (r - 1) * (L + (L + L)) ≤ n) :
    iSupIndep (fun j : Fin r => groundSpace (A j) (n + 1)) ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) (n + 2)) ∧
        ((⨅ b : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
          (⨅ a : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
          ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact ⟨
    groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital (by omega),
    groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital (by omega),
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital hn⟩

/-- Condition-C1 form of the large-length block intersection as an internal
direct sum.

**Unfaithful:** This proof relies on the finite-\(C_1\) internal-direct-sum and
block-intersection conclusions above, which transitively use the boundary-closing
coordinate comparison rather than deriving it from arXiv:2011.12127,
Section IV.C, lines 2078--2079. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem pgvwc07_directSum_restriction_intersection_of_ge_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    iSupIndep (fun j : Fin r => groundSpace (A j) (n + 1)) ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) (n + 2)) ∧
        ((⨅ b : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
          (⨅ a : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
          ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact ⟨
    groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital (by omega),
    groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital (by omega),
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn⟩

/-- BNT block-separating equations and a homogeneous block-injectivity period
window give the PGVWC block-intersection identity for all sufficiently large
lengths.

Let
\[
  S=L+(L+L),\qquad q=(r-1)S.
\]
The BNT block-separation hypotheses give equations that separate each ordered pair of
blocks at length \(S\). If the individual blocks are injective at a positive
length \(p\) and throughout a complete window of \(p+q\) consecutive lengths,
then the simultaneous block-word tuples span the full product algebra in a
complete period window. The abstract period-window block-intersection theorem
then gives the eventual intersection identity. -/
theorem pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_period_window
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hBlkPeriod : ∀ k : Fin r, IsNBlkInjective (A k) period)
    (hBlkWindow : ∀ s : ℕ, s < period + (r - 1) * (L + (L + L)) →
      ∀ k : Fin r, IsNBlkInjective (A k) (start + s))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  let S : ℕ := L + (L + L)
  let q : ℕ := (r - 1) * S
  have hPair : HasPairBlockSeparatingWords A S := by
    simpa [S] using
      (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv
        A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)
  have hPeriodSpan : WordTupleSpanTop A (period + q) := by
    simpa [S, q] using
      (wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords
        A hBlkPeriod hPair)
  have hPeriodPos : 0 < period + q := by
    exact Nat.add_pos_left hperiod_pos q
  have hWindowSpan : ∀ s : ℕ, s < period + q →
      WordTupleSpanTop A ((start + q) + s) := by
    intro s hs
    have hSpan :=
      wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords
        A (hBlkWindow s (by simpa [q, S] using hs)) hPair
    simpa [q, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSpan
  exact pgvwc07_iSup_restriction_intersection_eventually_of_period_window
    A hPeriodPos hPeriodSpan hWindowSpan hUnital

/-- BNT block-separation hypotheses and the PGVWC07 normalization give the eventual
block-intersection identity without separately assuming a higher-length
block-injectivity window.

The normalization
\[
  \sum_a A^j_aA^{j\dagger}_a=I
\]
propagates the full homogeneous span of each block from length \(L\) to every
larger length. Thus the needed consecutive range of block-injectivity
hypotheses is obtained from the equations
\[
  S_L(A^j)=M_{D_j}(\mathbb C),\qquad
  S_{L+s}(A^j)=M_{D_j}(\mathbb C).
\] -/
theorem pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  refine ⟨L + (r - 1) * (L + (L + L)), ?_⟩
  intro n hn
  exact pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital
    A hIrr hLeft hOverlap hBlocks hBlk hInj hL hUnital hn

/-- Condition-C1 form of the eventual block-intersection identity without a
separate one-site injectivity assumption.

**Unfaithful:** This proof relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, which
transitively uses the boundary-closing coordinate comparison rather than
deriving it from arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented
in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`; prove the comparison. -/
theorem pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  refine ⟨(L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))), ?_⟩
  intro n hn
  exact pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1
    A hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn

end MPSTensor
