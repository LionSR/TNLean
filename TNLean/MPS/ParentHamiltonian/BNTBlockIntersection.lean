/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Symmetry.StringOrderAux

/-!
# BNT block-separation hypotheses for PGVWC block intersections

This file connects the already-injective BNT block-separation product span to the
PGVWC07 one-step block-intersection identity.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12 and the
  direct-sum lemma used there.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

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

/-- Length-\(L_0\) injectivity form of the PGVWC one-step block-intersection
identity.

Assume each block is injective at a common length \(L_0\). At the source length
\(L_0+1\), writing \(S_m=\bigvee_j G_m(A_j)\), the identity is
\[
  \mathbb C^d\otimes S_m\cap S_m\otimes\mathbb C^d=S_{m+1}.
\]
This is the equation used in PGVWC07, Theorem 12, proof lines
1430--1452. -/
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

/-- Length-\(L_0\) injectivity form of the BNT product span at all sufficiently
large lengths.

Assume every block is injective at the common length \(L_0\) and the
normalization
\[
  \sum_a A^j_aA^{j\dagger}_a=I.
\]
The normalization propagates this finite-length injectivity from \(L_0\) to
\(L_0+1\) and \(3(L_0+1)\). The BNT direct-sum argument at the source length
\(L_0+1\)
then gives the simultaneous product span for every
\[
  n\ge (L_0+1)+(r-1)\,3(L_0+1).
\] -/
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

/-- A positive dual fixed point prepares the left-canonical family needed only
for the sharp BNT separation argument.

For each source block \(A^j\), set
\(B^j_a=(\Lambda^j)^{1/2}A^j_a(\Lambda^j)^{-1/2}\). Positivity of
\(\Lambda^j\) makes this an invertible gauge, while the dual fixed-point
equation makes \(B^j\) left-canonical. Irreducibility, fixed-length injectivity,
self-overlap normalization, and pairwise gauge-phase inequivalence pass to the
prepared family. The sharp tuple span is then transported back to the source
representatives.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456.
The positive dual datum used for the prepared gauge is supplied by the canonical
normalization theorem at lines 742--763. These line numbers refer to
`Papers/quant-ph_0608197/MPSarchive.tex` in this repository. Scope: this result
establishes only the fixed-length tuple span; it does not establish the global-cut
or parent-Hamiltonian kernel conclusions. -/
theorem wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, (Λ j).PosDef)
    (hDualFixed : ∀ j,
      transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hBlk1 : ∀ k : Fin r, IsNBlkInjective (A k) (L₀ + 1))
    (hBlk3 : ∀ k : Fin r,
      IsNBlkInjective (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))))
    (hL₀ : 0 < L₀) :
    WordTupleSpanTop A
      ((r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))) := by
  let prepared : (j : Fin r) → MPSTensor d (dim j) :=
    fun j => tpGauge (A j) (Λ j)
  have hGauge : ∀ j, GaugeEquiv (A j) (prepared j) := by
    intro j
    exact gaugeEquiv_tpGauge (A j) (Λ j) (hΛ j)
  have hPreparedIrr : HasIrreducibleBlocks (d := d) prepared :=
    HasIrreducibleBlocks.ofForall fun j =>
      isIrreducibleTensor_tpGauge_of_isIrreducibleMap
        (A j) (Λ j) (hΛ j)
        (isIrreducibleMap_of_isIrreducibleTensor (A j) (hIrr.block_irreducible j))
  have hPreparedLeft : IsLeftCanonicalBlockFamily (d := d) prepared :=
    IsLeftCanonicalBlockFamily.ofForall fun j =>
      tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint
        (A j) (Λ j) (hΛ j) (hDualFixed j)
  have hPreparedOverlap : HasNormalizedSelfOverlap (d := d) prepared := by
    refine HasNormalizedSelfOverlap.ofForall fun j => ?_
    have heq :
        (fun N => mpvOverlap (d := d) (prepared j) (prepared j) N) =
          fun N => mpvOverlap (d := d) (A j) (A j) N := by
      funext N
      simp only [mpvOverlap]
      apply Finset.sum_congr rfl
      intro σ _
      rw [← GaugeEquiv.sameMPV (hGauge j) N σ]
    rw [heq]
    exact hOverlap.overlap_tendsto_one j
  have hPreparedDistinct : BlocksNotGaugePhaseEquiv (d := d) prepared := by
    intro j k hjk hdim hGPE
    apply hBlocks j k hjk hdim
    exact gaugePhaseEquiv_of_gaugeEquiv_left_right_cast hdim
      (hGauge j) (by simpa [prepared] using hGPE) (hGauge k)
  have hPreparedBlk0 : ∀ k, IsNBlkInjective (prepared k) L₀ :=
    fun k => isNBlkInjective_of_gaugeEquiv (hBlk0 k) (hGauge k)
  have hPreparedBlk1 : ∀ k, IsNBlkInjective (prepared k) (L₀ + 1) :=
    fun k => isNBlkInjective_of_gaugeEquiv (hBlk1 k) (hGauge k)
  have hPreparedBlk3 : ∀ k,
      IsNBlkInjective (prepared k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) :=
    fun k => isNBlkInjective_of_gaugeEquiv (hBlk3 k) (hGauge k)
  have hPreparedSpan :=
    wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
      prepared hPreparedIrr hPreparedLeft hPreparedOverlap hPreparedDistinct
      hPreparedBlk0 hPreparedBlk1 hPreparedBlk3 hL₀ hr
  exact wordTupleSpanTop_of_family_gaugeEquiv_symm hPreparedSpan hGauge

/-- The normalized BNT hypotheses give the simultaneous product span in the
source range of PGVWC07, Theorem 12.

For at least two blocks, the sharp direct-sum argument gives the full tuple
span at length \(3(r-1)(L_0+1)\). Right-canonical normalization then propagates
that span to every larger length. Thus no additional injective prefix is
needed. The base span is arXiv:quant-ph/0608197, lines 1346--1421; the unital
propagation is lines 893--898.

**Scope restriction (doubly normalized specialization):** At the PGVWC07 source
length bound, `hUnital` is the source identity
\(\sum_a A^j_a(A^j_a)^\dagger=1\), while `hLeft` additionally specializes the
source dual fixed-point equation
\(\sum_a (A^j_a)^\dagger\Lambda_j A^j_a=\Lambda_j\) to
\(\Lambda_j=1\). The general normalization is documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.
-/
theorem wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    WordTupleSpanTop A n := by
  have hBlk1 : ∀ k : Fin r, IsNBlkInjective (A k) (L₀ + 1) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hBlk3 : ∀ k : Fin r,
      IsNBlkInjective (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hBase : WordTupleSpanTop A
      ((r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))) :=
    wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀ hr
  exact wordTupleSpanTop_of_ge_of_unital A hBase hUnital hn

/-- The PGVWC07 source normalization gives the simultaneous product span at
all lengths above the sharp BNT bound.

The positive dual fixed points are used only to prepare a left-canonical gauge
for the base separation theorem. The resulting base span is transported back,
and the source identity \(\sum_a A^j_aA^{j\dagger}_a=I\) propagates it to
longer words. No diagonality hypothesis on the dual fixed points is needed.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456.
The positive dual datum used for the prepared gauge is supplied by the canonical
normalization theorem at lines 742--763. These line numbers refer to
`Papers/quant-ph_0608197/MPSarchive.tex` in this repository. Scope: this result
establishes only the propagated tuple span; it does not establish the global-cut
or parent-Hamiltonian kernel conclusions. -/
theorem wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, (Λ j).PosDef)
    (hDualFixed : ∀ j,
      transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    WordTupleSpanTop A n := by
  have hBlk1 : ∀ k : Fin r, IsNBlkInjective (A k) (L₀ + 1) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hBlk3 : ∀ k : Fin r,
      IsNBlkInjective (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
    intro k
    exact isNBlkInjective_of_ge_of_unital (A k) (hUnital k) (hBlk0 k) (by omega)
  have hBase :=
    wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1_of_dualFixedPoint
      A hr hIrr hOverlap hBlocks Λ hΛ hDualFixed hBlk0 hBlk1 hBlk3 hL₀
  exact wordTupleSpanTop_of_ge_of_unital A hBase hUnital hn

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

/-- Length-\(L_0\) injectivity form of the internal-direct-sum conclusion for
the block local spaces. -/
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

/-- In the PGVWC07 source range, the normalized BNT local spaces form an
internal direct sum.

This is the direct-sum lemma in arXiv:quant-ph/0608197, lines 1346--1421.

**Scope restriction (doubly normalized specialization):** At the PGVWC07 source
length bound, `hUnital` is the source identity
\(\sum_a A^j_a(A^j_a)^\dagger=1\), while `hLeft` additionally specializes the
source dual fixed-point equation
\(\sum_a (A^j_a)^\dagger\Lambda_j A^j_a=\Lambda_j\) to
\(\Lambda_j=1\). The general normalization is documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.
-/
theorem groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    iSupIndep fun j : Fin r => groundSpace (A j) n :=
  groundSpace_iSupIndep_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07
      A hr hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn)

/-- Under the PGVWC07 source normalization, the block local spaces form an
internal direct sum throughout the sharp source range.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456.
The positive dual datum used to reach the prepared canonical gauge is supplied
by the canonical normalization theorem at lines 742--763. These line numbers
refer to `Papers/quant-ph_0608197/MPSarchive.tex` in this repository. Scope: this
result establishes only independence of the block local spaces; it does not
establish the global-cut or parent-Hamiltonian kernel conclusions. -/
theorem groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, (Λ j).PosDef)
    (hDualFixed : ∀ j,
      transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    iSupIndep fun j : Fin r => groundSpace (A j) n :=
  groundSpace_iSupIndep_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
      A hr hIrr hOverlap hBlocks Λ hΛ hDualFixed hBlk0 hL₀ hUnital hn)

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

/-- Length-\(L_0\) injectivity form of the one-step block-intersection identity
at every length above the BNT block-separation bound. -/
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

/-- The one-step block-intersection identity holds throughout the sharp length
range in PGVWC07, Theorem 12.

The internal middle-word length is at least \(3(r-1)(L_0+1)\). This is the
intersection step in arXiv:quant-ph/0608197, lines 1424--1452.

**Scope restriction (doubly normalized specialization):** At the PGVWC07 source
length bound, `hUnital` is the source identity
\(\sum_a A^j_a(A^j_a)^\dagger=1\), while `hLeft` additionally specializes the
source dual fixed-point equation
\(\sum_a (A^j_a)^\dagger\Lambda_j A^j_a=\Lambda_j\) to
\(\Lambda_j=1\). The general normalization is documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.
-/
theorem pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07
      A hr hIrr hLeft hOverlap hBlocks hBlk0 hL₀ hUnital hn)
    hUnital

/-- The PGVWC07 one-step restriction-intersection identity holds under the
source unital normalization and positive dual fixed points, without a
left-canonical hypothesis on the source representatives.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456.
The positive dual datum used to reach the prepared canonical gauge is supplied
by the canonical normalization theorem at lines 742--763. These line numbers
refer to `Papers/quant-ph_0608197/MPSarchive.tex` in this repository. Scope: this
result establishes only the one-step restriction-intersection identity; it does
not establish the global-cut or parent-Hamiltonian kernel conclusions. -/
theorem
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, (Λ j).PosDef)
    (hDualFixed : ∀ j,
      transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    {L₀ : ℕ}
    (hBlk0 : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    {n : ℕ}
    (hn : (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ n) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
      A hr hIrr hOverlap hBlocks Λ hΛ hDualFixed hBlk0 hL₀ hUnital hn)
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

/-- Length-\(L_0\) injectivity form of the large-length block intersection as
an internal direct sum. -/
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

/-- Length-\(L_0\) injectivity form of the eventual block-intersection identity
without a separate one-site injectivity assumption. -/
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
