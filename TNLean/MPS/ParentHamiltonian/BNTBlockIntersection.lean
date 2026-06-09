/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum

/-!
# BNT direct-sum input for block intersections

This file connects the already-injective BNT direct-sum product span to the
PGVWC07 one-step block-intersection identity.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12 and Lemma
  `lem:direct-sum`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- Already-injective BNT direct-sum data give the PGVWC one-step
block-intersection identity at the resulting product-span length.

The internal word length is
\[
  n=L+(r-1)(L+(L+L)).
\]
At this length the direct-sum theorem supplies the common blockwise word span
required in the PGVWC07 restriction-intersection argument. -/
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

/-- BNT block-separating equations and a homogeneous block-injectivity period
window give the PGVWC block-intersection identity for all sufficiently large
lengths.

Let
\[
  S=L+(L+L),\qquad q=(r-1)S.
\]
The BNT direct-sum hypotheses give equations that separate each ordered pair of
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

end MPSTensor
