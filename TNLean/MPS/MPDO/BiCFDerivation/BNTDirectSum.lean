/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumUniqueness
import TNLean.MPS.MPDO.BiCFDerivation.Selectors

/-!
# BNT input for the equal-size direct-sum branch

This file connects the same-dimension BNT separation hypothesis to the
parent-Hamiltonian uniqueness input for David--Perez-Garcia--Schuch--Wolf,
Lemma `lem:direct-sum`.

The statement deliberately keeps the direct-sum hypotheses explicit:
`BlocksNotGaugePhaseEquiv` gives the long-chain non-proportional MPV witness,
while injectivity and length-`L` block injectivity are still separate inputs to
the parent-Hamiltonian argument.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- Same-dimension BNT-separated blocks give the equal-size direct-sum
directness conclusion once the direct-sum injectivity hypotheses are supplied.

This is the BNT-facing form of the equal-size branch of
David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`.  The theorem does
not infer injectivity or transport non-equivalence through blocking; those
inputs remain explicit. It is exported for the pair-trace theorem below and for
downstream direct-sum comparisons that need the image-space directness statement
before applying trace separation. -/
theorem groundSpace_inf_eq_bot_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    (hAj_blk : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L)
    (hAk_blk : IsNBlkInjective (A k) L)
    (hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)))
    (hAk_inj : IsInjective (A k))
    (hL : 1 < L) :
    groundSpace (cast (congr_arg (MPSTensor d) hdim) (A j)) (L + (L + L)) ⊓
        groundSpace (A k) (L + (L + L)) = ⊥ := by
  obtain ⟨N, hNmin, hSep⟩ :=
    exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
      A hIrr hLeft hOverlap hBlocks hjk hdim (max 2 L)
  have hN : 2 ≤ N := le_trans (Nat.le_max_left 2 L) hNmin
  have hLN : L ≤ N := le_trans (Nat.le_max_right 2 L) hNmin
  exact groundSpace_inf_eq_bot_of_exists_not_forall_mpv_eq_mul_of_dim_ge
    hAj_blk hAk_blk hAj_inj hAk_inj le_rfl hL ⟨N, hN, hLN, hSep⟩

/-- Same-dimension BNT-separated blocks give the PGVWC directness conclusion from
Condition C1 at a finite length \(L_0\).

PGVWC07, Lemma `lem:direct-sum`, first uses Condition C1 in each block at
length \(L_0\), then compares the spaces \(\mathcal G_{L_0+1}^{A^j}\). This
version follows that length convention and does not assume one-site
injectivity. -/
theorem groundSpace_inf_eq_bot_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    {L₀ : ℕ}
    (hAj_c1 : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L₀)
    (hAk_c1 : IsNBlkInjective (A k) L₀)
    (hAj_blk : IsNBlkInjective
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (L₀ + 1))
    (hAk_blk : IsNBlkInjective (A k) (L₀ + 1))
    (hL₀ : 0 < L₀) :
    groundSpace (cast (congr_arg (MPSTensor d) hdim) (A j))
        ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ⊓
      groundSpace (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) = ⊥ := by
  obtain ⟨N, hNmin, hSep⟩ :=
    exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
      A hIrr hLeft hOverlap hBlocks hjk hdim (max 2 (L₀ + 1))
  have hN : 2 ≤ N := le_trans (Nat.le_max_left 2 (L₀ + 1)) hNmin
  have hLN : L₀ + 1 ≤ N := le_trans (Nat.le_max_right 2 (L₀ + 1)) hNmin
  exact groundSpace_inf_eq_bot_of_exists_not_forall_mpv_eq_mul_of_dim_ge_succ
    hAj_c1 hAk_c1 hAj_blk hAk_blk le_rfl hL₀ ⟨N, hN, hLN, hSep⟩

/-- Same-dimension BNT-separated blocks give homogeneous pair trace separation
at the three-block length once the direct-sum injectivity hypotheses are
supplied.

This is the pair-trace form consumed by selector and word-span constructions.
The theorem still does not infer block injectivity at either length; those
remain explicit direct-sum inputs. -/
theorem pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    (hAj_blk : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L)
    (hAk_blk : IsNBlkInjective (A k) L)
    (hAj_blk3 : IsNBlkInjective
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (L + (L + L)))
    (hAk_blk3 : IsNBlkInjective (A k) (L + (L + L)))
    (hAj_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A j)))
    (hAk_inj : IsInjective (A k))
    (hL : 1 < L) :
    PairTraceSeparatingAt
    (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k) (L + (L + L)) := by
  exact pairTraceSeparatingAt_of_groundSpace_inf_eq_bot_of_isNBlkInjective
    (groundSpace_inf_eq_bot_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
      A hIrr hLeft hOverlap hBlocks hjk hdim hAj_blk hAk_blk hAj_inj hAk_inj hL)
    hAj_blk3 hAk_blk3

/-- Same-dimension BNT-separated blocks give homogeneous pair trace separation
at the PGVWC length \(3(L_0+1)\), assuming Condition C1 at \(L_0\) and the
corresponding block injectivity at \(L_0+1\) and \(3(L_0+1)\). -/
theorem pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k)
    {L₀ : ℕ}
    (hAj_c1 : IsNBlkInjective (cast (congr_arg (MPSTensor d) hdim) (A j)) L₀)
    (hAk_c1 : IsNBlkInjective (A k) L₀)
    (hAj_blk : IsNBlkInjective
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (L₀ + 1))
    (hAk_blk : IsNBlkInjective (A k) (L₀ + 1))
    (hAj_blk3 : IsNBlkInjective
      (cast (congr_arg (MPSTensor d) hdim) (A j))
      ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))))
    (hAk_blk3 : IsNBlkInjective (A k) ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))))
    (hL₀ : 0 < L₀) :
    PairTraceSeparatingAt
      (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
      ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
  exact pairTraceSeparatingAt_of_groundSpace_inf_eq_bot_of_isNBlkInjective
    (groundSpace_inf_eq_bot_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge_c1
      A hIrr hLeft hOverlap hBlocks hjk hdim hAj_c1 hAk_c1 hAj_blk hAk_blk hL₀)
    hAj_blk3 hAk_blk3

/-- BNT-separated blocks give a common three-block homogeneous pair trace
separation length for every ordered pair, once the direct-sum injectivity
hypotheses are supplied.

The same-dimension branch uses the BNT non-gauge-equivalence witness.  The
unequal-dimension branch uses the strict-size part of the direct-sum argument.
No block injectivity is inferred here; the direct-sum hypotheses remain
explicit. -/
theorem forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) (L + (L + L)) := by
  intro k j hjk
  by_cases hdim : dim k = dim j
  · apply pairTraceSeparatingAt_uncast_left hdim
    exact pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge
      A hIrr hLeft hOverlap hBlocks hjk.symm hdim
      ((isNBlkInjective_cast_dim hdim (A k) L).2 (hBlk k))
      (hBlk j)
      ((isNBlkInjective_cast_dim hdim (A k) (L + (L + L))).2 (hBlk3 k))
      (hBlk3 j)
      ((isInjective_cast_dim hdim (A k)).2 (hInj k))
      (hInj j) hL
  · exact pairTraceSeparatingAt_threeBlock_of_isNBlkInjective_of_dim_ne
      (hBlk k) (hBlk j) (hBlk3 k) (hBlk3 j) hdim

/-- BNT-separated blocks give the PGVWC pair trace separation length from
Condition C1 at \(L_0\), without the one-site special case of Condition C1.

The length is \(3(L_0+1)\), written as
\((L_0+1)+((L_0+1)+(L_0+1))\) to match the formal concatenation of the three
blocks in PGVWC07, Lemma `lem:direct-sum`. -/
theorem forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
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
    (hL₀ : 0 < L₀) :
    ∀ k j : Fin r, j ≠ k →
      PairTraceSeparatingAt (A k) (A j)
        ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) := by
  intro k j hjk
  by_cases hdim : dim k = dim j
  · apply pairTraceSeparatingAt_uncast_left hdim
    exact pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_same_dim_of_dim_ge_c1
      A hIrr hLeft hOverlap hBlocks hjk.symm hdim
      ((isNBlkInjective_cast_dim hdim (A k) L₀).2 (hBlk0 k))
      (hBlk0 j)
      ((isNBlkInjective_cast_dim hdim (A k) (L₀ + 1)).2 (hBlk1 k))
      (hBlk1 j)
      ((isNBlkInjective_cast_dim hdim (A k)
        ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))).2 (hBlk3 k))
      (hBlk3 j)
      hL₀
  · exact pairTraceSeparatingAt_threeBlock_of_isNBlkInjective_of_dim_ne
      (hBlk1 k) (hBlk1 j) (hBlk3 k) (hBlk3 j) hdim

/-- Existential common-length form of
`forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv`.

Packages the universal pair-separation result into an existential: there is a
single finite length at which every ordered pair of distinct blocks is
trace-separated. -/
theorem exists_forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S :=
  ⟨L + (L + L),
    forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL⟩

/-- Existential common-length form of
`forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1`. -/
theorem exists_forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
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
    (hL₀ : 0 < L₀) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S :=
  ⟨(L₀ + 1) + ((L₀ + 1) + (L₀ + 1)),
    forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀⟩

/-- BNT-separated blocks give common pairwise block-separating equations at the
three-block length, once the direct-sum injectivity hypotheses are supplied.

This is the selector-facing consequence of the direct-sum input used in
PGVWC07, Lemma `lem:direct-sum`: the homogeneous trace separation at
\(L+(L+L)\) is converted into equations selecting one block against another. -/
theorem hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    HasPairBlockSeparatingWords A (L + (L + L)) :=
  hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt A
    (forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)

/-- BNT-separated blocks give common pairwise block-separating equations at
length \(3(L_0+1)\) from Condition C1 at \(L_0\). -/
theorem hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
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
    (hL₀ : 0 < L₀) :
    HasPairBlockSeparatingWords A ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) :=
  hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt A
    (forall_pairTraceSeparatingAt_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀)

/-- BNT-separated blocks satisfy the abstract block-injectivity selector datum
under the same explicit direct-sum injectivity hypotheses. -/
theorem propBlockInjective_of_blocksNotGaugePhaseEquiv_directSum
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    PropBlockInjective A :=
  propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords A hBlk
    (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)

/-- Finite-C1 version of the BNT abstract block-injectivity selector datum. -/
theorem propBlockInjective_of_blocksNotGaugePhaseEquiv_directSum_c1
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
    (hL₀ : 0 < L₀) :
    PropBlockInjective A :=
  propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords A hBlk1
    (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀)

/-- Common block injectivity and the BNT direct-sum separation input give a
finite simultaneous block-word span.

Explicitly, the length is
\[
  L+(r-1)(L+(L+L)),
\]
because the length-\(L\) block-injective prefix supplies the target matrix in a
chosen block, and the \(r-1\) three-block selectors kill the other blocks. -/
theorem wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    WordTupleSpanTop A (L + (r - 1) * (L + (L + L))) :=
  wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords A hBlk
    (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)

/-- Finite-C1 version of the BNT direct-sum product span.

The simultaneous block-word tuples span the full product algebra at
\[
  (L_0+1)+(r-1)\,3(L_0+1).
\]
The proof follows PGVWC07 by using Condition C1 at \(L_0\), the source
comparison length \(L_0+1\), and the three-block separation length
\(3(L_0+1)\). -/
theorem wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1
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
    (hL₀ : 0 < L₀) :
    WordTupleSpanTop A
      ((L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))) :=
  wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords A hBlk1
    (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀)

/-- Existential form of
`wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors`. -/
theorem exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L) :
    ∃ N : ℕ, WordTupleSpanTop A N :=
  ⟨L + (r - 1) * (L + (L + L)),
    wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL⟩

/-- Existential form of
`wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1`. -/
theorem exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1
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
    (hL₀ : 0 < L₀) :
    ∃ N : ℕ, WordTupleSpanTop A N :=
  ⟨(L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))),
    wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1
      A hIrr hLeft hOverlap hBlocks hBlk0 hBlk1 hBlk3 hL₀⟩

end MPSTensor
