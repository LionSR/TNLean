/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalChainGroundSpace
import TNLean.MPS.ParentHamiltonian.BNTBlockIntersection

/-!
# Block-diagonal propagation for parent-Hamiltonian local spaces

This file combines the normalized BNT block-separation hypotheses with the
one-step identity from arXiv:quant-ph/0608197
\[
  \mathbb C^d\otimes S_M\cap S_M\otimes\mathbb C^d=S_{M+1},
  \qquad S_M=\bigvee_jG_M(A_j),
\]
as used in Theorem 12 of arXiv:quant-ph/0608197. The separate periodic
step is the comparison obtained when closing the boundaries with block-diagonal
boundary conditions, as in arXiv:2011.12127, Section IV.C.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The normalized BNT block-separation hypotheses imply that the periodic chain
space of a block-diagonal tensor lies in the linear sum of the block local
spaces.

Let
\[
  B=\bigoplus_j\mu_jA_j,\qquad S_M=\bigvee_jG_M(A_j).
\]
Assume the normalized BNT block-separation hypotheses give the one-step
recursion from arXiv:quant-ph/0608197 in the range
\[
  M>L_0+(r-1)(L_0+(L_0+L_0)).
\]
Then, for every \(N\ge L\) in that range,
\[
  \mathcal G_{N,L}(B)\subseteq S_N.
\]
This is the inclusion into \(S_N\) in Theorem 12 of
arXiv:quant-ph/0608197 (proof lines 1430--1456). The step that closes the
boundaries with block-diagonal boundary conditions, replacing \(S_N\) by the sum
of periodic block ground spaces, is separate. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL₀ : 1 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange : L₀ + (r - 1) * (L₀ + (L₀ + L₀)) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, groundSpace (A j) N := by
  classical
  apply chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace
    (μ := μ) (A := A) hμ hN hL hLN
  intro M hM
  have hMpos : 0 < M := lt_of_lt_of_le hL hM
  have hbound : L₀ + (r - 1) * (L₀ + (L₀ + L₀)) ≤ M - 1 := by
    omega
  have hstep :=
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital
      (d := d) (L := L₀) A hIrr hLeft hOverlap hBlocks hBlk hInj hL₀
      hUnital (n := M - 1) hbound
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hMpos)
  rw [← hM1]
  simpa [Nat.add_assoc] using hstep

/-- Finite-length block injectivity gives the periodic-boundary inclusion into the
sum of local block ground spaces.

Let
\[
  B=\bigoplus_j\mu_jA_j,\qquad S_M=\bigvee_jG_M(A_j).
\]
Assume each block is injective at length \(L_0\), the blocks are separated
normalized BNT blocks, and
\[
  M-1\ge (L_0+1)+(r-1)((L_0+1)+((L_0+1)+(L_0+1))).
\]
Then the one-step identity for \(S_M\) from arXiv:quant-ph/0608197 holds.
Consequently, for every \(N\ge L\) in this range,
\[
  \mathcal G_{N,L}(B)\subseteq S_N.
\]
This is the inclusion into the linear span of block local ground spaces used in
Theorem 12 of arXiv:quant-ph/0608197 (proof lines
1430--1456). The replacement of \(S_N\) by periodic block chain spaces is the
separate step of closing the boundaries with block-diagonal boundary
conditions.

The proof uses only the span-based one-step intersection identity
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, which is
independent of the boundary-condition comparison at boundary-crossing windows. The
periodic-boundary upgrade — replacing the open-boundary span \(\bigvee_jG_N(A_j)\)
by \(\sum_j\mathcal G_{N,L}(A_j)\) — is the separate comparison of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex` (issue 2971).

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison at boundary-crossing windows
tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, groundSpace (A j) N := by
  classical
  apply chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace
    (μ := μ) (A := A) hμ hN hL hLN
  intro M hM
  have hMpos : 0 < M := lt_of_lt_of_le hL hM
  have hbound :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤
        M - 1 := by
    omega
  have hstep :=
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1
      (d := d) (L₀ := L₀) A hIrr hLeft hOverlap hBlocks hBlk hL₀
      hUnital (n := M - 1) hbound
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hMpos)
  rw [← hM1]
  simpa [Nat.add_assoc] using hstep

/-- The normalized BNT block-separation hypotheses give the periodic-boundary
inclusion into \(S_N\), and \(S_N\) is a direct sum of local block spaces.

Let
\[
  B=\bigoplus_j\mu_jA_j,\qquad S_N=\bigvee_jG_N(A_j).
\]
At the lengths used in Theorem 12 of arXiv:quant-ph/0608197
(arXiv:quant-ph/0608197, proof lines 1430--1456), one has
\[
  \mathcal G_{N,L}(B)\subseteq S_N,
\]
and the summands \(G_N(A_j)\) form an internal direct sum. This does not assert
the separate step closing the boundaries with block-diagonal boundary
conditions. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL₀ : 1 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange : L₀ + (r - 1) * (L₀ + (L₀ + L₀)) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, groundSpace (A j) N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  refine ⟨?_, ?_⟩
  · exact chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hInj hL₀ hUnital hN hL hLN hRange
  · exact groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital
      A hIrr hLeft hOverlap hBlocks hBlk hInj hL₀ hUnital (by omega)

/-- Finite-length block injectivity gives the open-boundary inclusion into
\(S_N\), and \(S_N\) is an internal direct sum of local block ground spaces.

Here \(S_N=\bigvee_jG_N(A_j)\) is the open-boundary span. The proof uses only the
span-based one-step intersection identity and the block-separation independence,
both independent of the boundary-condition comparison at boundary-crossing
windows. The periodic-boundary upgrade replacing \(S_N\) by
\(\sum_j\mathcal G_{N,L}(A_j)\) is the separate comparison of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex` (issue 2971).

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison at boundary-crossing windows
tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, groundSpace (A j) N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  refine ⟨?_, ?_⟩
  · exact
      chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1
        μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
  · exact groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital (by omega)

/-- Open-boundary block decomposition for vectors satisfying the block-diagonal
periodic constraints.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Assume the blocks are irreducible, left-canonical, normalized in self-overlap,
pairwise not gauge-phase equivalent, unital, and injective at a common positive
length. Then every
\(\psi\in\mathcal G_{N,L}(B)\) has a unique decomposition
\[
  \psi=\sum_j\psi_j,\qquad \psi_j\in G_N(A_j).
\]
This is an open-boundary decomposition. The periodic-boundary upgrade in
arXiv:quant-ph/0608197, Theorem 12, is a separate boundary-condition
comparison: one must prove \(\psi_j\in\mathcal G_{N,L}(A_j)\) for the
block components produced here.

The decomposition uses only the span-based open-boundary inclusion and
block-separation independence, both independent of the boundary-condition
comparison at boundary-crossing windows. That periodic-boundary comparison
(arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456;
arXiv:2011.12127, Section IV.C, lines 2126--2128) is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex` (issue 2971).

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison at boundary-crossing windows
tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem exists_unique_sum_groundSpace_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ φ : (j : Fin r) → NSiteSpace d N,
      (∀ j, φ j ∈ groundSpace (A j) N) ∧
        ψ = ∑ j, φ j ∧
          ∀ φ' : (j : Fin r) → NSiteSpace d N,
            (∀ j, φ' j ∈ groundSpace (A j) N) →
              ψ = ∑ j, φ' j → φ' = φ := by
  classical
  obtain ⟨hLe, hIndep⟩ :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
  obtain ⟨φ, hφ, hφsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun j : Fin r => groundSpace (A j) N) ψ).mp (hLe hψ)
  have hψφ : ψ = ∑ j : Fin r, φ j := by
    simpa [Finsupp.sum_fintype] using hφsum.symm
  refine ⟨φ, hφ, hψφ, ?_⟩
  intro φ' hφ' hψφ'
  apply funext
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hIndep
  intro j
  have hsum : ∑ i, (φ' i - φ i) = 0 := by
    rw [Finset.sum_sub_distrib, ← hψφ', ← hψφ, sub_self]
  have hmem : ∀ i : Fin r, i ∈ Finset.univ → φ' i - φ i ∈ groundSpace (A i) N := by
    intro i _
    exact Submodule.sub_mem _ (hφ' i) (hφ i)
  have hzero := hIndep Finset.univ (fun i => φ' i - φ i) hmem hsum j (Finset.mem_univ j)
  exact sub_eq_zero.mp hzero

/-- Block-diagonal boundary conditions for a vector satisfying the block-diagonal
periodic constraints.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Under the normalized BNT block-separation hypotheses and the \(L_0\)-block
injectivity range bound, every \(\psi\in\mathcal G_{N,L}(B)\) can be
represented by block-diagonal boundary conditions
\[
  \psi=\Gamma_N^B\!\left(\bigoplus_jX_j\right)
\]
and each component vector
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
lies in the open-boundary ground space \(G_N(A_j)\).

The latter membership is the defining open-boundary range property of the
displayed boundary matrix. The substantive assertion is the block-diagonal
representation of \(\psi\). The periodic-boundary upgrade is the separate
boundary-condition comparison for the cyclic windows crossing the chosen cut.

This proves the displayed statement, in which the component membership is the
open-boundary range property \(\Gamma_N^{A_j}(\mu_j^NX_j)\in G_N(A_j)\). The
boundary-condition comparison in arXiv:quant-ph/0608197, proof lines
1454--1456, and arXiv:2011.12127, lines 2126--2128, shows, under the
comparison identities, that these same component
vectors lie in \(\mathcal G_{N,L}(A_j)\).

The block-diagonal boundary representation and the open-boundary component
membership use only the span-based open-boundary inclusion, independently of
the boundary-condition comparison at boundary-crossing windows. The
periodic-boundary upgrade to \(\mathcal G_{N,L}(A_j)\) (arXiv:quant-ph/0608197,
Theorem 12, proof lines 1446--1456; arXiv:2011.12127, Section IV.C, lines
2126--2128) is the separate step recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex` (issue 2971).

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison at boundary-crossing windows
tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ groundSpace (A j) N := by
  classical
  obtain ⟨φ, hφ, hψφ, _huniq⟩ :=
    exists_unique_sum_groundSpace_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  have hφRange : ∀ j : Fin r, φ j ∈ (groundSpaceMap (A j) N).range := by
    intro j
    simpa [groundSpace] using hφ j
  choose Y hY using hφRange
  let X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => ((μ j) ^ N)⁻¹ • Y j
  refine ⟨X, ?_, ?_⟩
  · rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
    calc
      ψ = ∑ j : Fin r, φ j := hψφ
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            have hpow : (μ j) ^ N ≠ 0 := pow_ne_zero N (hμ j)
            simp [X, hY j, hpow]
  · intro j
    have hpow : (μ j) ^ N ≠ 0 := pow_ne_zero N (hμ j)
    simpa [X, hY j, hpow] using hφ j

/-- For normalized BNT blocks, the block-diagonal periodic chain space satisfies
two inclusions.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Under the normalized BNT block-separation hypotheses and in the proved length
range,
\[
  \bigvee_j \mathcal G_{N,L}(A_j)
  \subseteq
  \mathcal G_{N,L}(B)
  \subseteq
  \bigvee_j G_N(A_j),
\]
and the right-hand local block sum is internal. The periodic-boundary comparison
from arXiv:quant-ph/0608197, with block-diagonal boundary conditions,
replaces \(\bigvee_jG_N(A_j)\) by \(\sum_j\mathcal G_{N,L}(A_j)\). -/
theorem chainGroundSpace_toTensorFromBlocks_two_inclusions_and_iSupIndep_of_bnt_unital
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL₀ : 1 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange : L₀ + (r - 1) * (L₀ + (L₀ + L₀)) + 1 ≤ L) :
    (⨆ j : Fin r, chainGroundSpace (A j) L N) ≤
        chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ∧
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, groundSpace (A j) N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  refine ⟨?_, ?_⟩
  · exact iSup_chainGroundSpace_block_le_toTensorFromBlocks μ A hμ hN hLN
  · exact chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hInj hL₀ hUnital hN hL hLN hRange

/-- Finite-length block injectivity gives the two established inclusions for the
block-diagonal periodic chain space.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Under the normalized BNT block-separation hypotheses and the corresponding
finite injectivity range,
\[
  \bigvee_j \mathcal G_{N,L}(A_j)
  \subseteq
  \mathcal G_{N,L}(B)
  \subseteq
  \bigvee_j G_N(A_j),
\]
and the right-hand local block sum is internal. The separate step from
arXiv:quant-ph/0608197 is
to close the boundaries with block-diagonal boundary conditions.

Both displayed inclusions and the internal-direct-sum conclusion use only the
span-based open-boundary results, independently of the boundary-condition
comparison at boundary-crossing windows. The periodic-boundary upgrade
replacing \(\bigvee_jG_N(A_j)\) by \(\sum_j\mathcal G_{N,L}(A_j)\)
(arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456;
arXiv:2011.12127, Section IV.C, lines 2126--2128) is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex` (issue 2971).

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison at boundary-crossing windows
tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem chainGroundSpace_toTensorFromBlocks_two_inclusions_and_iSupIndep_of_bnt_unital_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L) :
    (⨆ j : Fin r, chainGroundSpace (A j) L N) ≤
        chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ∧
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, groundSpace (A j) N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  refine ⟨?_, ?_⟩
  · exact iSup_chainGroundSpace_block_le_toTensorFromBlocks μ A hμ hN hLN
  · exact chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange

/-- Boundary decomposition implies the reverse block-diagonal chain inclusion.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
If every \(\psi\in\mathcal G_{N,L}(B)\) admits a decomposition
\[
  \psi=\sum_j\psi_j,
  \qquad
  \psi_j\in\mathcal G_{N,L}(A_j),
\]
then
\[
  \mathcal G_{N,L}(B)\subseteq\bigvee_j\mathcal G_{N,L}(A_j).
\] -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_of_boundary_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ}
    (hBoundary : ∀ ψ : NSiteSpace d N,
      ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∃ φ : (j : Fin r) → NSiteSpace d N,
          (∀ j, φ j ∈ chainGroundSpace (A j) L N) ∧
            ψ = ∑ j, φ j) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  classical
  intro ψ hψ
  rcases hBoundary ψ hψ with ⟨φ, hφ, rfl⟩
  exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (hφ j)

/-- Cyclic restriction preserves the block-diagonal boundary-condition
decomposition.

Let \(B=\bigoplus_j\mu_jA_j\). For block-diagonal boundary conditions
\(\bigoplus_jX_j\), every cyclic window satisfies
\[
  R_{i,\tau}\!\left(\Gamma_N^B\!\left(\bigoplus_jX_j\right)\right)
    =
  \sum_j R_{i,\tau}\!\left(\Gamma_N^{A_j}(\mu_j^NX_j)\right).
\]
This is the cyclic-window form of the block-diagonal boundary-condition
identity used in Theorem 12 of arXiv:quant-ph/0608197, proof lines
1430--1434. -/
theorem cyclicRestrictₗ_groundSpaceMap_toTensorFromBlocks_blockDiagonal_eq_sum
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (i : Fin N) (τ : Fin N → Fin d)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    cyclicRestrictₗ hN L i τ
        (groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X))) =
      ∑ j : Fin r,
        cyclicRestrictₗ hN L i τ
          (groundSpaceMap (A j) N ((μ j) ^ N • X j)) := by
  classical
  rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  exact map_sum (cyclicRestrictₗ hN L i τ)
    (fun j : Fin r => groundSpaceMap (A j) N ((μ j) ^ N • X j)) Finset.univ

/-- A block-diagonal boundary condition satisfying the periodic local constraints
has its local block sum in the direct sum of the block local spaces.

Let \(B=\bigoplus_j\mu_jA_j\). If
\[
  \psi=\Gamma_N^B\!\left(\bigoplus_jX_j\right)
\]
and \(\psi\in\mathcal G_{N,L}(B)\), then each length-\(L\) local constraint of
\(\psi\) gives
\[
  \sum_j R_{i,\tau}\!\left(\Gamma_N^{A_j}(\mu_j^NX_j)\right)
    \in \bigvee_j G_L(A_j).
\]
This is the direct-sum local constraint obtained before the source's blockwise
extraction step
\[
  A^j_{i_{m+1}}C^j_{i_1}=D^j_{i_{m+1}}A^j_{i_1}
\]
in Theorem 12 of Perez-Garcia, Verstraete, Wolf, and Cirac (2007).
It does not yet identify the individual
summands with vectors in the corresponding \(G_L(A_j)\). -/
theorem blockDiagonal_boundary_cyclicRestrict_sum_mem_iSup_groundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hψX :
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
    (i : Fin N) (τ : Fin N → Fin d) :
    (∑ j : Fin r,
        cyclicRestrictₗ hN L i τ
          (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
      ⨆ j : Fin r, groundSpace (A j) L := by
  classical
  have hLocal :
      cyclicRestrictₗ hN L i τ ψ ∈
        groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L := by
    rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
    let S : Submodule ℂ (NSiteSpace d L) :=
      groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L
    change cyclicRestrictₗ hN L i τ ψ ∈ S
    change ψ ∈
      ⨅ (i : Fin N) (τ : Fin N → Fin d), S.comap (cyclicRestrictₗ hN L i τ) at hψ
    have hAtI :
        ψ ∈ ⨅ τ : Fin N → Fin d, S.comap (cyclicRestrictₗ hN L i τ) :=
      (Submodule.mem_iInf (p := fun i : Fin N =>
        ⨅ τ : Fin N → Fin d, S.comap (cyclicRestrictₗ hN L i τ))).mp hψ i
    exact (Submodule.mem_iInf
      (p := fun τ : Fin N → Fin d => S.comap (cyclicRestrictₗ hN L i τ))).mp hAtI τ
  have hSum :
      (∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
        groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L := by
    rw [← cyclicRestrictₗ_groundSpaceMap_toTensorFromBlocks_blockDiagonal_eq_sum
      μ A hN i τ X]
    rw [← hψX]
    exact hLocal
  simpa [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ L] using hSum

private theorem contiguousRestrictₗ_groundSpaceMap_mem_groundSpace
    {A : MPSTensor d D} {s L N : ℕ} (hsL : s + L ≤ N)
    (τ : Fin N → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    contiguousRestrictₗ s L hsL τ (groundSpaceMap A N X) ∈ groundSpace A L := by
  rw [groundSpace, LinearMap.mem_range]
  let leftWord : List (Fin d) := List.ofFn fun k : Fin s => τ ⟨k.val, by omega⟩
  let rightWord : List (Fin d) := List.ofFn fun k : Fin (N - (s + L)) =>
    τ ⟨s + L + k.val, by omega⟩
  refine ⟨evalWord A rightWord * X * evalWord A leftWord, ?_⟩
  ext σ
  simp only [contiguousRestrictₗ_apply, groundSpaceMap_apply]
  have hlist :
      List.ofFn (contiguousCfg s L σ τ) = leftWord ++ List.ofFn σ ++ rightWord := by
    apply List.ext_getElem
    · simp [leftWord, rightWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by
        simpa [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkLeft : k < s
      · have hkNotWin : ¬(s ≤ k ∧ k < s + L) := by omega
        rw [contiguousCfg, dif_neg hkNotWin]
        rw [List.getElem_append_left]
        · rw [List.getElem_append_left]
          · have hkLeftWord : k < leftWord.length := by
              simpa only [leftWord, List.length_ofFn] using hkLeft
            rw [show leftWord[k]'hkLeftWord = τ ⟨k, by omega⟩ from by
              simp only [leftWord, List.getElem_ofFn]]
          · simpa only [leftWord, List.length_ofFn] using hkLeft
        · simpa only [leftWord, List.length_append, List.length_ofFn] using
            (show k < s + L by omega)
      · by_cases hkWin : k < s + L
        · have hwin : s ≤ k ∧ k < s + L := by omega
          rw [contiguousCfg, dif_pos hwin]
          rw [List.getElem_append_left]
          · rw [List.getElem_append_right]
            · rw [List.getElem_ofFn]
              congr 1
              ext
              simp [leftWord]
            · simpa only [leftWord, List.length_ofFn] using
                (show s ≤ k by omega)
          · simpa only [leftWord, List.length_append, List.length_ofFn] using hkWin
        · have hkRight : s + L ≤ k := by omega
          have hkNotWin : ¬(s ≤ k ∧ k < s + L) := by omega
          rw [contiguousCfg, dif_neg hkNotWin]
          rw [List.getElem_append_right]
          · have hRightIndex :
                k - (leftWord ++ List.ofFn σ).length < rightWord.length := by
              simp only [rightWord, leftWord, List.length_append, List.length_ofFn]
              omega
            rw [show rightWord[k - (leftWord ++ List.ofFn σ).length]'hRightIndex =
                τ ⟨k, by omega⟩ from by
              simp only [rightWord, List.getElem_ofFn]
              congr 1
              ext
              simp only [leftWord, List.length_append, List.length_ofFn]
              omega]
          · simpa only [leftWord, List.length_append, List.length_ofFn] using
              (show s + L ≤ k by omega)
  rw [hlist, evalWord_append, evalWord_append]
  calc
    Matrix.trace (evalWord A (List.ofFn σ) *
        (evalWord A rightWord * X * evalWord A leftWord))
        = Matrix.trace ((evalWord A (List.ofFn σ) * (evalWord A rightWord * X)) *
            evalWord A leftWord) := by
          rw [← Matrix.mul_assoc (evalWord A (List.ofFn σ)) (evalWord A rightWord * X)
            (evalWord A leftWord)]
    _ = Matrix.trace (evalWord A leftWord *
        (evalWord A (List.ofFn σ) * (evalWord A rightWord * X))) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((evalWord A leftWord * evalWord A (List.ofFn σ) *
        evalWord A rightWord) * X) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-- Cyclic windows not crossing the chosen cut already satisfy the block local
constraint.

For a block \(A_j\) and boundary matrix \(X_j\), if the cyclic window beginning
at \(i\) stays inside the linear interval \(\{0,\ldots,N-1\}\), then
\[
  R_{i,\tau}\!\left(\Gamma_N^{A_j}(\mu_j^NX_j)\right)\in G_L(A_j).
\]
The boundary matrix remains outside the window, so the restricted vector is
\[
  \Gamma_L^{A_j}(A_{\mathrm{right}}\mu_j^NX_jA_{\mathrm{left}}).
\]
If the cyclic window crosses the chosen cut, the boundary matrix lies between
the two pieces of the window after trace rotation.  The block-diagonal
periodic-boundary input is the matrix identity
\[
  A^j_{i_{m+1}}C^j_{i_1}=D^j_{i_{m+1}}A^j_{i_1}
\]
from Theorem 12 of Perez-Garcia, Verstraete, Wolf, and Cirac (2007). -/
theorem blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_nonwrapping
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (j : Fin r) (i : Fin N) (τ : Fin N → Fin d)
    (hi : i.val + L ≤ N) :
    cyclicRestrictₗ hN L i τ
        (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
      groundSpace (A j) L := by
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ hN hLN hi]
  exact contiguousRestrictₗ_groundSpaceMap_mem_groundSpace (A := A j) (s := i.val)
    (L := L) (N := N) (by omega) τ ((μ j) ^ N • X j)

/-- Componentwise periodicity is reduced to the cyclic windows crossing the
chosen cut.

Let \(B=\bigoplus_j\mu_jA_j\), and fix block-diagonal boundary conditions
\(X_j\). For a block component
\[
  \Gamma_N^{A_j}(\mu_j^NX_j),
\]
membership in \(\mathcal G_{N,L}(A_j)\) means that every cyclic
length-\(L\) window lies in \(G_L(A_j)\). If a window beginning at \(i\)
satisfies \(i+L\le N\), this is already the preceding non-crossing-window
case.
Thus it remains only to prove the same membership for the windows satisfying
\[
  N<i+L.
\]

In the notation of arXiv:quant-ph/0608197, Theorem 12, these are the
boundary-crossing windows controlled by the comparison
\[
  A^j_{i_{m+1}}C^j_{i_1}=D^j_{i_{m+1}}A^j_{i_1}.
\]
This theorem records the reduction; it assumes the crossing-window membership
rather than proving the displayed comparison. -/
theorem blockDiagonal_boundary_component_chainGroundSpace_of_crossing_windows
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCrossing : ∀ (j : Fin r) (i : Fin N) (τ : Fin N → Fin d),
      N < i.val + L →
        cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
          groundSpace (A j) L) :
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  intro j
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  by_cases hi : i.val + L ≤ N
  · exact blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_nonwrapping
      μ A hN hLN X j i τ hi
  · exact hCrossing j i τ (Nat.lt_of_not_ge hi)

/-- A block-diagonal boundary representation whose component vectors satisfy the
periodic block constraints lies in the blockwise periodic chain sum.

Let \(B=\bigoplus_j\mu_jA_j\). If a boundary condition for \(B\) is block
diagonal, say \(X=\bigoplus_jX_j\), and every component
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
belongs to \(\mathcal G_{N,L}(A_j)\), then
\[
  \Gamma_N^B(X)\in\bigvee_j\mathcal G_{N,L}(A_j).
\]
This is the block-diagonal boundary-condition reduction preceding the step of
inverting and re-growing tensors described in arXiv:2011.12127, lines
2126--2128; this theorem assumes the periodic constraint for each block rather
than deriving it. -/
theorem groundSpaceMap_toTensorFromBlocks_blockDiagonal_mem_iSup_chainGroundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ}
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hX : ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N) :
    groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∈
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  classical
  rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (hX j)

/-- Block-diagonal boundary conditions plus periodic constraints for each block
give the reverse inclusion for the block-diagonal periodic chain.

Let \(B=\bigoplus_j\mu_jA_j\). Suppose every
\(\psi\in\mathcal G_{N,L}(B)\) has a block-diagonal boundary representation
\[
  \psi=\Gamma_N^B\!\left(\bigoplus_jX_j\right)
\]
whose \(j\)-th single-block vector
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
lies in \(\mathcal G_{N,L}(A_j)\). Then
\[
  \mathcal G_{N,L}(B)\subseteq\bigvee_j\mathcal G_{N,L}(A_j).
\]
The source periodic-boundary comparison is to prove the displayed periodic
constraint for each block from the block-diagonal boundary conditions. In
Theorem 12 of arXiv:quant-ph/0608197, this is the comparison
\[
  A^j_{i_{m+1}}C^j_{i_1}=D^j_{i_{m+1}}A^j_{i_1}.
\]
The review arXiv:2011.12127 describes the same step as closing the boundaries
after inverting and re-growing tensors with block-diagonal boundary conditions
(arXiv:2011.12127, lines 2126--2128). -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_of_blockDiagonal_boundary_groundSpaceMap
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ}
    (hBoundary : ∀ ψ : NSiteSpace d N,
      ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
          ∀ j : Fin r,
            groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  intro ψ hψ
  rcases hBoundary ψ hψ with ⟨X, hψX, hX⟩
  rw [hψX]
  exact groundSpaceMap_toTensorFromBlocks_blockDiagonal_mem_iSup_chainGroundSpace μ A X hX

/-- Block-diagonal boundary representation gives the periodic block-chain equality in
the finite injectivity range.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Assume the normalized BNT block-separation hypotheses and the finite injectivity
range. Suppose that every vector in \(\mathcal G_{N,L}(B)\) has a
block-diagonal boundary representation
\[
  \psi=\Gamma_N^B\!\left(\bigoplus_jX_j\right)
\]
whose \(j\)-th single-block vector
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
belongs to \(\mathcal G_{N,L}(A_j)\). Then
\[
  \mathcal G_{N,L}(B)=\bigvee_j\mathcal G_{N,L}(A_j),
\]
and the sum \(\bigvee_jG_N(A_j)\) is internal.

The source periodic-boundary step is to obtain the displayed block-diagonal
boundary representation and the periodic constraints for each block from the
inverting-and-re-growing argument in Perez-Garcia, Verstraete, Wolf, and Cirac
(arXiv:quant-ph/0608197) and Cirac, Perez-Garcia, Schuch, and Verstraete
(arXiv:2011.12127), with block-diagonal boundary conditions.

**Scope restriction (periodic-boundary comparison):** The block-diagonal boundary
representation whose block components already satisfy the periodic constraints
\(\Gamma_N^{A_j}(\mu_j^NX_j)\in\mathcal G_{N,L}(A_j)\) is the explicit hypothesis
`hBoundary` here. The span-based open-boundary version of this representation is
proved (its components lie in \(G_N(A_j)\)); the periodic-boundary upgrade is the
boundary-condition comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines
1446--1456, and arXiv:2011.12127, Section IV.C, lines 2126--2128, not yet derived
from the periodic ground-space constraint. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`; tracked in issue 2971.

**Unfaithful:** This proof transitively relies on
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`, whose
normalized BNT product-span input is not yet source-faithful: its derivation uses
the normal-range reduction of arXiv:2011.12127, Section IV.C, lines 2078--2079,
documented in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. This deviation
is independent of the periodic-boundary comparison tracked in issue 2971.
Elimination: derive the normalized BNT product-span input
`wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` from the source periodic-boundary
coordinate comparison of arXiv:2011.12127, Section IV.C, lines 2078--2079
(per `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`), discharging the
`pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1`
dependency; tracked in issue 2405. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hBoundary : ∀ ψ : NSiteSpace d N,
      ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
          ∀ j : Fin r,
            groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  have hClose :
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) L N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_of_blockDiagonal_boundary_groundSpaceMap
      μ A hBoundary
  refine ⟨?_, ?_⟩
  · exact
      chainGroundSpace_toTensorFromBlocks_eq_iSup_chainGroundSpace_of_boundary_closing
        μ A hμ hN hLN hClose
  · exact
      (chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1
        μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange).2

end MPSTensor
