/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalChainGroundSpace
import TNLean.MPS.ParentHamiltonian.BNTBlockIntersection

/-!
# Block-diagonal propagation for parent-Hamiltonian local spaces

This file combines the normalized BNT block-separation hypotheses with the
PGVWC07 one-step identity
\[
  \mathbb C^d\otimes S_M\cap S_M\otimes\mathbb C^d=S_{M+1},
  \qquad S_M=\bigvee_jG_M(A_j),
\]
as used in PGVWC07, Theorem 2blocks.2.
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
Assume the normalized BNT block-separation hypotheses give the PGVWC one-step
recursion in the range
\[
  M>L_0+(r-1)(L_0+(L_0+L_0)).
\]
Then, for every \(N\ge L\) in that range,
\[
  \mathcal G_{N,L}(B)\subseteq S_N.
\]
This is the inclusion into \(S_N\) in PGVWC07, Theorem 2blocks.2
(arXiv:quant-ph/0608197, proof lines 1430--1456). The step that closes the
boundaries with block-diagonal boundary conditions, replacing \(S_N\) by the
sum of periodic block ground spaces, is separate. -/
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

/-- Condition C1 gives the periodic-chain inclusion into the sum of local block
ground spaces.

Let
\[
  B=\bigoplus_j\mu_jA_j,\qquad S_M=\bigvee_jG_M(A_j).
\]
Assume each block satisfies PGVWC07 Condition C1 at length \(L_0\), the blocks
are separated normalized BNT blocks, and
\[
  M-1\ge (L_0+1)+(r-1)((L_0+1)+((L_0+1)+(L_0+1))).
\]
Then the PGVWC one-step identity for \(S_M\) holds. Consequently, for every
\(N\ge L\) in this range,
\[
  \mathcal G_{N,L}(B)\subseteq S_N.
\]
This is the inclusion into the linear span of block local ground spaces used in
PGVWC07, Theorem 2blocks.2 (arXiv:quant-ph/0608197, proof lines
1430--1456). The replacement of \(S_N\) by periodic block chain spaces is the
separate step of closing the boundaries with block-diagonal boundary
conditions. -/
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

/-- The normalized BNT block-separation hypotheses give the periodic-chain
inclusion into \(S_N\), and \(S_N\) is a direct sum of local block spaces.

Let
\[
  B=\bigoplus_j\mu_jA_j,\qquad S_N=\bigvee_jG_N(A_j).
\]
At the lengths used in PGVWC07, Theorem 2blocks.2
(arXiv:quant-ph/0608197, proof lines 1430--1456), one has
\[
  \mathcal G_{N,L}(B)\subseteq S_N,
\]
and the summands \(G_N(A_j)\) form an internal direct sum. This does not assert
the later step closing the boundaries with block-diagonal boundary conditions. -/
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

/-- Condition C1 gives the periodic-chain inclusion into \(S_N\), and \(S_N\)
is an internal direct sum of local block ground spaces. -/
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
This is still an open-boundary decomposition. The remaining PGVWC07 boundary
step is to prove \(\psi_j\in\mathcal G_{N,L}(A_j)\). -/
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
  obtain ⟨φ, hφ, hψφ⟩ :=
    exists_sum_mem_of_mem_iSup_fin (fun j : Fin r => groundSpace (A j) N) (hLe hψ)
  refine ⟨φ, hφ, hψφ, ?_⟩
  intro φ' hφ' hψφ'
  apply funext
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero] at hIndep
  intro j
  have hsum : ∑ i, (φ' i - φ i) = 0 := by
    rw [Finset.sum_sub_distrib, ← hψφ', ← hψφ, sub_self]
  have hmem : ∀ i : Fin r, i ∈ Finset.univ → φ' i - φ i ∈ groundSpace (A i) N := by
    intro i _
    exact Submodule.sub_mem _ (hφ' i) (hφ i)
  have hzero := hIndep Finset.univ (fun i => φ' i - φ i) hmem hsum j (Finset.mem_univ j)
  exact sub_eq_zero.mp hzero

/-- The current normalized BNT formalization gives two inclusions for the
block-diagonal periodic chain space.

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
and the right-hand local block sum is internal. The remaining PGVWC07
boundary-closing step with block-diagonal boundary conditions replaces
\(\bigvee_jG_N(A_j)\) by \(\sum_j\mathcal G_{N,L}(A_j)\). -/
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

/-- Condition C1 gives the two established inclusions for the block-diagonal
periodic chain space.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Under the normalized BNT block-separation hypotheses and the finite Condition
C1 range,
\[
  \bigvee_j \mathcal G_{N,L}(A_j)
  \subseteq
  \mathcal G_{N,L}(B)
  \subseteq
  \bigvee_j G_N(A_j),
\]
and the right-hand local block sum is internal. The remaining PGVWC07 step is
to close the boundaries with block-diagonal boundary conditions. -/
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

/-- Conditional block-diagonal chain equality in the finite injectivity range.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Under the normalized BNT block-separation hypotheses and the finite injectivity
range, suppose that every vector in \(\mathcal G_{N,L}(B)\) can be written
\[
  \psi=\sum_j\psi_j,
  \qquad
  \psi_j\in\mathcal G_{N,L}(A_j).
\]
Then
\[
  \mathcal G_{N,L}(B)=\bigvee_j\mathcal G_{N,L}(A_j),
\]
and the sum \(\bigvee_jG_N(A_j)\) is internal. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_boundary_decomposition
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
        ∃ φ : (j : Fin r) → NSiteSpace d N,
          (∀ j, φ j ∈ chainGroundSpace (A j) L N) ∧
            ψ = ∑ j, φ j) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  have hClose :
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) L N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_of_boundary_decomposition μ A hBoundary
  refine ⟨?_, ?_⟩
  · exact
      chainGroundSpace_toTensorFromBlocks_eq_iSup_chainGroundSpace_of_boundary_closing
        μ A hμ hN hLN hClose
  · exact
      (chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1
        μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange).2

end MPSTensor
