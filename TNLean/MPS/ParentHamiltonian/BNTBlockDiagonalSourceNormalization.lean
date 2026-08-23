/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain

/-!
# Source-normalized block-diagonal chain consequences

This file collects the source-shaped PGVWC07 chain consequences obtained from
positive dual fixed points together with the source unital normalization.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d : ℕ}

/-- Under the PGVWC07 source normalization, every block-diagonal periodic vector
belongs to the sum of the open-boundary block spaces at the sharp source length.
The positive dual fixed points are used only by the tuple-span/intersection layer;
all long-word propagation remains in the source unital gauge.

Source: arXiv:quant-ph/0608197, canonical normalization lines 742--763 and
Theorem 12 proof lines 1346--1456 in
`Papers/quant-ph_0608197/MPSarchive.tex`. -/
theorem
    chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r) (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, Matrix.PosDef (Λ j))
    (hDualFixed : ∀ j,
      Kraus.transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    (hBlk : ∀ k : Fin r, Kraus.IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, groundSpace (A j) N := by
  classical
  apply chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace
    (μ := μ) (A := A) hμ hN hL hLN
  intro M hM
  have hMpos : 0 < M := lt_of_lt_of_le hL hM
  have hbound :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) ≤ M - 1 := by
    omega
  have hstep :=
    pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
      (d := d) (L₀ := L₀) A hr hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀
      hUnital (n := M - 1) hbound
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hMpos)
  rw [← hM1]
  simpa [Nat.add_assoc] using hstep

/-- Under the source-shaped PGVWC07 hypotheses, the chain-ground-space
containment is accompanied by independence of the open-boundary block spaces.

Source: arXiv:quant-ph/0608197, Theorem 12 direct-sum proof lines 1346--1421
and canonical normalization lines 742--763 in
`Papers/quant-ph_0608197/MPSarchive.tex`. -/
theorem
chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r) (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, Matrix.PosDef (Λ j))
    (hDualFixed : ∀ j,
      Kraus.transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    (hBlk : ∀ k : Fin r, Kraus.IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, groundSpace (A j) N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  refine ⟨?_, ?_⟩
  · exact
      chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
        μ A hr hμ hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀ hUnital
          hN hL hLN hRange
  · exact
      groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
        A hr hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀ hUnital (by omega)

/-- Every source-shaped PGVWC07 block-diagonal chain vector has a unique sum
decomposition into the open-boundary spaces of the blocks.

Source: arXiv:quant-ph/0608197, Theorem 12 direct-sum proof lines 1346--1421
and canonical normalization lines 742--763 in
`Papers/quant-ph_0608197/MPSarchive.tex`. -/
theorem
    exists_unique_sum_groundSpace_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r) (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, Matrix.PosDef (Λ j))
    (hDualFixed : ∀ j,
      Kraus.transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    (hBlk : ∀ k : Fin r, Kraus.IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ φ : (j : Fin r) → NSiteSpace d N,
      (∀ j, φ j ∈ groundSpace (A j) N) ∧
        ψ = ∑ j, φ j ∧
          ∀ φ' : (j : Fin r) → NSiteSpace d N,
            (∀ j, φ' j ∈ groundSpace (A j) N) →
              ψ = ∑ j, φ' j → φ' = φ := by
  classical
  obtain ⟨hLe, hIndep⟩ := (
chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1_pgvwc07_of_dualFixedPoint
      μ A hr hμ hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀ hUnital
        hN hL hLN hRange)
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

/-- Under the source-shaped PGVWC07 hypotheses, a periodic vector of the block
sum admits one block-diagonal open-boundary matrix. Its block components belong
to the corresponding open-boundary block spaces.

Source: arXiv:quant-ph/0608197, canonical normalization lines 742--763 and
Theorem 12 proof lines 1424--1456 in
`Papers/quant-ph_0608197/MPSarchive.tex`. -/
theorem
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1_pgvwc07_of_dualFixedPoint
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r) (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (Λ : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hΛ : ∀ j, Matrix.PosDef (Λ j))
    (hDualFixed : ∀ j,
      Kraus.transferMap (d := d) (D := dim j) (fun a => (A j a)ᴴ) (Λ j) = Λ j)
    (hBlk : ∀ k : Fin r, Kraus.IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ groundSpace (A j) N := by
  have hOpen : ψ ∈ ⨆ j : Fin r, groundSpace (A j) N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
      μ A hr hμ hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀ hUnital
        hN hL hLN hRange hψ
  exact BlockSumGroundSpace.exists_blockDiagonal_boundary_of_mem_iSup_groundSpace
    μ A hμ hOpen

end MPSTensor
