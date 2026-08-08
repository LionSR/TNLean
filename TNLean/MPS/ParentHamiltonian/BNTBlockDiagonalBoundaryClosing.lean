/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossing
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixBlock
import TNLean.MPS.ParentHamiltonian.CyclicTranslation
import TNLean.MPS.ParentHamiltonian.GroundSpaceSpanning
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Boundary closing by comparison across a cyclic cut

This file formalizes the change-of-cut comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1454--1456.  Two open-boundary
decompositions of the same periodic state, with cuts separated by \(S\) sites,
are compared against the common complementary words of length \(K\). A
simultaneous spanning family on the complementary segment then identifies the
boundary matrices block by block.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- A length at which a tensor is block injective identifies the two boundary
matrices in a word intertwiner and promotes the relation to one-site
commutation. This is the boundary-identification step in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1454--1456. -/
theorem boundary_eq_and_commutes_of_isNBlkInjective_of_intertwines
    {D S : ℕ} {A : MPSTensor d D}
    (hBlk : IsNBlkInjective A S) (hS : 0 < S)
    (X Y : Matrix (Fin D) (Fin D) ℂ)
    (hIntertwine : ∀ α : Fin S → Fin d,
      X * evalWord A (List.ofFn α) = evalWord A (List.ofFn α) * Y) :
    X = Y ∧ ∀ a : Fin d, X * A a = A a * X := by
  have hMaps : LinearMap.mulLeft ℂ X = LinearMap.mulRight ℂ Y := by
    apply LinearMap.ext_on_range
      (v := fun α : Fin S → Fin d ↦ evalWord A (List.ofFn α))
    · simpa [wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A S).mpr hBlk
    · intro α
      simpa only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
        hIntertwine α
  have hXY := congrArg (fun f ↦ f 1) hMaps
  simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_one, one_mul] at hXY
  refine ⟨hXY, ?_⟩
  apply boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes
    hBlk hS (le_refl S)
  intro α
  rw [hIntertwine α, hXY]

/-- Comparing open-boundary decompositions before and after moving the cut
gives a blockwise boundary intertwiner.

Suppose translating the cut of

\[
  \sum_j \Gamma_{K+S}^{A_j}(X_j)
\]

by \(K\) sites gives

\[
  \sum_j \Gamma_{K+S}^{A_j}(Y_j).
\]

If the simultaneous block words of length \(K\) span the product matrix
algebra, then every word \(A^j_\alpha\) of length \(S\) satisfies

\[
  X_j A^j_\alpha=A^j_\alpha Y_j.
\]

This is the global-cut form of the boundary comparison used in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1454--1456, following the
single-block change-of-cut argument in proof lines 1276--1289. -/
theorem block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {K S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A K)
    (X Y : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hEq :
      cyclicTranslateState (⟨K, by omega⟩ : Fin (K + S))
          (∑ j : Fin r, groundSpaceMap (A j) (K + S) (X j)) =
        ∑ j : Fin r, groundSpaceMap (A j) (K + S) (Y j)) :
    ∀ (α : Fin S → Fin d) (j : Fin r),
      X j * evalWord (A j) (List.ofFn α) =
        evalWord (A j) (List.ofFn α) * Y j := by
  classical
  intro α
  apply block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun j ↦ X j * evalWord (A j) (List.ofFn α))
    (fun j ↦ evalWord (A j) (List.ofFn α) * Y j)
  intro β
  have hcoeff := congrFun hEq (Fin.append β α)
  change
    (∑ j : Fin r, groundSpaceMap (A j) (K + S) (X j))
        (cyclicTranslateCfg (⟨K, by omega⟩ : Fin (K + S)) (Fin.append β α)) =
      (∑ j : Fin r, groundSpaceMap (A j) (K + S) (Y j)) (Fin.append β α)
    at hcoeff
  simp only [Finset.sum_apply, groundSpaceMap_apply] at hcoeff
  rw [cyclicTranslateCfg_fin_append hS β α] at hcoeff
  have hswap :
      List.ofFn ((Fin.append α β) ∘ Fin.cast (Nat.add_comm K S)) =
        List.ofFn α ++ List.ofFn β := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (Nat.add_comm S K) (Fin.append α β)).symm
  rw [hswap, List.ofFn_fin_append] at hcoeff
  simp_rw [evalWord_append] at hcoeff
  calc
    (∑ j : Fin r,
        Matrix.trace
          ((X j * evalWord (A j) (List.ofFn α)) *
            evalWord (A j) (List.ofFn β))) =
        ∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn α) *
                evalWord (A j) (List.ofFn β)) * X j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_assoc]
      exact Matrix.trace_mul_comm _ _
    _ =
        ∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) *
                evalWord (A j) (List.ofFn α)) * Y j) := hcoeff
    _ =
        ∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn α) * Y j) *
              evalWord (A j) (List.ofFn β)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_assoc]
      exact Matrix.trace_mul_comm _ _

/-- Length-indexed form of the global-cut comparison, with the chain length
kept as a separate variable. This is the change-of-cut comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1454--1456. -/
theorem block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq_of_add_eq
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {N K S : ℕ} (hKS : K + S = N) (hS : 0 < S)
    (hSpan : WordTupleSpanTop A K)
    (X Y : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hEq :
      cyclicTranslateState (⟨K, by omega⟩ : Fin N)
          (∑ j : Fin r, groundSpaceMap (A j) N (X j)) =
        ∑ j : Fin r, groundSpaceMap (A j) N (Y j)) :
    ∀ (α : Fin S → Fin d) (j : Fin r),
      X j * evalWord (A j) (List.ofFn α) =
        evalWord (A j) (List.ofFn α) * Y j := by
  subst N
  exact block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq
    A hS hSpan X Y hEq

/-- A global comparison of two cuts closes the block-diagonal boundary
conditions without any short-tail simultaneous spanning hypothesis.

Let \(B=\bigoplus_j\mu_jA_j\). Under the normalized BNT block-separation
hypotheses, suppose \(N\ge L+L_0\), where every block is injective at length
\(L_0>0\). Every vector in the periodic chain space of \(B\) has block-diagonal
open-boundary matrices \(X_j\). Move the cut past the final \(L_0\) sites and
apply the same open-boundary decomposition to the translated state. Comparing
the two decompositions against the complementary words of length \(N-L_0\)
gives

\[
  (\mu_j^N X_j)A^j_\alpha=A^j_\alpha(\mu_j^N Y_j).
\]

The simultaneous spanning hypothesis is used only at the long length
\(N-L_0\), where it follows from the BNT separation bound. Block injectivity at
length \(L_0\) then identifies the two boundary matrices and gives commutation,
which closes every boundary-crossing local interval. This is the change-of-cut
argument of arXiv:quant-ph/0608197, Theorem 12, proof lines 1276--1289 and
1454--1456, with the block-diagonal boundary restriction of arXiv:2011.12127,
Section IV.C, lines 2126--2128.

This earlier variant is retained with the sufficient range
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The theorem
`exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1_pgvwc07`
below proves the same conclusion at the source bound
\(3(r-1)(L_0+1)+1\le L\).
-/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1
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
    (hNlarge : L + L₀ ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  obtain ⟨X, hψX, _⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  let s : Fin N := ⟨N - L₀, by omega⟩
  have hTranslate :
      cyclicTranslateState s ψ ∈
        chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N :=
    cyclicTranslateState_mem_chainGroundSpace
      (toTensorFromBlocks (d := d) (μ := μ) A) hN hLN s hψ
  obtain ⟨Y, hψY, _⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hTranslate
  have hXsum :
      ψ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
    calc
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
            (Matrix.blockDiagonal' X)) := hψX
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hYsum :
      cyclicTranslateState s ψ =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    calc
      cyclicTranslateState s ψ =
          groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
              (Matrix.blockDiagonal' Y)) := hψY
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hSplit : N - L₀ + L₀ = N := by omega
  have hSumTranslate :
      cyclicTranslateState s
          (∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j)) =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    rw [← hXsum]
    exact hYsum
  have hLongSpan : WordTupleSpanTop A (N - L₀) := by
    apply wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital
    omega
  have hIntertwine :
      ∀ (α : Fin L₀ → Fin d) (j : Fin r),
        ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn α) =
          evalWord (A j) (List.ofFn α) * ((μ j) ^ N • Y j) := by
    apply block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq_of_add_eq
      A hSplit hL₀ hLongSpan
        (fun j ↦ (μ j) ^ N • X j) (fun j ↦ (μ j) ^ N • Y j)
    simpa only [s] using hSumTranslate
  have hComm : ∀ j : Fin r, ∀ a : Fin d,
      ((μ j) ^ N • X j) * A j a = A j a * ((μ j) ^ N • X j) := by
    intro j
    exact (boundary_eq_and_commutes_of_isNBlkInjective_of_intertwines
      (hBlk j) hL₀ ((μ j) ^ N • X j) ((μ j) ^ N • Y j)
      (fun α ↦ hIntertwine α j)).2
  have hCommWord : ∀ j : Fin r, ∀ w : List (Fin d),
      ((μ j) ^ N • X j) * evalWord (A j) w =
        evalWord (A j) w * ((μ j) ^ N • X j) := by
    intro j w
    induction w with
    | nil => simp [evalWord_nil]
    | cons a w ih =>
        rw [evalWord_cons, ← Matrix.mul_assoc, hComm j a, Matrix.mul_assoc, ih,
          ← Matrix.mul_assoc]
  refine ⟨X, hψX, ?_⟩
  apply blockDiagonal_boundary_component_chainGroundSpace_of_boundary_identities
    μ A hN hLN X
  intro j i _τ _hi
  refine ⟨(μ j) ^ N • X j, ?_⟩
  intro β
  exact hCommWord j (List.ofFn β)

/-- A global change of cut closes the block-diagonal boundary conditions in
the sharp PGVWC07 source range.

Let \(r\ge2\), let every block be injective at length \(L_0>0\), and assume
\(L\ge3(r-1)(L_0+1)+1\) and \(N\ge L+L_0\). The source-range simultaneous span
on the complementary segment \(N-L_0\) identifies the boundary matrices before
and after moving the cut. Each block component therefore satisfies every
periodic local constraint. This is arXiv:quant-ph/0608197, Theorem 12, proof
lines 1424--1456. -/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hr : 2 ≤ r) (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d]
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  have hN : 0 < N := by omega
  have hL : 0 < L := by omega
  have hLN : L ≤ N := by omega
  obtain ⟨X, hψX, _⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1_pgvwc07
      μ A hr hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  let s : Fin N := ⟨N - L₀, by omega⟩
  have hTranslate :
      cyclicTranslateState s ψ ∈
        chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N :=
    cyclicTranslateState_mem_chainGroundSpace
      (toTensorFromBlocks (d := d) (μ := μ) A) hN hLN s hψ
  obtain ⟨Y, hψY, _⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1_pgvwc07
      μ A hr hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hTranslate
  have hXsum :
      ψ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
    calc
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
            (Matrix.blockDiagonal' X)) := hψX
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hYsum :
      cyclicTranslateState s ψ =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    calc
      cyclicTranslateState s ψ =
          groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
              (Matrix.blockDiagonal' Y)) := hψY
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hSplit : N - L₀ + L₀ = N := by omega
  have hSumTranslate :
      cyclicTranslateState s
          (∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j)) =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    rw [← hXsum]
    exact hYsum
  have hLongSpan : WordTupleSpanTop A (N - L₀) := by
    apply wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07
      A hr hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital
    omega
  have hIntertwine :
      ∀ (α : Fin L₀ → Fin d) (j : Fin r),
        ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn α) =
          evalWord (A j) (List.ofFn α) * ((μ j) ^ N • Y j) := by
    apply block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq_of_add_eq
      A hSplit hL₀ hLongSpan
        (fun j ↦ (μ j) ^ N • X j) (fun j ↦ (μ j) ^ N • Y j)
    simpa only [s] using hSumTranslate
  have hComm : ∀ j : Fin r, ∀ a : Fin d,
      ((μ j) ^ N • X j) * A j a = A j a * ((μ j) ^ N • X j) := by
    intro j
    exact (boundary_eq_and_commutes_of_isNBlkInjective_of_intertwines
      (hBlk j) hL₀ ((μ j) ^ N • X j) ((μ j) ^ N • Y j)
      (fun α ↦ hIntertwine α j)).2
  have hCommWord : ∀ j : Fin r, ∀ w : List (Fin d),
      ((μ j) ^ N • X j) * evalWord (A j) w =
        evalWord (A j) w * ((μ j) ^ N • X j) := by
    intro j w
    induction w with
    | nil => simp [evalWord_nil]
    | cons a w ih =>
        rw [evalWord_cons, ← Matrix.mul_assoc, hComm j a, Matrix.mul_assoc, ih,
          ← Matrix.mul_assoc]
  refine ⟨X, hψX, ?_⟩
  apply blockDiagonal_boundary_component_chainGroundSpace_of_boundary_identities
    μ A hN hLN X
  intro j i _τ _hi
  refine ⟨(μ j) ^ N • X j, ?_⟩
  intro β
  exact hCommWord j (List.ofFn β)

/-- At the length bound of Perez-Garcia, Verstraete, Wolf, and Cirac, the
periodic chain space of a normalized BNT block sum is the sum of the periodic
chain spaces of its blocks, while the open-boundary block spaces are independent.

This is arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456. The required
interaction length is
\[
  3(r-1)(L_0+1)+1 \leq L,
\]
and the chain length satisfies \(L+L_0\leq N\). -/
theorem
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d]
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r ↦ groundSpace (A j) N) := by
  have hN : 0 < N := by omega
  have hL : 0 < L := by omega
  have hLN : L ≤ N := by omega
  have hClose :
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) L N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_of_blockDiagonal_boundary_groundSpaceMap
      μ A (fun ψ hψ ↦
        exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1_pgvwc07
          μ A hr hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hRange hNlarge hψ)
  refine ⟨?_, ?_⟩
  · exact
      chainGroundSpace_toTensorFromBlocks_eq_iSup_chainGroundSpace_of_boundary_closing
        μ A hμ hN hLN hClose
  · exact
      groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07
        A hr hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital (by omega)

/-- At the source length bound, the normalized BNT block-diagonal periodic
chain space is the sum of the periodic chain spaces of its blocks.

This is the equality in arXiv:quant-ph/0608197, Theorem 12, proof lines
1424--1456. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d]
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  exact
    (chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1_pgvwc07
      μ A hμ hr hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hRange hNlarge).1

/-- At the source length bound, blockwise periodic uniqueness gives containment
of the block-diagonal parent-Hamiltonian kernel in the span of the BNT matrix
product vectors.

This is the final conditional step in arXiv:quant-ph/0608197, Theorem 12, proof
lines 1424--1456. -/
theorem ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d]
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N)
    (hBlock : ∀ j : Fin r,
      chainGroundSpace (A j) L N ≤ mpvSubmodule (A j) N) :
    LinearMap.ker (parentHamiltonian
      (toTensorFromBlocks (d := d) (μ := μ) A) L N) ≤
      bntMPSVectorSpan A N := by
  have hN : 0 < N := by omega
  have hLN : L ≤ N := by omega
  refine ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan
    μ A hN hLN ?_ hBlock
  exact le_of_eq
    (chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1_pgvwc07
      μ A hμ hr hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hRange hNlarge)

/-- At the PGVWC07 source range, the parent-Hamiltonian kernel of the normalized
BNT block direct sum is exactly the span of the periodic component vectors.

This packages the final equality in arXiv:quant-ph/0608197, Theorem 12, proof
lines 1424--1456. -/
theorem ker_parentHamiltonian_toTensorFromBlocks_eq_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L₀ L N : ℕ}
    (hr : 2 ≤ r)
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d]
    (hRange :
      (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N) :
    LinearMap.ker (parentHamiltonian
      (toTensorFromBlocks (d := d) (μ := μ) A) L N) =
      bntMPSVectorSpan A N := by
  have hL : L₀ < L := by
    calc
      L₀ < ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 := by omega
      _ ≤ (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 :=
        Nat.add_le_add_right (by
          simpa only [one_mul] using
            (Nat.mul_le_mul_right ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
              (show 1 ≤ r - 1 by omega))) 1
      _ ≤ L := hRange
  have hN : 0 < N := by omega
  have hNtwo : 2 ≤ N := by omega
  have hLN : L ≤ N := by omega
  have hNstrict : L₀ + 1 < N := by omega
  apply le_antisymm
  · apply
      ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07
        μ A hμ hr hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hRange hNlarge
    intro j
    exact le_of_eq (chainGroundSpace_eq_mpvSubmodule_normal
      ⟨L₀, hL₀, hBlk j⟩ (hBlk j) hL₀ hNtwo hL hLN hNstrict)
  · exact bntMPSVectorSpan_le_ker_parentHamiltonian_toTensorFromBlocks
      μ A hμ hN hLN

/-- The normalized BNT block-diagonal periodic chain space is the sum of the
single-block periodic chain spaces in the finite Condition C1 range, and the
corresponding open-boundary block spaces are independent.

This is the periodic ground-space conclusion of arXiv:quant-ph/0608197,
Theorem 12, proof lines 1430--1456, in the finite Condition C1 range. The
boundary closing is supplied by the global change-of-cut comparison above, so
there is no short crossing-tail span hypothesis.

This earlier variant is retained with the sufficient range containing the extra
summand \(L_0+1\). The theorem
`chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1_pgvwc07`
above proves the source bound from arXiv:quant-ph/0608197, Theorem 12.
-/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1
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
    (hNlarge : L + L₀ ≤ N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r ↦ groundSpace (A j) N) := by
  apply chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
    μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
  intro ψ hψ
  exact exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1
    μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      hNlarge hψ

/-- The normalized BNT block-diagonal periodic chain space is the sum of the
single-block periodic chain spaces in the finite Condition C1 range. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1
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
    (hNlarge : L + L₀ ≤ N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  exact (chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1
    μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hNlarge).1

/-- The global change-of-cut comparison gives the fixed-chain kernel
containment needed for the block-diagonal parent-Hamiltonian spanning clause,
provided the periodic chain space of each block is contained in its MPS line. -/
theorem ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1
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
    (hNlarge : L + L₀ ≤ N)
    (hBlock : ∀ j : Fin r,
      chainGroundSpace (A j) L N ≤ mpvSubmodule (A j) N) :
    LinearMap.ker (parentHamiltonian
      (toTensorFromBlocks (d := d) (μ := μ) A) L N) ≤
      bntMPSVectorSpan A N := by
  refine ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan
    μ A hN hLN ?_ hBlock
  exact le_of_eq
    (chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hNlarge)

end MPSTensor
