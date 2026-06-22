/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain

/-!
# Boundary-decomposition consequence for block-diagonal chain spaces

This file contains the boundary-decomposition consequence of the
block-diagonal chain-space comparison.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

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
and the sum \(\bigvee_jG_N(A_j)\) is internal.

**Scope restriction (periodic-boundary comparison):** The blockwise decomposition
with periodic components \(\psi_j\in\mathcal G_{N,L}(A_j)\) is the explicit
hypothesis `hBoundary` here. The span-based open-boundary decomposition is proved
(its summands lie in \(G_N(A_j)\)); the periodic-boundary upgrade is the
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
