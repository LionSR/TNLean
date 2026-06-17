/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossing

/-!
# Boundary-condition comparisons for block-diagonal parent spaces

The word-indexed Pérez-García--Verstraete--Wolf--Cirac comparison
\[
  A^j_\beta C^j_{i,\rho}
  =
  \bigl((\mu_j^NX_j)A^j_\beta\bigr)A^j_\rho
\]
is the local boundary-crossing coordinate form of the \(C^j,D^j\) trace
comparison from arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451,
after specializing \(D^j_\beta\) to \((\mu_j^N X_j)A^j_\beta\). The normalized
\(E^j\)-calculation then implies the periodic-boundary single-block constraints
and the finite-range block-diagonal periodic-boundary equality used here.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The \(C^j,D^j\) boundary-condition comparison upgrades a block-diagonal
boundary representation to periodic single-block states.

Under the normalized BNT hypotheses, every vector in the block-diagonal
periodic-boundary ground space has block-diagonal boundary conditions \(X_j\). If those
same boundary conditions satisfy the Pérez-García--Verstraete--Wolf--Cirac
comparison, in the word-indexed boundary-crossing form
\[
  A^j_\beta C^j_{i,\rho}
  =
  \bigl((\mu_j^NX_j)A^j_\beta\bigr)A^j_\rho ,
\]
then the single-block vectors \(\Gamma_N^{A_j}(\mu_j^NX_j)\) satisfy the
periodic-boundary constraints.

This records the source comparison in arXiv:quant-ph/0608197, Theorem 12,
proof lines 1446--1451, before the normalized \(E^j\)-calculation turns it
into the boundary-crossing identities with \(E_{j,i,\rho}\).
The words \(\beta\) and \(\rho\) are local coordinates for a boundary-crossing
window, not terminology of the source statement.

**Unfaithful:** This proof relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j,E^j\)
boundary-condition comparison from arXiv:quant-ph/0608197, Theorem 12, proof
lines 1446--1456, and use it to discharge the currently assumed comparison;
tracked in issue 2971. -/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_pgvwc_comparison_bnt_c1
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
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N)
    (hComparison :
      ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
        ∃ C : ∀ (j : Fin r) (_ : Fin N),
          (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ∀ (j : Fin r) (i : Fin N),
            N < i.val + L →
              ∀ ρ : Fin (N - L) → Fin d,
                ∀ β : Fin (i.val + L - N) → Fin d,
                  evalWord (A j) (List.ofFn β) * C j i ρ =
                    (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                      evalWord (A j) (List.ofFn ρ)) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  obtain ⟨X, hψX, _hOpen⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  obtain ⟨C, hCompat⟩ := hComparison X hψX
  refine ⟨X, hψX, ?_⟩
  exact blockDiagonal_boundary_component_chainGroundSpace_of_pgvwc_comparison_of_injective
    μ A hN hLN X hBlk hUnital hNlarge C hCompat

/-- The \(C^j,D^j\) boundary-condition comparison gives the block-diagonal
periodic-boundary equality in the finite BNT range.

This theorem assumes the source \(C^j,D^j\) comparison only up to the
word-indexed matrix identity
\[
  A^j_\beta C^j_{i,\rho}
  =
  \bigl((\mu_j^NX_j)A^j_\beta\bigr)A^j_\rho
\]
for every boundary-crossing interval, local word \(\beta\) before the cut,
and outside word \(\rho\), with \(D^j_\beta\) already specialized to
\((\mu_j^NX_j)A^j_\beta\). The normalized \(E^j\)-calculation and the
block-injective crossing-window argument then give the periodic-boundary
single-block constraints, and hence the block-diagonal periodic-boundary
equality.

**Unfaithful:** This proof relies on
`chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j,E^j\)
boundary-condition comparison from arXiv:quant-ph/0608197, Theorem 12, proof
lines 1446--1456, and use it to discharge the currently assumed comparison;
tracked in issue 2971. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_pgvwc_comparison
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
    (hComparison :
      ∀ {ψ : NSiteSpace d N},
        ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
          ∃ C : ∀ (j : Fin r) (_ : Fin N),
            (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
            ∀ (j : Fin r) (i : Fin N),
              N < i.val + L →
                ∀ ρ : Fin (N - L) → Fin d,
                  ∀ β : Fin (i.val + L - N) → Fin d,
                    evalWord (A j) (List.ofFn β) * C j i ρ =
                      (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                        evalWord (A j) (List.ofFn ρ)) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  exact
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      (fun ψ hψ =>
        exists_blockDiagonal_boundary_chainGroundSpace_of_pgvwc_comparison_bnt_c1
          μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
          hNlarge hψ (fun X hψX => hComparison hψ X hψX))

end MPSTensor
