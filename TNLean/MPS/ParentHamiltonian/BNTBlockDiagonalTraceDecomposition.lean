/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossingTrace

/-!
# Finite-spanning versions of trace-decomposition results for block-diagonal parent spaces

This file packages a finite-spanning form of the trace decompositions in
Perez-Garcia--Verstraete--Wolf--Cirac, Theorem 12, into the block-diagonal
boundary and finite-range equality conclusions. The remaining source step is to
derive that trace-decomposition equality from the \(C^j,D^j\) comparison after
specializing \(D^j_\beta\) to the block-diagonal boundary expression
\((\mu_j^N X_j)A^j_\beta\). The normalized \(E^j\)-calculation is then supplied
by the downstream complementary-word lemmas.

The variables \(\beta\), \(\rho\), and \(w\) are not names from the paper.
They are the three word coordinates obtained by opening a boundary-crossing
cyclic interval; the source proof uses the boundary indices \(i_1\) and
\(i_{m+1}\) for the corresponding matrices \(C^j\) and \(D^j\).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Source trace decompositions upgrade a block-diagonal boundary representation
to periodic single-block states.

Under the normalized BNT hypotheses, every vector in the block-diagonal
periodic chain space has block-diagonal boundary conditions \(X_j\). Assume
also a length \(m\) at which the simultaneous block-word tuples span the
full product algebra. If, for those same boundary conditions, the
boundary-crossing trace decompositions
\[
  \sum_j\operatorname{tr}(A^j_\beta C^j_{i,\rho}A^j_w)
  =
  \sum_j\operatorname{tr}\bigl(((\mu_j^NX_j)A^j_\beta)A^j_\rho A^j_w\bigr)
\]
hold for every boundary-crossing interval \(i\), cut word \(\beta\),
complementary word \(\rho\), and word \(w\) of length \(m\), then the
single-block vectors
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
belong to \(\mathcal G_{N,L}(A_j)\).

This is the finite-spanning reformulation of the trace-decomposition form of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1456, after the
block-diagonal boundary conditions of arXiv:2011.12127, lines 2126--2128.

**Unfaithful:** This proof relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j,E^j\)
boundary-condition comparison from arXiv:quant-ph/0608197, Theorem 12, proof
lines 1446--1456, and use it to discharge the currently assumed
trace-decomposition equality; tracked in issue 2971. -/
theorem
    exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_bnt_c1
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {m L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hTraceSpan : WordTupleSpanTop A m)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N)
    (hTrace :
      ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
          ∃ C : ∀ (j : Fin r) (_ : Fin N),
            (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
            ∀ i : Fin N,
              N < i.val + L →
                ∀ ρ : Fin (N - L) → Fin d,
                  ∀ β : Fin (i.val + L - N) → Fin d,
                    ∀ w : Fin m → Fin d,
                      (∑ j : Fin r,
                        Matrix.trace
                          ((evalWord (A j) (List.ofFn β) * C j i ρ) *
                            evalWord (A j) (List.ofFn w))) =
                      (∑ j : Fin r,
                        Matrix.trace
                          ((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) *
                              evalWord (A j) (List.ofFn ρ)) *
                            evalWord (A j) (List.ofFn w)))) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  obtain ⟨X, hψX, _hOpen⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  obtain ⟨C, hCoeff⟩ := hTrace X hψX
  refine ⟨X, hψX, ?_⟩
  exact
    blockDiagonal_boundary_component_chainGroundSpace_of_trace_decomposition_of_injective
      μ A hN hLN X hTraceSpan hBlk hUnital hNlarge C hCoeff

/-- Source trace decompositions give the block-diagonal periodic-boundary
equality in the finite BNT range.

This theorem combines the block-diagonal boundary representation with the
trace-decomposition form of the Pérez-García--Verstraete--Wolf--Cirac
boundary-crossing comparison. It assumes a finite simultaneous word-spanning
length \(m\) and the trace equality at that length, for every
boundary-crossing interval and every block-diagonal boundary representation.
Deriving that equality from the source \(C^j,D^j\) comparison, with
\(D^j_\beta=(\mu_j^N X_j)A^j_\beta\), is the remaining step recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Unfaithful:** This proof relies on
`chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j,E^j\)
boundary-condition comparison from arXiv:quant-ph/0608197, Theorem 12, proof
lines 1446--1456, and use it to discharge the currently assumed
trace-decomposition equality; tracked in issue 2971. -/
theorem
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {m L₀ L N : ℕ}
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hTraceSpan : WordTupleSpanTop A m)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hL₀ : 0 < L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    [NeZero d] (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N)
    (hRange :
      (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + 1 ≤ L)
    (hNlarge : L + L₀ ≤ N)
    (hTrace :
      ∀ {ψ : NSiteSpace d N},
        ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
            ∃ C : ∀ (j : Fin r) (_ : Fin N),
              (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
              ∀ i : Fin N,
                N < i.val + L →
                  ∀ ρ : Fin (N - L) → Fin d,
                    ∀ β : Fin (i.val + L - N) → Fin d,
                      ∀ w : Fin m → Fin d,
                        (∑ j : Fin r,
                          Matrix.trace
                            ((evalWord (A j) (List.ofFn β) * C j i ρ) *
                              evalWord (A j) (List.ofFn w))) =
                        (∑ j : Fin r,
                          Matrix.trace
                            ((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) *
                                evalWord (A j) (List.ofFn ρ)) *
                              evalWord (A j) (List.ofFn w)))) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  exact
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      (fun ψ hψ =>
        exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_bnt_c1
          μ A hμ hIrr hLeft hOverlap hBlocks hTraceSpan hBlk hL₀ hUnital hN hL hLN hRange
          hNlarge hψ (fun X hψX => hTrace hψ X hψX))

end MPSTensor
