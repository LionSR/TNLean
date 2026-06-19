/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossingTrace
import TNLean.MPS.ParentHamiltonian.PGVWCCDEIdentities

/-!
# Finite-spanning versions of trace-decomposition results for block-diagonal parent spaces

This file records a finite-spanning form of the trace decompositions in
Theorem 12 of arXiv:quant-ph/0608197 and applies it to the block-diagonal
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

/-- Source trace decompositions give the periodic constraints for each block
under block injectivity.

For each boundary-crossing interval beginning at \(i\), assume there are
matrices \(C^j_{i,\rho}\) indexed by complementary words such that the two
trace decompositions agree for every cut word \(\beta\), complementary word
\(\rho\), and middle word \(w\):
\[
  \sum_j\operatorname{tr}(A^j_\beta C^j_{i,\rho}A^j_w)
  =
  \sum_j\operatorname{tr}\bigl(((\mu_j^NX_j)A^j_\beta)A^j_\rho A^j_w\bigr).
\]
Since the word tuples \((A^1_w,\ldots,A^r_w)\) span the full product algebra
\(\prod_j M_{D_j}(\mathbb C)\) at length \(m\), the trace equality implies
the blockwise identity
\[
  A^j_\beta C^j_{i,\rho}=((\mu_j^NX_j)A^j_\beta)A^j_\rho .
\]
The normalization \(\sum_\rho A^j_\rho A^{j\dagger}_\rho=I\) and the
compatibility identity for the complementary word \(\rho\) then give, for each
block \(j\) and interval \(i\), a matrix \(E_{j,i,\rho}\) such that, for every
cut word \(\beta\),
\[
  ((\mu_j^NX_j)A^j_\beta)A^j_\rho=A^j_\beta E_{j,i,\rho}.
\]
These identities give
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)\in\mathcal G_{N,L}(A_j).
\]
This is the boundary-crossing trace-decomposition form of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1456.

**Local fix (adjoint correction):** The matrix identity used here
replaces the source's \(E^j=\sum_k C^j_kA^j_k\) by
\(E^j=\sum_k C^j_kA^{j\dagger}_k\), since the normalization is
\(\sum_k A^j_kA^{j\dagger}_k=I\). This is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem
    blockDiagonal_boundary_component_chainGroundSpace_of_trace_decomposition_of_injective
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m L₀ L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hTraceSpan : WordTupleSpanTop A m)
    (hBlk : ∀ j : Fin r, IsNBlkInjective (A j) L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hNlarge : L + L₀ ≤ N)
    (C : ∀ (j : Fin r) (_ : Fin N),
      (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ i : Fin N,
      N < i.val + L →
        ∀ ρ : Fin (N - L) → Fin d, ∀ β : Fin (i.val + L - N) → Fin d,
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
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  refine
    blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities_of_injective
      μ A hN hLN X hBlk hUnital hNlarge ?_
  intro j i hi ρ
  obtain ⟨E, _hE, hBoundary, _hCDE⟩ :=
    pgvwc07_complementary_word_cde_identities_of_block_boundary_trace_decomposition
      (μ := μ) (A := A) (m := m) (K := i.val + L - N) (M := N - L) (N := N)
      hTraceSpan X (fun k => C k i) hUnital (hCoeff i hi) j
  refine ⟨E * evalWord (A j) (List.ofFn ρ), ?_⟩
  intro β
  calc
    (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
        evalWord (A j) (List.ofFn ρ)
        = (evalWord (A j) (List.ofFn β) * E) *
            evalWord (A j) (List.ofFn ρ) := by rw [hBoundary β]
    _ = evalWord (A j) (List.ofFn β) *
        (E * evalWord (A j) (List.ofFn ρ)) := by rw [Matrix.mul_assoc]

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
derive the \(C^j,D^j,E^j\) boundary-condition comparison from
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and use it to
discharge the currently assumed
trace-decomposition equality. -/
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

/-- BNT normalization gives the common middle-word product span.

In arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1451, condition C1 is
used to separate the two trace decompositions at a common middle-word length.
Under the finite block-injectivity and BNT hypotheses used here, the
block-separation theorem gives that simultaneous product span at
\[
  (L_0+1)+(r-1)\bigl((L_0+1)+((L_0+1)+(L_0+1))\bigr).
\]
The remaining hypothesis is therefore the trace-decomposition equality itself,
with \(D^j_\beta\) specialized to \((\mu_j^NX_j)A^j_\beta\).

**Unfaithful:** This proof still relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the block-diagonal boundary representation and the displayed
trace-decomposition equality from the source boundary-condition argument. -/
theorem
    exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_bnt_c1_span
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
    (hTrace :
      let m : ℕ :=
        (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
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
  let m : ℕ :=
    (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
  have hTraceSpan : WordTupleSpanTop A m :=
    wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital (by simp [m])
  exact
    exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_bnt_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hTraceSpan hBlk hL₀ hUnital hN hL hLN hRange
      hNlarge hψ hTrace

/-- Source trace decompositions give the block-diagonal periodic-boundary
equality in the finite BNT range.

This theorem combines the block-diagonal boundary representation with the
trace-decomposition form of the boundary-condition comparison in
arXiv:quant-ph/0608197, Theorem 12. It assumes a finite simultaneous word-spanning
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
derive the \(C^j,D^j,E^j\) boundary-condition comparison from
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and use it to
discharge the currently assumed
trace-decomposition equality. -/
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

/-- BNT normalization gives the common middle-word product span for the
ground-space equality.

This is the finite block-injective specialization of the preceding equality
theorem. The simultaneous product span at the middle-word length used in
arXiv:quant-ph/0608197, Theorem 12, is derived from the BNT hypotheses; the
remaining input is the trace-decomposition equality from arXiv:quant-ph/0608197,
Theorem 12, proof lines 1436--1448, with \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\).

**Unfaithful:** This proof still relies on
`chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary`,
which transitively uses the boundary-condition comparison at boundary-crossing
windows rather than deriving it from arXiv:2011.12127, Section IV.C, lines
2126--2128. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive the block-diagonal boundary representation and the displayed
trace-decomposition equality from the source boundary-condition argument. -/
theorem
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_trace_decomposition_bnt_c1_span
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
    (hTrace :
      let m : ℕ :=
        (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
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
  classical
  let m : ℕ :=
    (L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
  have hTraceSpan : WordTupleSpanTop A m :=
    wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1
      A hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital (by simp [m])
  exact
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_trace_decomposition
      μ A hμ hIrr hLeft hOverlap hBlocks hTraceSpan hBlk hL₀ hUnital hN hL hLN hRange
      hNlarge hTrace

end MPSTensor
