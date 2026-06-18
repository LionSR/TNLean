/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossingTrace

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

The source proof writes this comparison with site-indexed matrices
\(C^j_{i_1}\), \(D^j_{i_{m+1}}\), and the derived matrix \(E^j\). The words
\(\beta\) and \(\rho\) below are cut-adapted coordinates for the same
periodic-boundary comparison, not additional source terminology.
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

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

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

/-- Boundary-crossing local constraints supply the \(C^j,D^j\) comparison.

Assume the block-diagonal periodic vector has already been written with
block-diagonal boundary conditions \(X_j\).  For every cyclic interval crossing
the cut, the local constraint puts the sum of the block restrictions in
\(\bigvee_j G_L(A_j)\).  If the complementary tail words span the product
matrix algebra in the corresponding length \(N-i\), the fixed-window
Pérez-García--Verstraete--Wolf--Cirac comparison gives matrices
\(C^j_{i,\rho}\) satisfying
\[
  A^j_\beta C^j_{i,\rho}
  =
  \bigl((\mu_j^N X_j)A^j_\beta\bigr)A^j_\rho .
\]
Combining this with the existing normalized \(E^j\)-calculation gives the
periodic single-block constraints.

This is the source comparison in arXiv:quant-ph/0608197, Theorem 12, proof
lines 1436--1451, specialized to the block-diagonal boundary conditions of
arXiv:2011.12127, Section IV.C, lines 2126--2128. Here \(\rho\) is the
complementary outside word produced by opening the cyclic interval;
arXiv:quant-ph/0608197 writes the same step with the boundary indices \(i_1\)
and \(i_{m+1}\).

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Unfaithful:** This proof still relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`
for the block-diagonal boundary representation of \(\psi\). Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive that representation and the crossing comparison from the source
boundary-condition argument; tracked in issue 2971. -/
theorem
    exists_blockDiagonal_boundary_chainGroundSpace_of_crossing_pgvwc_comparison_bnt_c1
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
    (hCrossingSpan :
      ∀ i : Fin N, N < i.val + L → WordTupleSpanTop A (N - i.val))
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  refine exists_blockDiagonal_boundary_chainGroundSpace_of_pgvwc_comparison_bnt_c1
    μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
    hNlarge hψ ?_
  intro X hψX
  have hExists :
      ∀ i : Fin N, ∀ ρ : Fin (N - L) → Fin d,
        ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          N < i.val + L →
            ∀ j : Fin r, ∀ β : Fin (i.val + L - N) → Fin d,
              evalWord (A j) (List.ofFn β) * C j =
                (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                  evalWord (A j) (List.ofFn ρ) := by
    intro i ρ
    by_cases hcross : N < i.val + L
    · let τ : Fin N → Fin d := fun t =>
        if htail : i.val + L - N ≤ t.val ∧ t.val < i.val then
          ρ ⟨t.val - (i.val + L - N), by omega⟩
        else
          default
      have hρ : (List.ofFn fun k : Fin (N - L) =>
          τ ⟨i.val + L - N + k.val, by omega⟩) = List.ofFn ρ := by
        apply List.ext_getElem
        · simp
        · intro n hn₁ hn₂
          simp only [List.getElem_ofFn]
          have hn : n < N - L := by
            simpa using hn₂
          have htail :
              i.val + L ≤ i.val + L - N + n + N ∧
                (⟨i.val + L - N + n, by omega⟩ : Fin N) < i := by
            constructor
            · omega
            · change i.val + L - N + n < i.val
              omega
          simp [τ, htail]
      have hmem :
          (∑ j : Fin r,
              cyclicRestrictₗ hN L i τ
                (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
            ⨆ j : Fin r, groundSpace (A j) L :=
        blockDiagonal_boundary_cyclicRestrict_sum_mem_iSup_groundSpace
          μ A hμ hN hLN hψ X hψX i τ
      obtain ⟨C, hC⟩ :=
        blockDiagonal_boundary_crossing_pgvwc_comparison_of_sum_mem_iSup
          μ A hN hLN X i τ hcross (hCrossingSpan i hcross) hmem
      refine ⟨C, ?_⟩
      intro _ j β
      simpa [hρ] using hC j β
    · refine ⟨fun j => 0, ?_⟩
      intro hi
      exact False.elim (hcross hi)
  choose C hC using hExists
  refine ⟨fun j i ρ => C i ρ j, ?_⟩
  intro j i hi ρ β
  exact hC i ρ hi j β

/-- Boundary-crossing local constraints give the block-diagonal periodic-boundary
equality in the finite BNT range.

Let
\[
  B=\bigoplus_j\mu_jA_j.
\]
Assume the normalized BNT block-separation hypotheses and the finite injectivity
range. If every boundary-crossing interval has the simultaneous block-word
spanning property needed to separate the block traces, then the local constraint
for a vector in \(\mathcal G_{N,L}(B)\) gives the Pérez-García--Verstraete--Wolf--
Cirac \(C^j,D^j\) comparison. The preceding theorem then shows that the
corresponding block components lie in the single-block periodic chain spaces.
Consequently
\[
  \mathcal G_{N,L}(B)=\bigvee_j\mathcal G_{N,L}(A_j),
\]
and the length-\(N\) single-block spaces are independent.

This is the equality-level form of PGVWC07, Theorem 12, proof lines 1436--1451,
specialized to the block-diagonal boundary conditions of
arXiv:2011.12127, Section IV.C, lines 2126--2128.

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Scope restriction (crossing span):** The theorem assumes that the simultaneous
block-word tuples of length \(N-i\) span the product algebra for each
boundary-crossing interval beginning at \(i\). Removing this visible span
hypothesis from the finite BNT range is part of the remaining PGVWC07
boundary-comparison cleanup recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Unfaithful:** This proof still relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`
for the block-diagonal boundary representation of \(\psi\). Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive that representation and the crossing comparison from the source
boundary-condition argument; tracked in issue 2971. -/
theorem
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_crossing_pgvwc_comparison
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
    (hCrossingSpan :
      ∀ i : Fin N, N < i.val + L → WordTupleSpanTop A (N - i.val)) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  exact
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      (fun ψ hψ =>
        exists_blockDiagonal_boundary_chainGroundSpace_of_crossing_pgvwc_comparison_bnt_c1
          μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
          hNlarge hCrossingSpan hψ)

/-- Boundary-crossing local constraints give the ground-space equality stated in
Pérez-García--Verstraete--Wolf--Cirac, Theorem 12.

The preceding theorem proves this equality together with an independence
statement for the length-\(N\) single-block spaces. This theorem records only
the equality conclusion
\[
  \mathcal G_{N,L}\!\left(\bigoplus_j\mu_jA_j\right)
  =
  \bigvee_j\mathcal G_{N,L}(A_j),
\]
which is the ground-space assertion in the source theorem.

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Scope restriction (crossing span):** The theorem assumes that the simultaneous
block-word tuples of length \(N-i\) span the product algebra for each
boundary-crossing interval beginning at \(i\). Removing this visible span
hypothesis from the finite BNT range is part of the remaining PGVWC07
boundary-comparison cleanup recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

**Unfaithful:** This proof still relies on
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`
for the block-diagonal boundary representation of \(\psi\). Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. Elimination:
derive that representation and the crossing comparison from the source
boundary-condition argument; tracked in issue 2971. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_crossing_pgvwc_comparison
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
    (hCrossingSpan :
      ∀ i : Fin N, N < i.val + L → WordTupleSpanTop A (N - i.val)) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  exact
    (chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_crossing_pgvwc_comparison
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      hNlarge hCrossingSpan).1

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
\((\mu_j^NX_j)A^j_\beta\). The words \(\beta\) and \(\rho\) are formal
word coordinates for the opened boundary comparison, refining the source
end-site notation rather than replacing it. The normalized \(E^j\)-calculation
and the block-injective crossing-window argument then give the
periodic-boundary single-block constraints, and hence the block-diagonal
periodic-boundary equality.

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

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

/-- The \(C^j,D^j\) boundary-condition comparison gives the ground-space
equality stated in PGVWC07, Theorem 12.

The preceding theorem proves this equality together with an independence
statement for the length-\(N\) single-block spaces. This theorem records only
the equality conclusion
\[
  \mathcal G_{N,L}\!\left(\bigoplus_j\mu_jA_j\right)
  =
  \bigvee_j\mathcal G_{N,L}(A_j),
\]
under the assumed word-indexed \(C^j,D^j\) comparison.

**Scope restriction (length-\(L_0\) injectivity range):** PGVWC07, Theorem 12,
assumes \(L\ge 3(b-1)(L_0+1)+1\).  This theorem is stated in the current BNT
range derived from length-\(L_0\) block injectivity,
\((L_0+1)+3(r-1)(L_0+1)+1\le L\). The source-range comparison is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

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
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_pgvwc_comparison
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
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  exact
    (chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_pgvwc_comparison
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      hNlarge hComparison).1

end MPSTensor
