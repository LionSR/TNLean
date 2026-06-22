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

/-- The opened-boundary \(C^j\)-comparison with the block boundary expression
implies the corresponding boundary trace comparison.

For fixed block-diagonal boundary matrices \(X_j\), suppose the opened-boundary
matrices \(C^j_{i,\rho}\) satisfy
\[
  A^j_\beta C^j_{i,\rho}
  =
  ((\mu_j^NX_j)A^j_\beta)A^j_\rho
\]
at every boundary-crossing interval. Multiplying by the middle word \(A^j_w\),
taking traces, and summing over \(j\) gives the boundary trace comparison used
in arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. Here
\((\mu_j^NX_j)A^j_\beta\) plays the role of \(D^j_\beta\) in the source
proof. -/
theorem blockDiagonal_boundary_trace_decomposition_of_pgvwc_comparison
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m L N : ℕ}
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : ∀ (j : Fin r) (_ : Fin N),
      (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hComparison : ∀ (j : Fin r) (i : Fin N),
      N < i.val + L →
        ∀ ρ : Fin (N - L) → Fin d,
          ∀ β : Fin (i.val + L - N) → Fin d,
            evalWord (A j) (List.ofFn β) * C j i ρ =
              (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                evalWord (A j) (List.ofFn ρ)) :
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
                    evalWord (A j) (List.ofFn w))) := by
  intro i hi ρ β w
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [hComparison j i hi ρ β]

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

/-- Source trace decompositions and an explicit block-diagonal boundary
representation give periodic single-block states.

Assume the vector has already been written with block-diagonal boundary
conditions \(X_j\). If, for those boundary conditions, the boundary-crossing
trace decompositions of arXiv:quant-ph/0608197, Theorem 12, proof lines
1436--1456 hold at a simultaneous product-spanning middle-word length, then the
trace comparison gives
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)\in\mathcal G_{N,L}(A_j)
\]
for every block \(j\). In the notation of the source proof, the boundary matrix
\(D^j_\beta\) has already been specialized to \((\mu_j^NX_j)A^j_\beta\).

This is the explicit-boundary form of the block-diagonal boundary-condition
step in arXiv:2011.12127, Section IV.C, lines 2126--2128. It does not use the
simultaneous block-word span at the short boundary-crossing tail length \(N-i\);
the only span hypothesis is the middle-word product span used to separate the
trace decompositions.

**Scope restriction (boundary representation and trace decomposition):** The
block-diagonal boundary representation of \(\psi\) and the displayed trace
decompositions are hypotheses here. Removing these remaining inputs is tracked
in issue 2971 and documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_of_boundary
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    {m L₀ L N : ℕ}
    (hTraceSpan : WordTupleSpanTop A m)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hN : 0 < N) (hLN : L ≤ N)
    (hNlarge : L + L₀ ≤ N)
    {ψ : NSiteSpace d N}
    (hBoundary :
      ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
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
  obtain ⟨X, hψX⟩ := hBoundary
  obtain ⟨C, hCoeff⟩ := hTrace X hψX
  refine ⟨X, hψX, ?_⟩
  exact
    blockDiagonal_boundary_component_chainGroundSpace_of_trace_decomposition_of_injective
      μ A hN hLN X hTraceSpan hBlk hUnital hNlarge C hCoeff

/-- A boundary-crossing local constraint gives the fixed-tail boundary trace
comparison once a block-diagonal boundary representation is fixed.

Assume
\[
  \psi=\Gamma_N^{\oplus_j\mu_jA_j}\!\left(\bigoplus_jX_j\right)
\]
and \(\psi\in\mathcal G_{N,L}(\oplus_j\mu_jA_j)\). For a cyclic interval
starting at \(i\) and crossing the boundary cut, the local constraint on
\(\psi\) says that the corresponding sum of block restrictions lies in
\(\bigvee_jG_L(A_j)\). Opening the interval with outside word \(\rho\), the
fixed-interval trace-decomposition lemma supplies matrices \(C^j_{i,\rho}\)
such that, for every word \(\beta\) before the cut and every wrapped tail word
\(w\) of length \(N-i\),
\[
  \sum_j\operatorname{tr}(A^j_\beta C^j_{i,\rho}A^j_w)
  =
  \sum_j\operatorname{tr}\bigl(((\mu_j^NX_j)A^j_\beta)A^j_\rho A^j_w\bigr).
\]

This is the explicit-boundary trace-decomposition step in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1451, specialized to
the block-diagonal boundary conditions in arXiv:2011.12127, Section IV.C,
lines 2126--2128. It records only the fixed wrapped-tail length \(N-i\)
provided by the local cyclic-window constraint; the separate middle-word trace
theorem keeps the common product-spanning length \(m\) as an explicit
hypothesis.

**Scope restriction (boundary representation):** The block-diagonal boundary
representation of \(\psi\) is a hypothesis here. Removing this remaining input
is tracked in issue 2971 and documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem blockDiagonal_boundary_crossing_trace_decomposition_of_boundary
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L N : ℕ} [NeZero d] (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hψX :
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
    (i : Fin N) (hi : N < i.val + L)
    (ρ : Fin (N - L) → Fin d) :
    ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ β : Fin (i.val + L - N) → Fin d,
        ∀ w : Fin (N - i.val) → Fin d,
          (∑ j : Fin r,
            Matrix.trace
              ((evalWord (A j) (List.ofFn β) * C j) *
                evalWord (A j) (List.ofFn w))) =
          (∑ j : Fin r,
            Matrix.trace
              ((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) *
                  evalWord (A j) (List.ofFn ρ)) *
                evalWord (A j) (List.ofFn w))) := by
  classical
  let τ : Fin N → Fin d := fun t =>
    if htail : i.val + L - N ≤ t.val ∧ t.val < i.val then
      ρ ⟨t.val - (i.val + L - N), by omega⟩
    else
      (0 : Fin d)
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
  obtain ⟨C, hTrace⟩ :=
    blockDiagonal_boundary_crossing_trace_decomposition_of_sum_mem_iSup
      μ A hN hLN X i τ hi hmem
  refine ⟨C, ?_⟩
  intro β w
  let σ : Fin L → Fin d := fun k =>
    if hk : k.val < N - i.val then
      w ⟨k.val, hk⟩
    else
      β ⟨k.val - (N - i.val), by omega⟩
  have hHead :
      (List.ofFn fun k : Fin (i.val + L - N) =>
        σ ⟨N - i.val + k.val, by omega⟩) = List.ofFn β := by
    apply List.ext_getElem
    · simp
    · intro n hn₁ hn₂
      simp only [List.getElem_ofFn]
      have hnot : ¬N - i.val + n < N - i.val := by omega
      simp [σ, hnot]
  have hMiddle :
      (List.ofFn fun k : Fin (N - L) =>
        τ ⟨i.val + L - N + k.val, by omega⟩) = List.ofFn ρ := hρ
  have hTail :
      (List.ofFn fun k : Fin (N - i.val) =>
        σ ⟨k.val, by omega⟩) = List.ofFn w := by
    apply List.ext_getElem
    · simp
    · intro n hn₁ hn₂
      simp only [List.getElem_ofFn]
      have hlt : n < N - i.val := by
        simpa using hn₁
      simp [σ, hlt]
  simpa [hHead, hMiddle, hTail, Matrix.mul_assoc] using hTrace σ

/-- A fixed block-diagonal boundary representation gives fixed-tail boundary
trace comparisons for all boundary-crossing intervals.

The preceding fixed-interval construction may be chosen for every crossing
start \(i\) and every outside word \(\rho\) at once. Thus, under the same
explicit boundary representation
\[
  \psi=\Gamma_N^{\oplus_j\mu_jA_j}\!\left(\bigoplus_jX_j\right),
\]
there are matrices \(C^j_{i,\rho}\) such that, whenever \(N<i+L\),
\[
  \sum_j\operatorname{tr}(A^j_\beta C^j_{i,\rho}A^j_w)
  =
  \sum_j\operatorname{tr}\bigl(((\mu_j^NX_j)A^j_\beta)A^j_\rho A^j_w\bigr)
\]
for every word \(\beta\) before the cut and every wrapped tail word \(w\) of
length \(N-i\).

This is the family form of the explicit-boundary trace-decomposition step in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1451, specialized to
the block-diagonal boundary conditions in arXiv:2011.12127, Section IV.C,
lines 2126--2128. It is still a fixed wrapped-tail statement; it does not
replace the separate common product-spanning length hypothesis.

**Scope restriction (boundary representation):** The block-diagonal boundary
representation of \(\psi\) is a hypothesis here. Removing this remaining
hypothesis is tracked in issue 2971 and documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem blockDiagonal_boundary_crossing_trace_decompositions_of_boundary
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ : ∀ k : Fin r, μ k ≠ 0)
    {L N : ℕ} [NeZero d] (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hψX :
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X))) :
    ∃ C : ∀ (j : Fin r) (_ : Fin N),
        (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ i : Fin N,
        N < i.val + L →
          ∀ ρ : Fin (N - L) → Fin d,
            ∀ β : Fin (i.val + L - N) → Fin d,
              ∀ w : Fin (N - i.val) → Fin d,
                (∑ j : Fin r,
                  Matrix.trace
                    ((evalWord (A j) (List.ofFn β) * C j i ρ) *
                      evalWord (A j) (List.ofFn w))) =
                (∑ j : Fin r,
                  Matrix.trace
                    ((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) *
                        evalWord (A j) (List.ofFn ρ)) *
                      evalWord (A j) (List.ofFn w))) := by
  classical
  have hExists :
      ∀ i : Fin N, ∀ ρ : Fin (N - L) → Fin d,
        ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          N < i.val + L →
            ∀ β : Fin (i.val + L - N) → Fin d,
              ∀ w : Fin (N - i.val) → Fin d,
                (∑ j : Fin r,
                  Matrix.trace
                    ((evalWord (A j) (List.ofFn β) * C j) *
                      evalWord (A j) (List.ofFn w))) =
                (∑ j : Fin r,
                  Matrix.trace
                    ((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) *
                        evalWord (A j) (List.ofFn ρ)) *
                      evalWord (A j) (List.ofFn w))) := by
    intro i ρ
    by_cases hi : N < i.val + L
    · obtain ⟨C, hC⟩ :=
        blockDiagonal_boundary_crossing_trace_decomposition_of_boundary
          μ A hμ hN hLN hψ X hψX i hi ρ
      exact ⟨C, fun _ => hC⟩
    · refine ⟨fun _ => 0, ?_⟩
      intro hcross
      exact False.elim (hi hcross)
  choose C hC using hExists
  refine ⟨fun j i ρ => C i ρ j, ?_⟩
  intro i hi ρ β w
  exact hC i ρ hi β w

/-- The \(C^j,D^j\) boundary comparison gives periodic single-block states
from an explicit block-diagonal boundary representation.

Assume the vector has already been written with block-diagonal boundary
conditions \(X_j\). If, for those same boundary conditions, the source
boundary comparison
\[
  A^j_\beta C^j_{i,\rho}
  =
  ((\mu_j^NX_j)A^j_\beta)A^j_\rho
\]
holds at each boundary-crossing interval, then the comparison identity implies,
for every boundary-crossing interval \(i\), outside word \(\rho\), word
\(\beta\) before the cut, and middle word \(w\),
\[
  \sum_j\operatorname{tr}\!\bigl(A^j_\beta C^j_{i,\rho}A^j_w\bigr)
  =
  \sum_j\operatorname{tr}\!\bigl(((\mu_j^NX_j)A^j_\beta)
    A^j_\rho A^j_w\bigr).
\]
The trace-decomposition theorem then gives
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)\in\mathcal G_{N,L}(A_j)
\]
for every block \(j\).

This is the explicit-boundary form of the block-diagonal boundary-condition
step in arXiv:2011.12127, Section IV.C, lines 2126--2128, using the
specialization \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\) from
arXiv:quant-ph/0608197, Theorem 12, lines 1446--1451.

**Scope restriction (boundary representation):** The block-diagonal boundary
representation of \(\psi\) is a hypothesis here. Removing this remaining input
is tracked in issue 2971 and documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_pgvwc_comparison_of_boundary
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    {m L₀ L N : ℕ}
    (hTraceSpan : WordTupleSpanTop A m)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hN : 0 < N) (hLN : L ≤ N)
    (hNlarge : L + L₀ ≤ N)
    {ψ : NSiteSpace d N}
    (hBoundary :
      ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
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
  refine
    exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_of_boundary
      μ A hTraceSpan hBlk hUnital hN hLN hNlarge hBoundary ?_
  intro X hψX
  obtain ⟨C, hCompat⟩ := hComparison X hψX
  refine ⟨C, ?_⟩
  exact blockDiagonal_boundary_trace_decomposition_of_pgvwc_comparison μ A X C hCompat

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

**Scope restriction (periodic-boundary comparison):** The boundary trace
decomposition `hTrace` is the explicit hypothesis here. The block-diagonal
boundary representation supplied by
`exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1`
is the boundary-comparison-free open-boundary inclusion of arXiv:quant-ph/0608197, Theorem 12 (its
block components lie in \(G_N(A_j)\)) and does not assume the boundary-crossing
comparison. The periodic-boundary upgrade encoded by `hTrace` — the boundary trace
comparison with \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\) — is the boundary-condition
comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, not yet derived from the periodic
ground-space constraint. Documented in
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
  exact
    exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_of_boundary
      μ A hTraceSpan hBlk hUnital hN hLN hNlarge ⟨X, hψX⟩ hTrace

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

**Scope restriction (periodic-boundary comparison):** The boundary trace
decomposition `hTrace` is the explicit hypothesis here. The block-diagonal
boundary representation it builds on is the boundary-comparison-free open-boundary inclusion of
arXiv:quant-ph/0608197, Theorem 12, independent of the boundary-crossing
comparison; the common middle-word span is supplied by the BNT block-separation
theorem. The periodic-boundary upgrade encoded by `hTrace` — the boundary trace
comparison with \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\) — is the boundary-condition
comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, not yet derived from the periodic
ground-space constraint. Documented in
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

**Scope restriction (periodic-boundary comparison):** The boundary trace
decomposition `hTrace` is the explicit hypothesis here. The underlying
block-diagonal boundary representation is the boundary-comparison-free open-boundary inclusion of
arXiv:quant-ph/0608197, Theorem 12, independent of the boundary-crossing
comparison. The periodic-boundary upgrade encoded by `hTrace` — the boundary trace
comparison with \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\) — is the boundary-condition
comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, not yet derived from the periodic
ground-space constraint. Documented in
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

**Scope restriction (periodic-boundary comparison):** The boundary trace
decomposition `hTrace` is the explicit hypothesis here. The underlying
block-diagonal boundary representation is the boundary-comparison-free open-boundary inclusion of
arXiv:quant-ph/0608197, Theorem 12, independent of the boundary-crossing
comparison; the common middle-word span is supplied by the BNT block-separation
theorem. The periodic-boundary upgrade encoded by `hTrace` — the boundary trace
comparison with \(D^j_\beta=(\mu_j^NX_j)A^j_\beta\) — is the boundary-condition
comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1456, and
arXiv:2011.12127, Section IV.C, lines 2126--2128, not yet derived from the periodic
ground-space constraint. Documented in
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
