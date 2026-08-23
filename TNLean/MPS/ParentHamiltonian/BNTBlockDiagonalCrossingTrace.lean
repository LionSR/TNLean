/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalCrossing
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty

/-!
# Trace decompositions at a boundary-crossing interval

This file records the fixed-interval trace-decomposition equality obtained from
the block-diagonal local constraint at a cyclic interval crossing the boundary
cut.  It is the local coefficient form of the two trace decompositions in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1444, specialized to the
block-diagonal boundary conditions used in arXiv:2011.12127, Section IV.C,
lines 2126--2128.

The paper writes the two decompositions with \(C^j_{i_1}\) and
\(D^j_{i_{m+1}}\). Below, \(\beta\) and \(w\) are the two pieces of the
local word after opening the cut, while \(\rho\) is the complementary outside
word on the sites not lying in the local interval.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- A fixed boundary-crossing local constraint gives the corresponding trace
decomposition.

Let a cyclic interval of length \(L\) begin at \(i\), with \(N<i+L\).  For a
local word \(\sigma\), write
\[
  \beta=\sigma_{N-i}\cdots\sigma_{L-1},\qquad
  \rho=\tau_{i+L-N}\cdots\tau_{i-1},\qquad
  w=\sigma_0\cdots\sigma_{N-i-1}.
\]
If the block sum of the cyclic restrictions lies in
\(\bigvee_jG_L(A^j)\), then there are matrices \(C^j_{i,\tau}\) such that
\[
  \sum_j\operatorname{tr}(A^j_\beta C^j_{i,\tau} A^j_w)
  =
  \sum_j\operatorname{tr}\bigl(((\mu_j^NX_j)A^j_\beta)A^j_\rho A^j_w\bigr)
\]
for every local word \(\sigma\). This is the fixed-interval
trace-decomposition comparison used in Perez-Garcia--Verstraete--Wolf--Cirac,
Theorem 12. -/
theorem blockDiagonal_boundary_crossing_trace_decomposition_of_sum_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (i : Fin N) (τ : Fin N → Fin d) (hi : N < i.val + L)
    (hmem :
      (∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
        ⨆ j : Fin r, groundSpace (A j) L) :
    ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ σ : Fin L → Fin d,
        let headWord : List (Fin d) := List.ofFn fun k : Fin (i.val + L - N) =>
          σ ⟨N - i.val + k.val, by omega⟩
        let middleWord : List (Fin d) := List.ofFn fun k : Fin (N - L) =>
          τ ⟨i.val + L - N + k.val, by omega⟩
        let tailWord : List (Fin d) := List.ofFn fun k : Fin (N - i.val) =>
          σ ⟨k.val, by omega⟩
        (∑ j : Fin r,
          Matrix.trace
            ((Kraus.evalWord (A j) headWord * C j) * Kraus.evalWord (A j) tailWord)) =
        (∑ j : Fin r,
          Matrix.trace
            ((((μ j) ^ N • X j) * Kraus.evalWord (A j) headWord *
                Kraus.evalWord (A j) middleWord) *
              Kraus.evalWord (A j) tailWord)) := by
  classical
  obtain ⟨φ, hφmem, hφsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun j : Fin r => groundSpace (A j) L)
      (∑ j : Fin r,
        cyclicRestrictₗ hN L i τ
          (groundSpaceMap (A j) N ((μ j) ^ N • X j)))).mp hmem
  have hφsum_univ :
      (∑ j : Fin r, φ j) =
        ∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j)) := by
    simpa [Finsupp.sum_fintype] using hφsum
  have hMatrix : ∀ j : Fin r,
      ∃ Cj : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        φ j = groundSpaceMap (A j) L Cj := by
    intro j
    have hφj := hφmem j
    rw [groundSpace, LinearMap.mem_range] at hφj
    rcases hφj with ⟨Cj, hCj⟩
    exact ⟨Cj, hCj.symm⟩
  choose C hC using hMatrix
  refine ⟨C, ?_⟩
  intro σ
  let headWord : List (Fin d) := List.ofFn fun k : Fin (i.val + L - N) =>
    σ ⟨N - i.val + k.val, by omega⟩
  let middleWord : List (Fin d) := List.ofFn fun k : Fin (N - L) =>
    τ ⟨i.val + L - N + k.val, by omega⟩
  let tailWord : List (Fin d) := List.ofFn fun k : Fin (N - i.val) =>
    σ ⟨k.val, by omega⟩
  have hσ : List.ofFn σ = tailWord ++ headWord := by
    simpa [tailWord, headWord] using
      ofFn_eq_boundary_crossing_tail_append_head i hi σ
  have hLeft :
      (∑ j : Fin r,
          Matrix.trace
            ((Kraus.evalWord (A j) headWord * C j) * Kraus.evalWord (A j) tailWord)) =
        ∑ j : Fin r, φ j σ := by
    refine Finset.sum_congr rfl ?_
    intro j _
    have hφj :
        φ j σ = Matrix.trace (Kraus.evalWord (A j) (List.ofFn σ) * C j) := by
      rw [hC j, groundSpaceMap_apply]
    calc
      Matrix.trace
          ((Kraus.evalWord (A j) headWord * C j) * Kraus.evalWord (A j) tailWord)
          =
        Matrix.trace
          (Kraus.evalWord (A j) tailWord * (Kraus.evalWord (A j) headWord * C j)) :=
            Matrix.trace_mul_comm _ _
      _ =
        Matrix.trace
          ((Kraus.evalWord (A j) tailWord * Kraus.evalWord (A j) headWord) * C j) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.trace (Kraus.evalWord (A j) (List.ofFn σ) * C j) := by
            rw [hσ, Kraus.evalWord_append]
      _ = φ j σ := hφj.symm
  have hSum :
      (∑ j : Fin r, φ j σ) =
        ∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j)) σ := by
    calc
      (∑ j : Fin r, φ j σ) = (∑ j : Fin r, φ j) σ := by simp
      _ =
        (∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j))) σ := by
            rw [hφsum_univ]
      _ =
        ∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j)) σ := by simp
  have hRight :
      (∑ j : Fin r,
          Matrix.trace
            ((((μ j) ^ N • X j) * Kraus.evalWord (A j) headWord *
                Kraus.evalWord (A j) middleWord) *
              Kraus.evalWord (A j) tailWord)) =
        ∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j)) σ := by
    refine Finset.sum_congr rfl ?_
    intro j _
    have hApply :=
      blockDiagonal_boundary_cyclicRestrict_component_apply_crossing
        μ A hN hLN X j i τ hi σ
    calc
      Matrix.trace
          ((((μ j) ^ N • X j) * Kraus.evalWord (A j) headWord *
              Kraus.evalWord (A j) middleWord) *
            Kraus.evalWord (A j) tailWord)
          =
        Matrix.trace
          (((μ j) ^ N • X j) *
            ((Kraus.evalWord (A j) headWord * Kraus.evalWord (A j) middleWord) *
              Kraus.evalWord (A j) tailWord)) := by
            simp [Matrix.mul_assoc]
      _ =
        Matrix.trace
          (((Kraus.evalWord (A j) headWord * Kraus.evalWord (A j) middleWord) *
              Kraus.evalWord (A j) tailWord) *
            ((μ j) ^ N • X j)) :=
            Matrix.trace_mul_comm _ _
      _ =
        cyclicRestrictₗ hN L i τ
          (groundSpaceMap (A j) N ((μ j) ^ N • X j)) σ := by
            simpa [headWord, middleWord, tailWord] using hApply.symm
  exact hLeft.trans (hSum.trans hRight.symm)

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
is documented in
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
              ((Kraus.evalWord (A j) (List.ofFn β) * C j) *
                Kraus.evalWord (A j) (List.ofFn w))) =
          (∑ j : Fin r,
            Matrix.trace
              ((((μ j) ^ N • X j) * Kraus.evalWord (A j) (List.ofFn β) *
                  Kraus.evalWord (A j) (List.ofFn ρ)) *
                Kraus.evalWord (A j) (List.ofFn w))) := by
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
hypothesis is documented in
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
                    ((Kraus.evalWord (A j) (List.ofFn β) * C j i ρ) *
                      Kraus.evalWord (A j) (List.ofFn w))) =
                (∑ j : Fin r,
                  Matrix.trace
                    ((((μ j) ^ N • X j) * Kraus.evalWord (A j) (List.ofFn β) *
                        Kraus.evalWord (A j) (List.ofFn ρ)) *
                      Kraus.evalWord (A j) (List.ofFn w))) := by
  classical
  have hExists :
      ∀ i : Fin N, ∀ ρ : Fin (N - L) → Fin d,
        ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          N < i.val + L →
            ∀ β : Fin (i.val + L - N) → Fin d,
              ∀ w : Fin (N - i.val) → Fin d,
                (∑ j : Fin r,
                  Matrix.trace
                    ((Kraus.evalWord (A j) (List.ofFn β) * C j) *
                      Kraus.evalWord (A j) (List.ofFn w))) =
                (∑ j : Fin r,
                  Matrix.trace
                    ((((μ j) ^ N • X j) * Kraus.evalWord (A j) (List.ofFn β) *
                        Kraus.evalWord (A j) (List.ofFn ρ)) *
                      Kraus.evalWord (A j) (List.ofFn w))) := by
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

/-- Fixed boundary-crossing \(C^j,D^j\) comparison from the local block-sum
constraint.

For a cyclic interval of length \(L\) beginning at \(i\), with \(N<i+L\), the
preceding trace decomposition has a fixed complementary word
\[
  \rho(k)=\tau_{i+L-N+k},\qquad 0\le k<N-L.
\]
If the tail-word products at length \(N-i\) span the blockwise product algebra,
then the trace decomposition implies, for every block \(j\) and every wrapped
word \(\beta\) before the cut,
\[
  A^j_\beta C^j
  =
  \bigl((\mu_j^NX_j)A^j_\beta\bigr)A^j_\rho .
\]
This is the fixed cyclic-interval coordinate form of the
Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j\) comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1448. The source writes
the local coordinates as \(i_1,\ldots,i_{m+1}\); here \(\beta\) is the wrapped
word before the cut and \(\rho\) is the complementary outside word. -/
theorem blockDiagonal_boundary_crossing_pgvwc_comparison_of_sum_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (i : Fin N) (τ : Fin N → Fin d) (hi : N < i.val + L)
    (hSpan : WordTupleSpanTop A (N - i.val))
    (hmem :
      (∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
        ⨆ j : Fin r, groundSpace (A j) L) :
    ∃ C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      let ρ : Fin (N - L) → Fin d := fun k =>
        τ ⟨i.val + L - N + k.val, by omega⟩
      ∀ j : Fin r, ∀ β : Fin (i.val + L - N) → Fin d,
        Kraus.evalWord (A j) (List.ofFn β) * C j =
          (((μ j) ^ N • X j) * Kraus.evalWord (A j) (List.ofFn β)) *
            Kraus.evalWord (A j) (List.ofFn ρ) := by
  classical
  obtain ⟨C, hTrace⟩ :=
    blockDiagonal_boundary_crossing_trace_decomposition_of_sum_mem_iSup
      μ A hN hLN X i τ hi hmem
  refine ⟨C, ?_⟩
  let ρ : Fin (N - L) → Fin d := fun k =>
    τ ⟨i.val + L - N + k.val, by omega⟩
  refine
    pgvwc07_fixed_complementary_word_compatibility_of_trace_decomposition
      (A := A) (m := N - i.val) (K := i.val + L - N) (M := N - L)
      hSpan (fun j => (μ j) ^ N • X j) C ρ ?_
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
        τ ⟨i.val + L - N + k.val, by omega⟩) = List.ofFn ρ := by
    rfl
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

/-- Fixed boundary-crossing \(C^j,D^j\) comparison gives local block membership.

For a cyclic interval of length \(L\) beginning at \(i\), with \(N<i+L\), assume
that the local block sum lies in \(\bigvee_jG_L(A^j)\) and that the tail-word
products of length \(N-i\) span the blockwise product algebra. The preceding
Perez-Garcia--Verstraete--Wolf--Cirac \(C^j,D^j\) comparison then supplies,
for each block \(j\), the boundary matrix required to write
\[
  R_{i,\tau}\!\left(\Gamma_N^{A_j}(\mu_j^NX_j)\right)
\]
as a vector in \(G_L(A^j)\).

This is the fixed-window local-membership consequence of arXiv:quant-ph/0608197,
Theorem 12, proof lines 1436--1456, in the block-diagonal boundary-condition
coordinates used in arXiv:2011.12127, Section IV.C, lines 2126--2128. -/
theorem
    blockDiagonal_boundary_crossing_component_mem_groundSpace_of_pgvwc_comparison_of_sum_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (i : Fin N) (τ : Fin N → Fin d) (hi : N < i.val + L)
    (hSpan : WordTupleSpanTop A (N - i.val))
    (hmem :
      (∑ j : Fin r,
          cyclicRestrictₗ hN L i τ
            (groundSpaceMap (A j) N ((μ j) ^ N • X j))) ∈
        ⨆ j : Fin r, groundSpace (A j) L) :
    ∀ j : Fin r,
      cyclicRestrictₗ hN L i τ
          (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
        groundSpace (A j) L := by
  classical
  obtain ⟨C, hC⟩ :=
    blockDiagonal_boundary_crossing_pgvwc_comparison_of_sum_mem_iSup
      μ A hN hLN X i τ hi hSpan hmem
  intro j
  refine
    blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_crossing_matrix
      μ A hN hLN X j i τ hi ?_
  refine ⟨C j, ?_⟩
  intro β
  exact (hC j β).symm

end MPSTensor
