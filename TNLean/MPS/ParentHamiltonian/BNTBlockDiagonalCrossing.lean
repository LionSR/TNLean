/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixIdentities
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# Boundary-crossing cyclic interval equations for block-diagonal parent spaces

This file isolates the cyclic-interval step for a block component when the
interval crosses the boundary cut.  The input is the blockwise matrix identity
appearing in the boundary-closing part of arXiv:quant-ph/0608197, Theorem
2blocks.2.

The equality theorem here is conditional on the complementary-word identities
obtained from the source \(C^j,D^j,E^j\) comparison. The
Pérez-García--Verstraete--Wolf--Cirac (PGVWC) comparison theorem below proves
the componentwise periodic-chain conclusion once those identities are in the
boundary-crossing form used in Theorem 2blocks.2. Deriving these identities
from the source comparison is documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The complementary word for the cyclic window of length `m+2` beginning at
site `M` in a chain of length `M+1`.

For an outside configuration `τ`, this is
\[
  \rho=\tau_{m+1}\cdots\tau_{M-1}.
\] -/
def lastCrossingComplementWord {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (τ : Fin (M + 1) → Fin d) : List (Fin d) :=
  List.ofFn fun k : Fin (M + 1 - (m + 2)) =>
    τ ⟨k.val + (m + 1), by omega⟩

/-- At the cyclic window beginning at the last site, one block component has the
left-boundary trace form used in the blockwise coefficient comparison.

For an outside configuration with complementary word \(\rho\), the \(j\)-th
summand is the left-boundary component with
\[
  C^j_a=A^j_\rho A^j_a(\mu_j^{M+1}X_j).
\]
This is the component form of the boundary-crossing specialization of
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1436--1452. -/
theorem blockDiagonal_boundary_last_cyclicRestrict_component_eq_leftBoundaryComponent
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (τ : Fin (M + 1) → Fin d) (j : Fin r) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
        (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j)) =
      pgvwc07LeftBoundaryComponent (A j)
        (fun a : Fin d =>
          evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
            ((μ j) ^ (M + 1) • X j))
        m := by
  classical
  ext σ
  let middleWord : List (Fin d) := lastCrossingComplementWord hLen τ
  let W : Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    evalWord (A j) (List.ofFn (Fin.tail (Fin.init σ)))
  let b : Fin d := σ (Fin.last (m + 1))
  let a : Fin d := σ 0
  let Xj : Matrix (Fin (dim j)) (Fin (dim j)) ℂ := (μ j) ^ (M + 1) • X j
  have htail :
      (Fin.tail σ : Fin (m + 1) → Fin d) =
        Fin.snoc (Fin.tail (Fin.init σ)) b := by
    have hinit : Fin.init (Fin.tail σ) = Fin.tail (Fin.init σ) := by
      ext k
      rfl
    have hlast : (Fin.tail σ) (Fin.last m) = b := by
      rfl
    calc
      Fin.tail σ = Fin.snoc (Fin.init (Fin.tail σ)) ((Fin.tail σ) (Fin.last m)) :=
        (Fin.snoc_init_self (Fin.tail σ)).symm
      _ = Fin.snoc (Fin.tail (Fin.init σ)) b := by rw [hinit, hlast]
  have hEvalTail :
      evalWord (A j) (List.ofFn (Fin.tail σ)) = W * A j b := by
    rw [htail, evalWord_ofFn_snoc]
  simp only [cyclicRestrictₗ_apply, groundSpaceMap_apply,
    pgvwc07LeftBoundaryComponent]
  rw [evalWord_cyclicCfg_snoc (A := A j) (M := M) (L := m + 2)
    (by omega : 1 ≤ M) hLen (by omega : 1 < m + 2) σ τ]
  rw [init_evalWord_split (A := A j) (M := M) (L := m + 2)
    (by omega : 1 ≤ M) hLen (by omega : 1 < m + 2) σ τ]
  change
    Matrix.trace
        (((evalWord (A j) (List.ofFn (Fin.tail σ)) *
              evalWord (A j) middleWord) *
            A j a) * Xj) =
      Matrix.trace (A j b *
        (evalWord (A j) middleWord * A j a * Xj) * W)
  rw [hEvalTail]
  calc
    Matrix.trace
        (((W * A j b * evalWord (A j) middleWord) * A j a) * Xj)
        =
      Matrix.trace (W *
        (((A j b * evalWord (A j) middleWord) * A j a) * Xj)) := by
          simp [Matrix.mul_assoc]
    _ =
      Matrix.trace ((((A j b * evalWord (A j) middleWord) * A j a) * Xj) * W) :=
        Matrix.trace_mul_comm _ _
    _ =
      Matrix.trace (A j b *
        (evalWord (A j) middleWord * A j a * Xj) * W) := by
          simp [Matrix.mul_assoc]

/-- At the cyclic window beginning at the last site, the block-diagonal local
sum has the left-boundary trace form used in the blockwise coefficient
comparison.

Let the total chain have length \(M+1\), and let the local window have length
\(m+2\). The cyclic window beginning at \(M\) consists of the last site followed
by the first \(m+1\) sites. If the complementary word is
\[
  \rho=\tau_{m+1}\cdots\tau_{M-1},
\]
then the \(j\)-th summand has coefficients
\[
  \operatorname{tr}\!\left(
    A^j_b\, A^j_\rho A^j_a\,(\mu_j^{M+1}X_j)\, A^j_w
  \right),
\]
where the local word is \(a w b\). Thus the block sum is the sum of
left-boundary components with
\[
  C^j_a=A^j_\rho A^j_a\,(\mu_j^{M+1}X_j).
\]
This is the boundary-crossing cyclic specialization of the two trace
decompositions in arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines
1436--1452. -/
theorem blockDiagonal_boundary_last_cyclicRestrict_sum_eq_leftBoundaryComponents
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (τ : Fin (M + 1) → Fin d) :
    (∑ j : Fin r,
        cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
          (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j))) =
      ∑ j : Fin r,
        pgvwc07LeftBoundaryComponent (A j)
          (fun a : Fin d =>
            evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
              ((μ j) ^ (M + 1) • X j))
          m := by
  classical
  ext σ
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  exact congrFun
    (blockDiagonal_boundary_last_cyclicRestrict_component_eq_leftBoundaryComponent
      μ A hLen X τ j) σ

/-- The last boundary-crossing window gives the blockwise coefficient identity
from the local block-sum condition.

Let the complementary word be
\(\rho=\tau_{m+1}\cdots\tau_{M-1}\). Suppose that the block sum of the last
crossing-window restrictions lies in
\(\bigvee_jG_{m+2}(A^j)\), and that length-\(m\) simultaneous word tuples span
the product algebra. Then there are matrices \(E_j\) such that
\[
  A^j_b\bigl(A^j_\rho A^j_a(\mu_j^{M+1}X_j)\bigr)
    =A^j_bE_jA^j_a
\]
for every block \(j\) and all boundary letters \(a,b\).

This is the direct cyclic-window instance of the coefficient comparison
\(A_bC_a=A_bEA_a\) in arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines
1436--1452. -/
theorem blockDiagonal_boundary_last_coefficients_of_sum_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (τ : Fin (M + 1) → Fin d)
    (hSpan : WordTupleSpanTop A m)
    (hmem :
      (∑ j : Fin r,
          cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
            (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j))) ∈
        ⨆ j : Fin r, groundSpace (A j) (m + 2)) :
    ∃ E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ j : Fin r, ∀ a b : Fin d,
        A j b *
            (evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
              ((μ j) ^ (M + 1) • X j)) =
          A j b * E j * A j a := by
  classical
  let C : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j a =>
      evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
        ((μ j) ^ (M + 1) • X j)
  let ψ : NSiteSpace d (m + 2) :=
    ∑ j : Fin r,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
        (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j))
  have hψ :
      ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) m := by
    dsimp [ψ, C]
    exact blockDiagonal_boundary_last_cyclicRestrict_sum_eq_leftBoundaryComponents
      μ A hLen X τ
  exact pgvwc07_boundary_identities_of_leftBoundaryComponent_mem_iSup
    A hSpan C ψ hψ hmem

/-- The coefficient comparison puts each block component in the last
boundary-crossing local ground space.

Assume the block sum of the last crossing-window restrictions lies in
\(\bigvee_jG_{m+2}(A^j)\), and assume the length-\(m\) simultaneous word tuples
span the product algebra. Then the \(j\)-th cyclic restriction at the window
beginning at the last site is a vector in
\(G_{m+2}(A^j)\). This is the local membership consequence of the displayed
identity \(A_b^jC_a^j=A_b^jE^jA_a^j\) in arXiv:quant-ph/0608197,
Theorem 2blocks.2, proof lines 1436--1452. -/
theorem
    blockDiagonal_boundary_last_cyclicRestrict_component_mem_groundSpace_of_sum_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (τ : Fin (M + 1) → Fin d)
    (hSpan : WordTupleSpanTop A m)
    (hmem :
      (∑ j : Fin r,
          cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
            (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j))) ∈
        ⨆ j : Fin r, groundSpace (A j) (m + 2))
    (j : Fin r) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
        (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j)) ∈
      groundSpace (A j) (m + 2) := by
  classical
  obtain ⟨E, hE⟩ :=
    blockDiagonal_boundary_last_coefficients_of_sum_mem_iSup
      μ A hLen X τ hSpan hmem
  rw [blockDiagonal_boundary_last_cyclicRestrict_component_eq_leftBoundaryComponent
    μ A hLen X τ j]
  exact pgvwc07LeftBoundaryComponent_mem_groundSpace (A j)
    (fun a : Fin d =>
      evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
        ((μ j) ^ (M + 1) • X j))
    (E j) m (hE j)

/-- A block-diagonal chain vector supplies the local block-sum condition for the
last boundary-crossing coefficient identity.

Let \(B=\bigoplus_j\mu_jA^j\). If
\[
  \psi=\Gamma_{M+1}^{B}\!\left(\bigoplus_jX_j\right)
  \quad\text{and}\quad
  \psi\in\mathcal G_{M+1,m+2}(B),
\]
then the local constraint at the cyclic window beginning at \(M\), together
with the length-\(m\) simultaneous product span, gives matrices \(E_j\) with
\[
  A^j_b\bigl(A^j_\rho A^j_a(\mu_j^{M+1}X_j)\bigr)
    =A^j_bE_jA^j_a .
\]
Here \(\rho=\tau_{m+1}\cdots\tau_{M-1}\) is the complementary word determined
by the outside configuration. -/
theorem blockDiagonal_boundary_last_coefficients_of_blockDiagonal_chainGroundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    {ψ : NSiteSpace d (M + 1)}
    (hψ : ψ ∈
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) (m + 2) (M + 1))
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hψX :
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) (M + 1)
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
    (τ : Fin (M + 1) → Fin d)
    (hSpan : WordTupleSpanTop A m) :
    ∃ E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ j : Fin r, ∀ a b : Fin d,
        A j b *
            (evalWord (A j) (lastCrossingComplementWord hLen τ) * A j a *
              ((μ j) ^ (M + 1) • X j)) =
          A j b * E j * A j a := by
  have hmem :=
    blockDiagonal_boundary_cyclicRestrict_sum_mem_iSup_groundSpace
      μ A hμ (show 0 < M + 1 by omega) hLen hψ X hψX ⟨M, by omega⟩ τ
  exact blockDiagonal_boundary_last_coefficients_of_sum_mem_iSup
    μ A hLen X τ hSpan hmem

/-- A block-diagonal chain vector gives local membership for the last
boundary-crossing component.

Let \(B=\bigoplus_j\mu_jA^j\). If
\[
  \psi=\Gamma_{M+1}^{B}\!\left(\bigoplus_jX_j\right),
  \qquad
  \psi\in\mathcal G_{M+1,m+2}(B),
\]
then, for every outside configuration and every block \(j\), the restriction
of \(\Gamma_{M+1}^{A_j}(\mu_j^{M+1}X_j)\) at the cyclic window beginning at
the last site belongs to \(G_{m+2}(A^j)\). -/
theorem
    blockDiagonal_boundary_last_component_mem_groundSpace_of_blockDiagonal_chainGroundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    {ψ : NSiteSpace d (M + 1)}
    (hψ : ψ ∈
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) (m + 2) (M + 1))
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hψX :
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) (M + 1)
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)))
    (τ : Fin (M + 1) → Fin d)
    (hSpan : WordTupleSpanTop A m)
    (j : Fin r) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (m + 2) ⟨M, by omega⟩ τ
        (groundSpaceMap (A j) (M + 1) ((μ j) ^ (M + 1) • X j)) ∈
      groundSpace (A j) (m + 2) := by
  have hmem :=
    blockDiagonal_boundary_cyclicRestrict_sum_mem_iSup_groundSpace
      μ A hμ (show 0 < M + 1 by omega) hLen hψ X hψX ⟨M, by omega⟩ τ
  exact
    blockDiagonal_boundary_last_cyclicRestrict_component_mem_groundSpace_of_sum_mem_iSup
      μ A hLen X τ hSpan hmem j

/-- A boundary-crossing cyclic interval is local when the boundary matrix
satisfies the displayed boundary identity.

Let the cyclic interval beginning at \(i\) cross the cut, so \(N<i+L\). Write
\(a=i+L-N\). The sites \(0,\ldots,a-1\) carry the segment after the interval
wraps past the cut, the sites \(a,\ldots,i-1\) carry the outside
configuration, and the sites \(i,\ldots,N-1\) carry the segment before the
cut. If there is a matrix \(E\) such that, for every word \(\beta\) on the
segment \(0,\ldots,a-1\),
\[
  \mu_j^N X_j A^j_\beta
    A^j_{\tau_a}\cdots A^j_{\tau_{i-1}}
    =
  A^j_\beta E,
\]
then the restriction is the local vector \(\Gamma_L^{A_j}(E)\).

This is the matrix form of the boundary-closing comparison in
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1436--1456. -/
theorem blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_crossing_matrix
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (j : Fin r) (i : Fin N) (τ : Fin N → Fin d)
    (hi : N < i.val + L)
    (hIdentity : ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ β : Fin (i.val + L - N) → Fin d,
        (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
            evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
              τ ⟨i.val + L - N + k.val, by omega⟩) =
          evalWord (A j) (List.ofFn β) * E) :
    cyclicRestrictₗ hN L i τ
        (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
      groundSpace (A j) L := by
  classical
  rcases hIdentity with ⟨E, hE⟩
  rw [groundSpace, LinearMap.mem_range]
  refine ⟨E, ?_⟩
  ext σ
  let headWord : List (Fin d) := List.ofFn fun k : Fin (i.val + L - N) =>
    σ ⟨N - i.val + k.val, by omega⟩
  let middleWord : List (Fin d) := List.ofFn fun k : Fin (N - L) =>
    τ ⟨i.val + L - N + k.val, by omega⟩
  let tailWord : List (Fin d) := List.ofFn fun k : Fin (N - i.val) =>
    σ ⟨k.val, by omega⟩
  let Xj : Matrix (Fin (dim j)) (Fin (dim j)) ℂ := (μ j) ^ N • X j
  have hσ : List.ofFn σ = tailWord ++ headWord := by
    apply List.ext_getElem
    · simp [tailWord, headWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkL : k < L := by
        simpa only [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkTail : k < N - i.val
      · rw [List.getElem_append_left]
        · have htail :
              tailWord[k]'(by simpa [tailWord, List.length_ofFn] using hkTail) =
                σ ⟨k, hkL⟩ := by
            simp only [tailWord, List.getElem_ofFn]
          rw [htail]
        · simpa [tailWord, List.length_ofFn] using hkTail
      · rw [List.getElem_append_right]
        · have hidx : k - tailWord.length < headWord.length := by
            simp [tailWord, headWord, List.length_ofFn]
            omega
          have hhead :
              headWord[k - tailWord.length]'hidx = σ ⟨k, hkL⟩ := by
            simp only [headWord, List.getElem_ofFn]
            congr 1
            ext
            simp [tailWord, List.length_ofFn]
            omega
          rw [hhead]
        · simpa [tailWord, List.length_ofFn] using
            (show tailWord.length ≤ k by simp [tailWord, List.length_ofFn]; omega)
  have hcfg :
      List.ofFn (cyclicCfg hN L i σ τ) = headWord ++ (middleWord ++ tailWord) := by
    apply List.ext_getElem
    · simp [headWord, middleWord, tailWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by
        simpa only [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkHead : k < i.val + L - N
      · have hoff : (k + N - i.val) % N = N - i.val + k := by
          have hsum : k + N - i.val = N - i.val + k := by omega
          rw [hsum]
          exact Nat.mod_eq_of_lt (by omega)
        have hoffLt : (k + N - i.val) % N < L := by
          rw [hoff]
          omega
        rw [cyclicCfg, dif_pos hoffLt]
        rw [List.getElem_append_left]
        · have hhead :
              headWord[k]'(by simpa [headWord, List.length_ofFn] using hkHead) =
                σ ⟨N - i.val + k, by omega⟩ := by
            simp only [headWord, List.getElem_ofFn]
          rw [hhead]
          exact congrArg σ (Fin.ext hoff)
        · simpa [headWord, List.length_ofFn] using hkHead
      · by_cases hkMiddle : k < i.val
        · have hoff : (k + N - i.val) % N = k + N - i.val := by
            exact Nat.mod_eq_of_lt (by omega)
          have hoffNot : ¬(k + N - i.val) % N < L := by
            rw [hoff]
            omega
          rw [cyclicCfg, dif_neg hoffNot]
          rw [List.getElem_append_right]
          · rw [List.getElem_append_left]
            · have hidx :
                  k - headWord.length < middleWord.length := by
                simp [headWord, middleWord, List.length_ofFn]
                omega
              have hmiddle :
                  middleWord[k - headWord.length]'hidx = τ ⟨k, hkN⟩ := by
                simp only [middleWord, List.getElem_ofFn]
                congr 1
                ext
                simp [headWord, List.length_ofFn]
                omega
              rw [hmiddle]
            · simp [headWord, middleWord, List.length_ofFn]
              omega
          · simp [headWord, List.length_ofFn]
            omega
        · have hi_le_k : i.val ≤ k := by omega
          have hoff : (k + N - i.val) % N = k - i.val := by
            have hsum : k + N - i.val = k - i.val + N := by omega
            rw [hsum, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          have hoffLt : (k + N - i.val) % N < L := by
            rw [hoff]
            omega
          rw [cyclicCfg, dif_pos hoffLt]
          rw [List.getElem_append_right]
          · rw [List.getElem_append_right]
            · have hidx :
                  k - headWord.length - middleWord.length < tailWord.length := by
                simp [headWord, middleWord, tailWord, List.length_ofFn]
                omega
              have htail :
                  tailWord[k - headWord.length - middleWord.length]'hidx =
                    σ ⟨k - i.val, by omega⟩ := by
                simp only [tailWord, List.getElem_ofFn]
                congr 1
                ext
                simp [headWord, middleWord, List.length_ofFn]
                omega
              rw [htail]
              exact congrArg σ (Fin.ext hoff)
            · simp [headWord, middleWord, List.length_ofFn]
              omega
          · simp [headWord, List.length_ofFn]
            omega
  have hIdentityσ :
      (Xj * evalWord (A j) headWord) * evalWord (A j) middleWord =
        evalWord (A j) headWord * E := by
    simpa [Xj, headWord, middleWord] using
      hE (fun k : Fin (i.val + L - N) => σ ⟨N - i.val + k.val, by omega⟩)
  simp only [groundSpaceMap_apply, cyclicRestrictₗ_apply]
  rw [hσ, hcfg, evalWord_append, evalWord_append, evalWord_append]
  set H := evalWord (A j) headWord
  set M := evalWord (A j) middleWord
  set T := evalWord (A j) tailWord
  calc
    Matrix.trace ((T * H) * E) = Matrix.trace (T * (H * E)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace (T * ((Xj * H) * M)) := by
      rw [hIdentityσ]
    _ = Matrix.trace ((T * Xj) * (H * M)) := by
      rw [← Matrix.mul_assoc T (Xj * H) M]
      rw [← Matrix.mul_assoc T Xj H]
      rw [Matrix.mul_assoc (T * Xj) H M]
    _ = Matrix.trace ((H * M) * (T * Xj)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((H * M) * T) * Xj) := by
      rw [← Matrix.mul_assoc (H * M) T Xj]
    _ = Matrix.trace ((H * (M * T)) * Xj) := by
      rw [Matrix.mul_assoc H M T]
    _ = Matrix.trace ((H * (M * T)) * ((μ j) ^ N • X j)) := by
      rfl

/-- A right boundary-matrix identity on the segment after the interval wraps
past the cut gives the local constraint.

Let the cyclic interval beginning at \(i\) cross the cut, so \(N<i+L\), and put
\(a=i+L-N\). If there is a boundary matrix \(Y\) such that, for every word
\(\beta\) of length \(a\),
\[
  \mu_j^N X_j A^j_\beta=A^j_\beta Y
\]
then the restriction belongs to \(G_L(A_j)\).  The middle word
\[
  A^j_{\tau_a}\cdots A^j_{\tau_{i-1}}
\]
is incorporated into the boundary matrix
\(Y A^j_{\tau_a}\cdots A^j_{\tau_{i-1}}\).

This is the equation form of the boundary-closing reduction used after the
blockwise comparison in arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines
1454--1456. -/
theorem blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_boundary_identity
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (j : Fin r) (i : Fin N) (τ : Fin N → Fin d)
    (hi : N < i.val + L)
    (hBoundary : ∃ Y : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ β : Fin (i.val + L - N) → Fin d,
        ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) =
          evalWord (A j) (List.ofFn β) * Y) :
    cyclicRestrictₗ hN L i τ
        (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
      groundSpace (A j) L := by
  rcases hBoundary with ⟨Y, hY⟩
  refine blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_crossing_matrix
    μ A hN hLN X j i τ hi ?_
  refine ⟨Y * evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
    τ ⟨i.val + L - N + k.val, by omega⟩), ?_⟩
  intro β
  calc
    (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
          evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
            τ ⟨i.val + L - N + k.val, by omega⟩)
        =
      (evalWord (A j) (List.ofFn β) * Y) *
          evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
            τ ⟨i.val + L - N + k.val, by omega⟩) := by
          rw [hY β]
    _ =
      evalWord (A j) (List.ofFn β) *
        (Y * evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
          τ ⟨i.val + L - N + k.val, by omega⟩)) := by
          rw [Matrix.mul_assoc]

/-- Right boundary-matrix identities give the componentwise periodic
constraints.

Fix block-diagonal boundary conditions \(X_j\).  For every boundary-crossing
cyclic interval \(N<i+L\), put \(a=i+L-N\), and suppose that each block has a
boundary matrix \(Y_{j,i,\tau}\) such that, for every word \(\beta\) of length
\(a\),
\[
  \mu_j^N X_j A^j_\beta=A^j_\beta Y_{j,i,\tau}
\]
Then every component
\[
  \Gamma_N^{A_j}(\mu_j^N X_j)
\]
belongs to \(\mathcal G_{N,L}(A_j)\).

This isolates the equation which remains after comparing the \(j\)-th block
component in arXiv:quant-ph/0608197, Theorem 2blocks.2; the
non-boundary-crossing intervals are handled by the contiguous calculation. -/
theorem blockDiagonal_boundary_component_chainGroundSpace_of_boundary_identities
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hBoundary : ∀ (j : Fin r) (i : Fin N) (_ : Fin N → Fin d),
      N < i.val + L →
        ∃ Y : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ∀ β : Fin (i.val + L - N) → Fin d,
            ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) =
              evalWord (A j) (List.ofFn β) * Y) :
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  exact blockDiagonal_boundary_component_chainGroundSpace_of_crossing_windows
    μ A hN hLN X fun j i τ hi =>
      blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_boundary_identity
        μ A hN hLN X j i τ hi (hBoundary j i τ hi)

/-- Boundary-crossing matrix identities for a spanning complementary segment give
the componentwise periodic constraints.

For each boundary-crossing cyclic interval, assume that for every complementary
word \(\rho\) there is a matrix \(E\) such that, for every wrapped word
\(\beta\),
\[
  \mu_j^N X_jA^j_\beta A^j_\rho=A^j_\beta E
\]
If those complementary word products span the full matrix algebra in each
block, then the word-span stripping theorem gives a right boundary-matrix
identity, and the preceding theorem gives the
periodic-chain constraint. -/
theorem blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hSpan : ∀ j : Fin r, wordSpan (A j) (N - L) = ⊤)
    (hIdentity : ∀ (j : Fin r) (i : Fin N),
      N < i.val + L →
        ∀ ρ : Fin (N - L) → Fin d,
          ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
            ∀ β : Fin (i.val + L - N) → Fin d,
              (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                  evalWord (A j) (List.ofFn ρ) =
                evalWord (A j) (List.ofFn β) * E) :
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  exact blockDiagonal_boundary_component_chainGroundSpace_of_boundary_identities
    μ A hN hLN X fun j i τ hi =>
      exists_common_boundary_matrix_of_word_identities_of_wordSpan_eq_top
        (A := A j)
        (α := Fin (i.val + L - N) → Fin d)
        (K := N - L)
        (F := fun β => evalWord (A j) (List.ofFn β))
        (Z := fun β => ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β))
        (hSpan j)
        (hIdentity j i hi)

/-- Boundary-crossing matrix identities over a long complementary segment give
the componentwise periodic constraints under block injectivity and the
normalization equation.

When \(L+L_0\le N\), the complementary segment has length at least \(L_0\).
Homogeneous word-span propagation then supplies the full matrix algebra in each
block, so the spanning complementary-identity statement applies. -/
theorem
    blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities_of_injective
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L₀ L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hBlk : ∀ j : Fin r, IsNBlkInjective (A j) L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hNlarge : L + L₀ ≤ N)
    (hIdentity : ∀ (j : Fin r) (i : Fin N),
      N < i.val + L →
        ∀ ρ : Fin (N - L) → Fin d,
          ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
            ∀ β : Fin (i.val + L - N) → Fin d,
              (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                  evalWord (A j) (List.ofFn ρ) =
                evalWord (A j) (List.ofFn β) * E) :
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  refine blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities
    μ A hN hLN X ?_ hIdentity
  intro j
  exact wordSpan_eq_top_of_ge_of_unital (A j) (hUnital j)
    ((wordSpan_eq_top_iff_isNBlkInjective (A j) L₀).mpr (hBlk j)) (by omega)

/-- PGVWC complementary-word comparisons give the componentwise periodic
constraints under block injectivity.

For each boundary-crossing interval beginning at \(i\), assume there are
matrices \(C^j_{i,\rho}\) indexed by complementary words such that, for every
wrapped word \(\beta\),
\[
  A^j_\beta C^j_{i,\rho}
  =
  \bigl((\mu_j^NX_j)A^j_\beta\bigr)A^j_\rho .
\]
The normalized PGVWC boundary calculation gives the complementary-word
identities used in the injective componentwise periodic-chain theorem.
This is the boundary-closing comparison in arXiv:quant-ph/0608197, Theorem
2blocks.2, proof lines 1446--1451, followed by the periodic conclusion in
lines 1454--1456.
-/
theorem
    blockDiagonal_boundary_component_chainGroundSpace_of_pgvwc_comparison_of_injective
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L₀ L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hBlk : ∀ j : Fin r, IsNBlkInjective (A j) L₀)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hNlarge : L + L₀ ≤ N)
    (C : ∀ (j : Fin r) (_ : Fin N),
      (Fin (N - L) → Fin d) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCompat : ∀ (j : Fin r) (i : Fin N),
      N < i.val + L →
        ∀ ρ : Fin (N - L) → Fin d, ∀ β : Fin (i.val + L - N) → Fin d,
          evalWord (A j) (List.ofFn β) * C j i ρ =
            (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
              evalWord (A j) (List.ofFn ρ)) :
    ∀ j : Fin r,
      groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  refine
    blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities_of_injective
      μ A hN hLN X hBlk hUnital hNlarge ?_
  intro j i hi ρ
  exact pgvwc07_complementary_word_boundary_identities_of_compatibility
    (A := A j) (K := i.val + L - N) (M := N - L)
    (X := ((μ j) ^ N • X j)) (C := C j i)
    (sum_evalWord_mul_conjTranspose_evalWord (A j) (hUnital j) (N - L))
    (hCompat j i hi) ρ

/-- PGVWC trace decompositions give the componentwise periodic constraints under
block injectivity.

For each boundary-crossing interval beginning at \(i\), assume there are
matrices \(C^j_{i,\rho}\) indexed by complementary words such that the two
trace decompositions agree for every wrapped word \(\beta\), complementary word
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
The normalized PGVWC boundary calculation then gives, for each block \(j\),
interval \(i\), and complementary word \(\rho\), a matrix \(E_{j,i,\rho}\)
such that, for every wrapped word \(\beta\),
\[
  ((\mu_j^NX_j)A^j_\beta)A^j_\rho=A^j_\beta E_{j,i,\rho}.
\]
These complementary-word identities give
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)\in\mathcal G_{N,L}(A_j).
\]
This is the boundary-crossing trace-decomposition form of
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1436--1456. -/
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
  exact pgvwc07_complementary_word_boundary_identities_of_trace_decomposition
    (A := A) (m := m) (K := i.val + L - N) (M := N - L) hTraceSpan
    (fun k => (μ k) ^ N • X k) (fun k => C k i) hUnital
    (hCoeff i hi) j ρ

/-- Complementary-word identities upgrade the block-diagonal boundary
representation to periodic block components.

Under the normalized BNT hypotheses, every vector in the block-diagonal
periodic chain space has block-diagonal boundary conditions \(X_j\).  If those
same boundary conditions satisfy the complementary-word identities which the
Pérez-García--Verstraete--Wolf--Cirac proof derives from the \(C^j,D^j,E^j\)
comparison: for every boundary-crossing interval \(i\), wrapped word
\(\beta\), and complementary word \(\rho\),
\[
  \mu_j^N X_jA^j_\beta A^j_\rho=A^j_\beta E_{j,i,\rho},
\]
then the component vectors
\[
  \Gamma_N^{A_j}(\mu_j^NX_j)
\]
belong to \(\mathcal G_{N,L}(A_j)\).

The complementary-word identities are assumptions of this theorem. The PGVWC
comparison theorem below gives the componentwise conclusion from the source
boundary-crossing form of these identities. Deriving these identities from the
source comparison is documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.

This result follows the block-diagonal boundary conditions of arXiv:2011.12127,
lines 2126--2128, and precedes the final equality in
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1454--1456. -/
theorem
    exists_blockDiagonal_boundary_chainGroundSpace_of_complementary_identities_bnt_c1
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
    (hIdentity :
      ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
        ∀ (j : Fin r) (i : Fin N),
          N < i.val + L →
            ∀ ρ : Fin (N - L) → Fin d,
              ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
                ∀ β : Fin (i.val + L - N) → Fin d,
                  (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                      evalWord (A j) (List.ofFn ρ) =
                    evalWord (A j) (List.ofFn β) * E) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈ chainGroundSpace (A j) L N := by
  classical
  obtain ⟨X, hψX, _hOpen⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_toTensorFromBlocks_of_bnt_unital_c1
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange hψ
  refine ⟨X, hψX, ?_⟩
  exact
    blockDiagonal_boundary_component_chainGroundSpace_of_complementary_word_identities_of_injective
      μ A hN hLN X hBlk hUnital hNlarge (hIdentity X hψX)

/-- Complementary-word identities give the block-diagonal periodic-chain
equality in the finite BNT range.

This theorem combines two steps of the source boundary-closing argument:
first obtain block-diagonal boundary conditions, then use the
Pérez-García--Verstraete--Wolf--Cirac complementary-word identities to put
each component vector in the corresponding periodic block chain space. The
hypothesis is the \(C,D,E\) comparison for every boundary-crossing interval; the
theorem does not assert that comparison. -/
theorem
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_complementary_identities
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
    (hIdentity :
      ∀ {ψ : NSiteSpace d N},
        ψ ∈ chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N →
        ∀ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) →
          ∀ (j : Fin r) (i : Fin N),
            N < i.val + L →
              ∀ ρ : Fin (N - L) → Fin d,
                ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
                  ∀ β : Fin (i.val + L - N) → Fin d,
                    (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                        evalWord (A j) (List.ofFn ρ) =
                      evalWord (A j) (List.ofFn β) * E) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        ⨆ j : Fin r, chainGroundSpace (A j) L N ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) N) := by
  exact
    chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_bnt_c1_blockBoundary
      μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
      (fun ψ hψ =>
        exists_blockDiagonal_boundary_chainGroundSpace_of_complementary_identities_bnt_c1
          μ A hμ hIrr hLeft hOverlap hBlocks hBlk hL₀ hUnital hN hL hLN hRange
          hNlarge hψ (fun X hψX => hIdentity hψ X hψX))

end MPSTensor
