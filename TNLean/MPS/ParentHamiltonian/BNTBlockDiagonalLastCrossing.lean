/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.ParentHamiltonian.WrappingWindow

/-!
# The last boundary-crossing interval for block-diagonal parent spaces

This file records the last-cut specialization of the boundary-crossing
coefficient comparison in arXiv:quant-ph/0608197, Theorem 12.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The complementary word for the cyclic window of length \(m+2\) beginning at
site \(M\) in a chain of length \(M+1\).

For an outside configuration \(\tau\), this is
\[
  \rho=\tau_{m+1}\cdots\tau_{M-1}.
\] -/
def lastCrossingComplementWord {m M : ℕ} (hLen : m + 2 ≤ M + 1)
    (τ : Fin (M + 1) → Fin d) : List (Fin d) :=
  List.ofFn fun k : Fin (M + 1 - (m + 2)) =>
    τ ⟨k.val + (m + 1), by omega⟩

/-- At the cyclic window beginning at the last site, one block summand has the
left-boundary trace form used in the blockwise coefficient comparison.

For an outside configuration with complementary word \(\rho\), the \(j\)-th
summand is the left-boundary summand with
\[
  C^j_a=A^j_\rho A^j_a(\mu_j^{M+1}X_j).
\]
This is the block-summand form of the boundary-crossing specialization of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1436--1452. -/
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
left-boundary summands with
\[
  C^j_a=A^j_\rho A^j_a\,(\mu_j^{M+1}X_j).
\]
This is the boundary-crossing specialization of the two trace
decompositions in arXiv:quant-ph/0608197, Theorem 12, proof lines
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
\(A_bC_a=A_bEA_a\) in arXiv:quant-ph/0608197, Theorem 12, proof lines
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
Theorem 12, proof lines 1436--1452. -/
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

end MPSTensor
