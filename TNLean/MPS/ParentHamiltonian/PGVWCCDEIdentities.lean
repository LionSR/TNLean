/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty

/-!
# \(C^j,D^j,E^j\) matrix identities from trace decompositions

This file derives the word-valued \(C^j,D^j,E^j\) matrix identities from
matching left and right block trace decompositions in arXiv:quant-ph/0608197,
Theorem 12, proof lines 1446--1451.

In the source proof the auxiliary matrices are indexed by the boundary indices
\(i_1\) and \(i_{m+1}\). The variables \(\beta\) and \(\rho\) below are the
cut-adapted word coordinates used to express the same comparison after a
periodic interval has been opened at the chosen cut.

The formula for \(E^j\) uses the adjointed word product
\[
  E^j=\sum_\rho C^j_\rho (A^j_\rho)^\dagger ,
\]
which is the form compatible with the normalization
\(\sum_\rho A^j_\rho(A^j_\rho)^\dagger=I\). The source line omits this adjoint;
the correction is recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Explicit PGVWC \(C^j,D^j,E^j\) identities from the trace decompositions.

Assume the right trace decomposition has
\[
  D^j_\beta=X_jA^j_\beta .
\]
If the two trace decompositions agree for every cut word \(\beta\),
complementary word \(\rho\), and middle word \(w\), then for every block \(j\)
there is a matrix
\[
  E^j=\sum_\rho C^j_\rho A^{j\dagger}_\rho
\]
such that
\[
  D^j_\beta=A^j_\beta E^j,\qquad
  A^j_\beta C^j_\rho=A^j_\beta E^jA^j_\rho .
\]
This is the word-valued form of arXiv:quant-ph/0608197, Theorem 12, proof
lines 1446--1451. The source notation is \(C^j_{i_1}\) and
\(D^j_{i_{m+1}}\); the parameters \(\beta\) and \(\rho\) are the local word
coordinates used here to state the same identity for an opened cyclic interval.

**Local fix (adjoint correction):** The source line writes
\(E^j=\sum_k C^j_kA^j_k\), while the normalization step uses
\(\sum_k A^j_kA^{j\dagger}_k=I\). The formal statement uses the adjointed
matrix \(E^j=\sum_k C^j_kA^{j\dagger}_k\), as recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem pgvwc07_complementary_word_cde_identities_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) * C j ρ) *
              evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((X j * evalWord (A j) (List.ofFn β)) *
                evalWord (A j) (List.ofFn ρ)) *
              evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r,
      ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        E = (∑ ρ : Fin M → Fin d, C j ρ * (evalWord (A j) (List.ofFn ρ))ᴴ) ∧
        (∀ β : Fin K → Fin d,
          X j * evalWord (A j) (List.ofFn β) =
            evalWord (A j) (List.ofFn β) * E) ∧
        (∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
          evalWord (A j) (List.ofFn β) * C j ρ =
            evalWord (A j) (List.ofFn β) * E *
              evalWord (A j) (List.ofFn ρ)) := by
  classical
  intro j
  let E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    ∑ ρ : Fin M → Fin d, C j ρ * (evalWord (A j) (List.ofFn ρ))ᴴ
  have hCompat :
      ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
        evalWord (A j) (List.ofFn β) * C j ρ =
          (X j * evalWord (A j) (List.ofFn β)) *
            evalWord (A j) (List.ofFn ρ) :=
    (pgvwc07_complementary_word_compatibility_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan X C hCoeff) j
  have hIds :=
    pgvwc07_boundary_word_matrix_identities_of_two_length_compatibility
      (A := A j) (K := K) (M := M) (C := C j)
      (Dmat := fun β : Fin K → Fin d => X j * evalWord (A j) (List.ofFn β))
      (sum_evalWord_mul_conjTranspose_evalWord (A j) (hUnital j) M)
      hCompat
  refine ⟨E, rfl, ?_, ?_⟩
  · intro β
    simpa [E] using hIds.1 β
  · intro ρ β
    simpa [E] using hIds.2 ρ β

/-- Block-diagonal boundary specialization of the PGVWC \(C^j,D^j,E^j\)
identities.

This is arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451,
specialized to the block-diagonal periodic boundary matrix
\[
  D^j_\beta=(\mu_j^NX_j)A^j_\beta .
\]
The conclusion gives a single matrix \(E^j\), independent of \(\rho\), such
that
\[
  (\mu_j^NX_j)A^j_\beta=A^j_\beta E^j,\qquad
  A^j_\beta C^j_\rho=A^j_\beta E^jA^j_\rho .
\]

The words \(\beta\) and \(\rho\) are the local coordinates obtained by opening
a boundary-crossing interval; the source proof uses \(C^j_{i_1}\) and
\(D^j_{i_{m+1}}\).

**Local fix (adjoint correction):** As in the unspecialized theorem, the
formal matrix is \(E^j=\sum_\rho C^j_\rho(A^j_\rho)^\dagger\), matching the
normalization \(\sum_\rho A^j_\rho(A^j_\rho)^\dagger=I\); the source line omits
the adjoint. Documented in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem pgvwc07_complementary_word_cde_identities_of_block_boundary_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M N : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) * C j ρ) *
              evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
                evalWord (A j) (List.ofFn ρ)) *
              evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r,
      ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        E = (∑ ρ : Fin M → Fin d, C j ρ * (evalWord (A j) (List.ofFn ρ))ᴴ) ∧
        (∀ β : Fin K → Fin d,
          ((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β) =
            evalWord (A j) (List.ofFn β) * E) ∧
        (∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
          evalWord (A j) (List.ofFn β) * C j ρ =
            evalWord (A j) (List.ofFn β) * E *
              evalWord (A j) (List.ofFn ρ)) := by
  exact
    pgvwc07_complementary_word_cde_identities_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan
      (fun j => (μ j) ^ N • X j) C hUnital hCoeff

end MPSTensor
