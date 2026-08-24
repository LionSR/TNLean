/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionBoundaryDecomposition

/-!
# Block-diagonal intersection identities

Algebraic identities for the block-diagonal parent-Hamiltonian intersection
argument: the left-boundary trace decomposition, the blockwise boundary-matrix
compatibilities \(A_bC_a=D_bA_a\), and the one-step block-intersection
equality for the join of the block ground spaces.

## References

* arXiv:quant-ph/0608197, Theorem 12, proof around \(A_b C_a=D_b A_a\)
  and \(E=\sum_a C_a A_a^\dagger\).
* [Cirac--Perez-Garcia--Schuch--Verstraete 2021], Section IV.C, lines
  2120--2129.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Boundary-matrix compatibility from equality of the two coefficient
decompositions in the source block-diagonal intersection proof.

For fixed physical indices \(a,b\), the coefficient comparison in
Theorem 12 of arXiv:quant-ph/0608197 gives
\[
  \sum_j \operatorname{tr}\!\left(
    A^j_b C^j_a A^j_{i_2}\cdots A^j_{i_m}\right)
  =
  \sum_j \operatorname{tr}\!\left(
    D^j_b A^j_a A^j_{i_2}\cdots A^j_{i_m}\right)
\]
for every middle word.  Under the common word-span condition, this implies
\[
  A^j_b C^j_a=D^j_b A^j_a
\]
for every block \(j\).
-/
theorem pgvwc07_blockwise_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m : ℕ} (hSpan : WordTupleSpanTop A m)
    (C Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ a b : Fin d, ∀ w : Fin m → Fin d,
      (∑ j : Fin r, Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ a b : Fin d, A j b * C j a = Dmat j b * A j a := by
  intro j a b
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => A k b * C k a) (fun k => Dmat k b * A k a) (hCoeff a b) j

/-- Word-valued boundary-matrix compatibility from equality of the two
coefficient decompositions in the proof of Theorem 12 of arXiv:quant-ph/0608197.

This is the same extraction as
`pgvwc07_blockwise_compatibility_of_trace_decomposition`, with the boundary
letters replaced by words. If, for every cut word \(\beta\), complementary
word \(\rho\), and middle word \(w\), the two trace decompositions agree,
then the blockwise matrices satisfy
\[
  A^j_\beta C^j_\rho=D^j_\beta A^j_\rho .
\]
This is the word form needed for the boundary-crossing comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_blockwise_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (Dmat : (j : Fin r) → (Fin K → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((Kraus.evalWord (A j) (List.ofFn β) * C j ρ) *
              Kraus.evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            ((Dmat j β * Kraus.evalWord (A j) (List.ofFn ρ)) *
              Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      Kraus.evalWord (A j) (List.ofFn β) * C j ρ =
        Dmat j β * Kraus.evalWord (A j) (List.ofFn ρ) := by
  intro j ρ β
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => Kraus.evalWord (A k) (List.ofFn β) * C k ρ)
    (fun k => Dmat k β * Kraus.evalWord (A k) (List.ofFn ρ))
    (hCoeff ρ β) j

/-- Fixed complementary-word compatibility from equality of the two coefficient
decompositions in the proof of Theorem 12 of arXiv:quant-ph/0608197.

Fix a complementary word \(\rho\). If, for every cut word \(\beta\) and
middle word \(w\), the trace decompositions agree with
\[
  D^j_\beta=X_jA^j_\beta ,
\]
then the blockwise matrices satisfy
\[
  A^j_\beta C^j_\rho=(X_jA^j_\beta)A^j_\rho .
\]
This is the fixed-\(\rho\) form of the comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_fixed_complementary_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (ρ : Fin M → Fin d)
    (hCoeff : ∀ β : Fin K → Fin d, ∀ w : Fin m → Fin d,
      (∑ j : Fin r,
        Matrix.trace
          ((Kraus.evalWord (A j) (List.ofFn β) * C j) *
            Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r,
        Matrix.trace
          (((X j * Kraus.evalWord (A j) (List.ofFn β)) *
              Kraus.evalWord (A j) (List.ofFn ρ)) *
            Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ β : Fin K → Fin d,
      Kraus.evalWord (A j) (List.ofFn β) * C j =
        (X j * Kraus.evalWord (A j) (List.ofFn β)) *
          Kraus.evalWord (A j) (List.ofFn ρ) := by
  intro j β
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => Kraus.evalWord (A k) (List.ofFn β) * C k)
    (fun k =>
      (X k * Kraus.evalWord (A k) (List.ofFn β)) * Kraus.evalWord (A k) (List.ofFn ρ))
    (hCoeff β) j

/-- Word-valued compatibility for a block-diagonal boundary matrix.

Assume the right trace decomposition has
\[
  D^j_\beta=(X_jA^j_\beta).
\]
Then the word-valued trace comparison gives
\[
  A^j_\beta C^j_\rho=(X_jA^j_\beta)A^j_\rho .
\]
This is the exact compatibility hypothesis used by the complementary-word
boundary theorem, following the boundary-crossing comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_complementary_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((Kraus.evalWord (A j) (List.ofFn β) * C j ρ) *
              Kraus.evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((X j * Kraus.evalWord (A j) (List.ofFn β)) *
                Kraus.evalWord (A j) (List.ofFn ρ)) *
              Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      Kraus.evalWord (A j) (List.ofFn β) * C j ρ =
        (X j * Kraus.evalWord (A j) (List.ofFn β)) *
          Kraus.evalWord (A j) (List.ofFn ρ) := by
  exact
    pgvwc07_blockwise_word_compatibility_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan C
      (fun j β => X j * Kraus.evalWord (A j) (List.ofFn β)) hCoeff

/-- Complementary-word boundary identities from the source trace decompositions.

Assume the right trace decomposition has
\[
  D^j_\beta=X_jA^j_\beta .
\]
If the two trace decompositions agree for every cut word \(\beta\),
complementary word \(\rho\), and middle word \(w\), then the normalization
\(\sum_\rho A^j_\rho A^{j\dagger}_\rho=I\) and the compatibility identity give,
for every block \(j\) and complementary word \(\rho\), a matrix \(E_{j,\rho}\)
such that
\[
  (X_jA^j_\beta)A^j_\rho=A^j_\beta E_{j,\rho}.
\]
This is the word-valued form of arXiv:quant-ph/0608197, Theorem 12,
proof lines 1446--1451.

**Local fix (adjoint correction):** The source line writes
\(E^j=\sum_k C^j_kA^j_k\), while the normalization step uses
\(\sum_k A^j_kA^{j\dagger}_k=I\). The local identity uses the adjointed
matrix \(E^j=\sum_k C^j_kA^{j\dagger}_k\), as recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem pgvwc07_complementary_word_boundary_identities_of_trace_decomposition
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
            ((Kraus.evalWord (A j) (List.ofFn β) * C j ρ) *
              Kraus.evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((X j * Kraus.evalWord (A j) (List.ofFn β)) *
                Kraus.evalWord (A j) (List.ofFn ρ)) *
              Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d,
      ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ∀ β : Fin K → Fin d,
          (X j * Kraus.evalWord (A j) (List.ofFn β)) *
              Kraus.evalWord (A j) (List.ofFn ρ) =
            Kraus.evalWord (A j) (List.ofFn β) * E := by
  intro j ρ
  exact pgvwc07_complementary_word_boundary_identities_of_compatibility
    (A := A j) (K := K) (M := M) (X := X j) (C := C j)
    (sum_evalWord_mul_conjTranspose_evalWord (A j) (hUnital j) M)
    ((pgvwc07_complementary_word_compatibility_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan X C hCoeff) j)
    ρ

/-- The composed open-segment step from the trace decompositions to
membership in the supremum of block ground spaces.

For a vector with left-boundary trace decomposition
\[
  \psi=\sum_j\alpha_j,\qquad
  \alpha_j(i_1,\ldots,i_{n+2})
    =\operatorname{tr}(A^j_{i_{n+2}}C^j_{i_1}A^j_{i_2}\cdots A^j_{i_{n+1}}),
\]
the trace-decomposition equality, the common word-span hypothesis, and the
normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I
\]
imply
\[
  \psi\in \bigvee_j G_{n+2}(A^j).
\]
This is the local membership step in
Theorem 12 of arXiv:quant-ph/0608197, proof lines 1446--1452.

**Local fix (missing adjoint):** The printed definition
\(E^j=\sum_a C_a^jA_a^j\) at line 1449 omits the adjoint required by the
right-canonical identity used in the calculation. Here
\(E^j=\sum_a C_a^jA_a^{j\dagger}\). See
`docs/paper-gaps/pgvwc07_common_identity_coefficients.tex`. -/
theorem pgvwc07_mem_iSup_groundSpace_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (C Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hCoeff : ∀ a b : Fin d, ∀ w : Fin n → Fin d,
      (∑ j : Fin r, Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w))))
    (ψ : NSiteSpace d (n + 2))
    (hψ : ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rw [hψ]
  let E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => ∑ a : Fin d, C j a * (A j a)ᴴ
  have hCompat :
      ∀ j : Fin r, ∀ a b : Fin d, A j b * C j a = Dmat j b * A j a :=
    pgvwc07_blockwise_compatibility_of_trace_decomposition A hSpan C Dmat hCoeff
  have hACE : ∀ j : Fin r, ∀ a b : Fin d,
      A j b * C j a = A j b * E j * A j a := by
    intro j
    exact (pgvwc07_boundary_matrix_identities_of_compatibility
      (A j) (C j) (Dmat j) (hUnital j) (hCompat j)).2
  exact pgvwc07_sum_leftBoundaryComponents_mem_iSup_groundSpace A C E n hACE

/-- The two block-ground-space restrictions produce boundary matrices \(C^j_a\)
and \(D^j_b\) with the left-boundary expansion
\[
  \psi=\sum_j \alpha_j,\qquad
  \alpha_j(i_1,\ldots,i_{n+2})
  =
  \operatorname{tr}(A^j_{i_{n+2}} C^j_{i_1}
    A^j_{i_2}\cdots A^j_{i_{n+1}}),
\]
and whose trace decompositions agree:
\[
  \sum_j\operatorname{tr}(A^j_b C^j_a A^j_w)
  =
  \sum_j\operatorname{tr}(D^j_b A^j_a A^j_w).
\]
This is the corresponding step in arXiv:quant-ph/0608197, Theorem 12,
proof lines 1442--1452. -/
theorem pgvwc07_trace_decompositions_of_iSup_restrictions
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (ψ : NSiteSpace d (n + 2))
    (hLeft : ∀ b : Fin d,
      restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1))
    (hRight : ∀ a : Fin d,
      restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) :
    ∃ C : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
    ∃ Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n ∧
      ∀ a b : Fin d, ∀ w : Fin n → Fin d,
        (∑ j : Fin r,
          Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w))) := by
  classical
  have hRightDecomp : ∀ a : Fin d,
      ∃ φ : (j : Fin r) → NSiteSpace d (n + 1),
        (∀ j : Fin r, φ j ∈ groundSpace (A j) (n + 1)) ∧
          restrictFirst ψ a = ∑ j : Fin r, φ j := by
    intro a
    obtain ⟨φ, hφmem, hφsum⟩ :=
      (Submodule.mem_iSup_iff_exists_finsupp
        (fun j : Fin r => groundSpace (A j) (n + 1)) (restrictFirst ψ a)).mp
        (hRight a)
    refine ⟨fun j => φ j, hφmem, ?_⟩
    simpa [Finsupp.sum_fintype] using hφsum.symm
  choose φ hφmem hφsum using hRightDecomp
  have hRightMatrix : ∀ j : Fin r, ∀ a : Fin d,
      ∃ C : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        φ a j = groundSpaceMap (A j) (n + 1) C := by
    intro j a
    have hmem := hφmem a j
    rw [groundSpace, LinearMap.mem_range] at hmem
    rcases hmem with ⟨C, hC⟩
    exact ⟨C, hC.symm⟩
  choose C hC using hRightMatrix
  have hLeftDecomp : ∀ b : Fin d,
      ∃ χ : (j : Fin r) → NSiteSpace d (n + 1),
        (∀ j : Fin r, χ j ∈ groundSpace (A j) (n + 1)) ∧
          restrictLast ψ b = ∑ j : Fin r, χ j := by
    intro b
    obtain ⟨χ, hχmem, hχsum⟩ :=
      (Submodule.mem_iSup_iff_exists_finsupp
        (fun j : Fin r => groundSpace (A j) (n + 1)) (restrictLast ψ b)).mp
        (hLeft b)
    refine ⟨fun j => χ j, hχmem, ?_⟩
    simpa [Finsupp.sum_fintype] using hχsum.symm
  choose χ hχmem hχsum using hLeftDecomp
  have hLeftMatrix : ∀ j : Fin r, ∀ b : Fin d,
      ∃ Dmat : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        χ b j = groundSpaceMap (A j) (n + 1) Dmat := by
    intro j b
    have hmem := hχmem b j
    rw [groundSpace, LinearMap.mem_range] at hmem
    rcases hmem with ⟨Dmat, hDmat⟩
    exact ⟨Dmat, hDmat.symm⟩
  choose Dmat hDmat using hLeftMatrix
  have hψ :
      ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n := by
    apply eq_of_forall_restrictFirst_eq
    intro a
    calc
      restrictFirst ψ a = ∑ j : Fin r, φ a j := hφsum a
      _ = ∑ j : Fin r, groundSpaceMap (A j) (n + 1) (C j a) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            exact hC j a
      _ = ∑ j : Fin r, restrictFirst
            (pgvwc07LeftBoundaryComponent (A j) (C j) n) a := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [restrictFirst_pgvwc07LeftBoundaryComponent]
      _ = restrictFirst
            (∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) a := by
            ext σ
            simp [restrictFirst_apply]
  have hCoeff : ∀ a b : Fin d, ∀ w : Fin n → Fin d,
      (∑ j : Fin r,
        Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r,
        Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w))) := by
    intro a b w
    have hRightEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ j : Fin r,
            Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w)) := by
      calc
        ψ (Fin.cons a (Fin.snoc w b))
            = restrictFirst ψ a (Fin.snoc w b) := by rfl
        _ = (∑ j : Fin r, φ a j) (Fin.snoc w b) := by
              exact congrFun (hφsum a) (Fin.snoc w b)
        _ = ∑ j : Fin r, φ a j (Fin.snoc w b) := by simp
        _ = ∑ j : Fin r,
            Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hC j a]
              exact groundSpaceMap_snoc_trace_boundary (A j) (C j a) w b
    have hLeftEval :
        ψ (Fin.snoc (Fin.cons a w) b) =
          ∑ j : Fin r,
            Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w)) := by
      calc
        ψ (Fin.snoc (Fin.cons a w) b)
            = restrictLast ψ b (Fin.cons a w) := by rfl
        _ = (∑ j : Fin r, χ b j) (Fin.cons a w) := by
              exact congrFun (hχsum b) (Fin.cons a w)
        _ = ∑ j : Fin r, χ b j (Fin.cons a w) := by simp
        _ = ∑ j : Fin r,
            Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hDmat j b]
              exact groundSpaceMap_cons_trace_boundary (A j) (Dmat j b) a w
    calc
      (∑ j : Fin r,
        Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w)))
          = ψ (Fin.cons a (Fin.snoc w b)) := hRightEval.symm
      _ = ψ (Fin.snoc (Fin.cons a w) b) := by
            rw [Fin.cons_snoc_eq_snoc_cons]
      _ = ∑ j : Fin r,
        Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w)) := hLeftEval
  exact ⟨C, Dmat, hψ, hCoeff⟩

/-- One-step block intersection from block-ground-space restrictions:
if both one-boundary restrictions of \(\psi\) lie in
\(\bigvee_j G_{n+1}(A^j)\), then, under the common word-span and unital
hypotheses, \(\psi\in\bigvee_j G_{n+2}(A^j)\).  This is the restriction form of
the open-segment step in arXiv:quant-ph/0608197, Theorem 12, proof lines
1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (ψ : NSiteSpace d (n + 2))
    (hLeft : ∀ b : Fin d,
      restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1))
    (hRight : ∀ a : Fin d,
      restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rcases pgvwc07_trace_decompositions_of_iSup_restrictions A ψ hLeft hRight with
    ⟨C, Dmat, hψ, hCoeff⟩
  exact pgvwc07_mem_iSup_groundSpace_of_trace_decomposition
    A hSpan C Dmat hUnital hCoeff ψ hψ

/-- One-step block intersection as a restriction characterization.

Under the common word-span hypothesis and the normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I,
\]
membership of an \((n+2)\)-site vector in \(\bigvee_jG_{n+2}(A^j)\) is
equivalent to the two fixed-boundary conditions
\[
  \psi(-,b)\in\bigvee_jG_{n+1}(A^j),
  \qquad
  \psi(a,-)\in\bigvee_jG_{n+1}(A^j).
\]
This is the one-step block-intersection identity of
Theorem 12 of arXiv:quant-ph/0608197, proof lines 1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_iff_iSup_restrictions
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (ψ : NSiteSpace d (n + 2)) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) ↔
      (∀ b : Fin d,
        restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) ∧
      (∀ a : Fin d,
        restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) := by
  classical
  constructor
  · intro hψ
    constructor
    · intro b
      refine Submodule.iSup_induction
        (p := fun j : Fin r => groundSpace (A j) (n + 2))
        (motive := fun φ => restrictLast φ b ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inLeftGround (A j) (n + 1) hφ b)
      · change (0 : NSiteSpace d (n + 1)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        change ((fun σ : Fin (n + 1) → Fin d => φ (Fin.snoc σ b)) +
            fun σ : Fin (n + 1) → Fin d => ξ (Fin.snoc σ b)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.add_mem (⨆ j : Fin r, groundSpace (A j) (n + 1)) hφ hξ
    · intro a
      refine Submodule.iSup_induction
        (p := fun j : Fin r => groundSpace (A j) (n + 2))
        (motive := fun φ => restrictFirst φ a ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inRightGround (A j) (n + 1) hφ a)
      · change (0 : NSiteSpace d (n + 1)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        change ((fun σ : Fin (n + 1) → Fin d => φ (Fin.cons a σ)) +
            fun σ : Fin (n + 1) → Fin d => ξ (Fin.cons a σ)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.add_mem (⨆ j : Fin r, groundSpace (A j) (n + 1)) hφ hξ
  · intro hRestrict
    exact pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions
      A hSpan hUnital ψ hRestrict.1 hRestrict.2

/-- Subspace form of the one-step block intersection identity.

Let \(S_n=\bigvee_jG_{n+1}(A^j)\). Under the common word-span
hypothesis and the normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I,
\]
the \((n+2)\)-site block ground space is the intersection of the inverse
images of \(S_n\) under all fixed last-letter and fixed first-letter
restrictions.  This is the restriction-subspace form of
Theorem 12 of arXiv:quant-ph/0608197, proof lines 1442--1452. -/
theorem pgvwc07_iSup_groundSpace_eq_restriction_intersection
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  simpa [restrictLast, restrictFirst] using
    (pgvwc07_mem_iSup_groundSpace_iff_iSup_restrictions A hSpan hUnital ψ).symm

/-- Product spans give the one-step block-intersection identity as an internal
direct sum.

Let
\[
  S_{n+1}=\bigvee_jG_{n+1}(A^j).
\]
If the simultaneous block-word tuples span the full product algebra at lengths
\(n\), \(n+1\), and \(n+2\), and the blocks satisfy
\[
  \sum_a A^j_aA^{j\dagger}_a=I,
\]
then \(S_{n+1}\) and \(\bigvee_jG_{n+2}(A^j)\) are internal direct sums, and
\[
  \left(\bigcap_b\operatorname{Res}_{-,b}^{-1}S_{n+1}\right)
  \cap
  \left(\bigcap_a\operatorname{Res}_{a,-}^{-1}S_{n+1}\right)
  =
  \bigvee_jG_{n+2}(A^j).
\]
This is the one-step block-intersection formula of
Theorem 12 of arXiv:quant-ph/0608197 together with the directness needed to
read the joins as direct sums of local block
spaces. -/
theorem pgvwc07_directSum_restriction_intersection_of_wordTupleSpanTop
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hSpan_succ : WordTupleSpanTop A (n + 1))
    (hSpan_succ_succ : WordTupleSpanTop A (n + 2))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    iSupIndep (fun j : Fin r => groundSpace (A j) (n + 1)) ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) (n + 2)) ∧
        ((⨅ b : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
          (⨅ a : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
          ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact ⟨groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan_succ,
    groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan_succ_succ,
    pgvwc07_iSup_groundSpace_eq_restriction_intersection A hSpan hUnital⟩

/-- Period-window form of the one-step block intersection.

If a positive period and a complete residue window give full homogeneous
blockwise product spans, then the one-step block-intersection subspace equality
holds at every sufficiently large internal word length. -/
theorem pgvwc07_iSup_restriction_intersection_eventually_of_period_window
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod : WordTupleSpanTop A period)
    (hwindow : ∀ s : ℕ, s < period → WordTupleSpanTop A (start + s))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rcases wordTupleSpanTop_eventually_of_wordTupleSpanTop_period_window
      A hperiod_pos hperiod hwindow with
    ⟨L, hL⟩
  refine ⟨L, ?_⟩
  intro n hn
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A (hL n hn) hUnital

end MPSTensor
