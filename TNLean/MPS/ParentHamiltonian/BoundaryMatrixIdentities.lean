/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Boundary matrix identities

This file records the normalized matrix calculation used in the PGVWC
block-diagonal intersection proof.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 2blocks.2, proof around
  \(A_b C_a=D_b A_a\) and \(E=\sum_a C_a A_a^\dagger\).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Right normalization propagates from letters to words of any fixed length.

If
\[
  \sum_a A_aA_a^\dagger=I,
\]
then the same equation holds after replacing the letters by all words of
length \(L\):
\[
  \sum_\rho A_\rho A_\rho^\dagger=I.
\]
This is the iterated form of the normalization used in arXiv:quant-ph/0608197,
Theorem 2blocks.2, proof line 1450. -/
theorem sum_evalWord_mul_conjTranspose_evalWord
    (A : MPSTensor d D)
    (hRight : ∑ i : Fin d, A i * (A i)ᴴ = 1) :
    ∀ L : ℕ,
      ∑ ρ : Fin L → Fin d,
        evalWord A (List.ofFn ρ) * (evalWord A (List.ofFn ρ))ᴴ = 1 := by
  intro L
  induction L with
  | zero =>
      simp
  | succ L ih =>
      let e : Fin d × (Fin L → Fin d) ≃ (Fin (L + 1) → Fin d) :=
        Fin.consEquiv (fun _ => Fin d)
      calc
        ∑ ρ : Fin (L + 1) → Fin d,
            evalWord A (List.ofFn ρ) * (evalWord A (List.ofFn ρ))ᴴ
          = ∑ p : Fin d × (Fin L → Fin d),
              evalWord A (List.ofFn (e p)) * (evalWord A (List.ofFn (e p)))ᴴ := by
                simpa [e] using
                  (Fintype.sum_equiv e
                    (f := fun p : Fin d × (Fin L → Fin d) =>
                      evalWord A (List.ofFn (e p)) *
                        (evalWord A (List.ofFn (e p)))ᴴ)
                    (g := fun ρ : Fin (L + 1) → Fin d =>
                      evalWord A (List.ofFn ρ) * (evalWord A (List.ofFn ρ))ᴴ)
                    (by intro p; rfl)).symm
        _ = ∑ i : Fin d, ∑ τ : Fin L → Fin d,
              evalWord A (List.ofFn (e (i, τ))) *
                (evalWord A (List.ofFn (e (i, τ))))ᴴ := by
                rw [Fintype.sum_prod_type]
        _ = ∑ i : Fin d, A i * (A i)ᴴ := by
                refine Finset.sum_congr rfl ?_
                intro i _
                calc
                  ∑ τ : Fin L → Fin d,
                      evalWord A (List.ofFn (e (i, τ))) *
                        (evalWord A (List.ofFn (e (i, τ))))ᴴ
                    =
                  ∑ τ : Fin L → Fin d,
                      A i *
                        (evalWord A (List.ofFn τ) *
                          (evalWord A (List.ofFn τ))ᴴ) *
                        (A i)ᴴ := by
                        refine Finset.sum_congr rfl ?_
                        intro τ _
                        simp [e, Matrix.conjTranspose_mul, Matrix.mul_assoc]
                  _ =
                    A i *
                      (∑ τ : Fin L → Fin d,
                        evalWord A (List.ofFn τ) * (evalWord A (List.ofFn τ))ᴴ) *
                      (A i)ᴴ := by
                        have hsum_right :
                            ∑ τ : Fin L → Fin d,
                                A i *
                                  (evalWord A (List.ofFn τ) *
                                    (evalWord A (List.ofFn τ))ᴴ) *
                                  (A i)ᴴ
                              =
                            (∑ τ : Fin L → Fin d,
                                A i *
                                  (evalWord A (List.ofFn τ) *
                                    (evalWord A (List.ofFn τ))ᴴ)) *
                              (A i)ᴴ := by
                              simpa [Matrix.mul_assoc] using
                                (Finset.sum_mul
                                  (s := (Finset.univ : Finset (Fin L → Fin d)))
                                  (f := fun τ : Fin L → Fin d =>
                                    A i *
                                      (evalWord A (List.ofFn τ) *
                                        (evalWord A (List.ofFn τ))ᴴ))
                                  (a := (A i)ᴴ)).symm
                        have hsum_left :
                            ∑ τ : Fin L → Fin d,
                                A i *
                                  (evalWord A (List.ofFn τ) *
                                    (evalWord A (List.ofFn τ))ᴴ)
                              =
                            A i *
                              ∑ τ : Fin L → Fin d,
                                evalWord A (List.ofFn τ) * (evalWord A (List.ofFn τ))ᴴ := by
                              simpa [Matrix.mul_assoc] using
                                (Finset.mul_sum
                                  (s := (Finset.univ : Finset (Fin L → Fin d)))
                                  (a := A i)
                                  (f := fun τ : Fin L → Fin d =>
                                    evalWord A (List.ofFn τ) *
                                      (evalWord A (List.ofFn τ))ᴴ)).symm
                        rw [hsum_right, hsum_left]
                  _ = A i * (A i)ᴴ := by
                        rw [ih]
                        simp
        _ = 1 := hRight

/-- Two-index boundary-matrix identities in the PGVWC boundary comparison.

This abstracts the normalized matrix calculation in arXiv:quant-ph/0608197,
Theorem 2blocks.2, proof lines 1446--1451.

This is the same normalized calculation when the right-normalized family is
indexed by a finite set and the left family is indexed by an arbitrary set:
\[
  A_b C_a=D_b B_a,\qquad \sum_a B_aB_a^\dagger=I.
\]
Then, with \(E=\sum_a C_aB_a^\dagger\),
\[
  D_b=A_bE,\qquad A_bC_a=A_bEB_a.
\]
-/
theorem pgvwc07_boundary_matrix_identities_of_two_index_compatibility
    {ι κ : Type*} [Fintype κ]
    (A : ι → Matrix (Fin D) (Fin D) ℂ)
    (B C : κ → Matrix (Fin D) (Fin D) ℂ)
    (Dmat : ι → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : κ, B a * (B a)ᴴ = 1)
    (hCompat : ∀ a : κ, ∀ b : ι, A b * C a = Dmat b * B a) :
    (∀ b : ι, Dmat b = A b * (∑ a : κ, C a * (B a)ᴴ)) ∧
      (∀ a : κ, ∀ b : ι,
        A b * C a = A b * (∑ c : κ, C c * (B c)ᴴ) * B a) := by
  classical
  have hD : ∀ b : ι, Dmat b = A b * (∑ a : κ, C a * (B a)ᴴ) := by
    intro b
    calc
      Dmat b = Dmat b * 1 := by simp
      _ = Dmat b * (∑ a : κ, B a * (B a)ᴴ) := by rw [hUnital]
      _ = ∑ a : κ, Dmat b * (B a * (B a)ᴴ) := by
            rw [Matrix.mul_sum]
      _ = ∑ a : κ, (Dmat b * B a) * (B a)ᴴ := by
            exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_assoc]
      _ = ∑ a : κ, (A b * C a) * (B a)ᴴ := by
            exact Finset.sum_congr rfl fun a _ => by rw [← hCompat a b]
      _ = ∑ a : κ, A b * (C a * (B a)ᴴ) := by
            exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_assoc]
      _ = A b * (∑ a : κ, C a * (B a)ᴴ) := by
            rw [Matrix.mul_sum]
  refine ⟨hD, ?_⟩
  intro a b
  calc
    A b * C a = Dmat b * B a := hCompat a b
    _ = A b * (∑ c : κ, C c * (B c)ᴴ) * B a := by rw [hD b]

/-- Boundary-matrix identities in the PGVWC block-diagonal intersection proof,
for an arbitrary finite index set.

Assume
\[
  A_b C_a=D_b A_a
\]
for all indices \(a,b\), and assume the right normalization
\[
  \sum_a A_aA_a^\dagger=I.
\]
Then, with \(E=\sum_a C_aA_a^\dagger\),
\[
  D_b=A_bE,\qquad A_bC_a=A_bEA_a.
\]
-/
theorem pgvwc07_boundary_matrix_identities_of_indexed_compatibility
    {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin D) (Fin D) ℂ)
    (C Dmat : ι → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : ι, A a * (A a)ᴴ = 1)
    (hCompat : ∀ a b : ι, A b * C a = Dmat b * A a) :
    (∀ b : ι, Dmat b = A b * (∑ a : ι, C a * (A a)ᴴ)) ∧
      (∀ a b : ι,
        A b * C a = A b * (∑ c : ι, C c * (A c)ᴴ) * A a) := by
  exact pgvwc07_boundary_matrix_identities_of_two_index_compatibility
    A A C Dmat hUnital hCompat

/-- Boundary-matrix identities in the PGVWC block-diagonal intersection proof. -/
theorem pgvwc07_boundary_matrix_identities_of_compatibility
    (A : MPSTensor d D)
    (C Dmat : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    (hCompat : ∀ a b : Fin d, A b * C a = Dmat b * A a) :
    (∀ b : Fin d, Dmat b = A b * (∑ a : Fin d, C a * (A a)ᴴ)) ∧
      (∀ a b : Fin d,
        A b * C a = A b * (∑ c : Fin d, C c * (A c)ᴴ) * A a) := by
  exact pgvwc07_boundary_matrix_identities_of_indexed_compatibility
    A C Dmat hUnital hCompat

/-- Word-indexed boundary-matrix identities in the PGVWC boundary comparison.

This is the same normalized matrix calculation with the finite index set taken
to be words of a fixed length:
\[
  A_\beta=A_{\beta_1}\cdots A_{\beta_K}.
\]
It is the algebraic form needed before the complementary-word boundary identity
in the periodic block-diagonal argument. -/
theorem pgvwc07_boundary_word_matrix_identities_of_compatibility
    (A : MPSTensor d D) {K : ℕ}
    (C Dmat : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hUnital :
      ∑ β : Fin K → Fin d,
        evalWord A (List.ofFn β) * (evalWord A (List.ofFn β))ᴴ = 1)
    (hCompat : ∀ α β : Fin K → Fin d,
      evalWord A (List.ofFn β) * C α = Dmat β * evalWord A (List.ofFn α)) :
    (∀ β : Fin K → Fin d,
      Dmat β =
        evalWord A (List.ofFn β) *
          (∑ α : Fin K → Fin d, C α * (evalWord A (List.ofFn α))ᴴ)) ∧
      (∀ α β : Fin K → Fin d,
        evalWord A (List.ofFn β) * C α =
          evalWord A (List.ofFn β) *
            (∑ γ : Fin K → Fin d, C γ * (evalWord A (List.ofFn γ))ᴴ) *
              evalWord A (List.ofFn α)) := by
  exact pgvwc07_boundary_matrix_identities_of_indexed_compatibility
    (fun β : Fin K → Fin d => evalWord A (List.ofFn β)) C Dmat hUnital hCompat

/-- Two-length word-indexed boundary-matrix identities.

This is the word-alphabet form of the PGVWC07 calculation in
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1446--1451.

The two index sets are words of lengths \(K\) and \(M\):
\[
  A_\beta C_\rho=D_\beta B_\rho,\qquad
  \sum_\rho B_\rho B_\rho^\dagger=I.
\]
This is the word form needed when a boundary-crossing cyclic interval has a
wrapped word and a complementary word of different lengths. -/
theorem pgvwc07_boundary_word_matrix_identities_of_two_length_compatibility
    (A : MPSTensor d D) {K M : ℕ}
    (C : (Fin M → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (Dmat : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hUnital :
      ∑ ρ : Fin M → Fin d,
        evalWord A (List.ofFn ρ) * (evalWord A (List.ofFn ρ))ᴴ = 1)
    (hCompat : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      evalWord A (List.ofFn β) * C ρ =
        Dmat β * evalWord A (List.ofFn ρ)) :
    (∀ β : Fin K → Fin d,
      Dmat β =
        evalWord A (List.ofFn β) *
          (∑ ρ : Fin M → Fin d, C ρ * (evalWord A (List.ofFn ρ))ᴴ)) ∧
      (∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
        evalWord A (List.ofFn β) * C ρ =
          evalWord A (List.ofFn β) *
            (∑ γ : Fin M → Fin d, C γ * (evalWord A (List.ofFn γ))ᴴ) *
              evalWord A (List.ofFn ρ)) := by
  exact pgvwc07_boundary_matrix_identities_of_two_index_compatibility
    (fun β : Fin K → Fin d => evalWord A (List.ofFn β))
    (fun ρ : Fin M → Fin d => evalWord A (List.ofFn ρ))
    C Dmat hUnital hCompat

/-- Complementary-word boundary identities from a two-length PGVWC comparison.

This is the boundary-crossing form of the PGVWC07 calculation in
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1446--1451.

Let \(X\in M_D(\mathbb C)\) be a matrix. Assume that for every complementary
word \(\rho\) and wrapped word \(\beta\),
\[
  A_\beta C_\rho=(X A_\beta)A_\rho,
\]
and that the complementary-word products are right-normalized. Then, for every
complementary word \(\rho\), there is a matrix \(E_\rho\) such that for every
wrapped word \(\beta\),
\[
  (X A_\beta)A_\rho=A_\beta E_\rho
\]. -/
theorem pgvwc07_complementary_word_boundary_identities_of_compatibility
    (A : MPSTensor d D) {K M : ℕ}
    (X : Matrix (Fin D) (Fin D) ℂ)
    (C : (Fin M → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hUnital :
      ∑ ρ : Fin M → Fin d,
        evalWord A (List.ofFn ρ) * (evalWord A (List.ofFn ρ))ᴴ = 1)
    (hCompat : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      evalWord A (List.ofFn β) * C ρ =
        (X * evalWord A (List.ofFn β)) * evalWord A (List.ofFn ρ)) :
    ∀ ρ : Fin M → Fin d,
      ∃ E : Matrix (Fin D) (Fin D) ℂ,
        ∀ β : Fin K → Fin d,
          (X * evalWord A (List.ofFn β)) * evalWord A (List.ofFn ρ) =
            evalWord A (List.ofFn β) * E := by
  classical
  intro ρ
  let E₀ : Matrix (Fin D) (Fin D) ℂ :=
    ∑ γ : Fin M → Fin d, C γ * (evalWord A (List.ofFn γ))ᴴ
  refine ⟨E₀ * evalWord A (List.ofFn ρ), ?_⟩
  intro β
  have hRect :
      evalWord A (List.ofFn β) * C ρ =
        evalWord A (List.ofFn β) * E₀ * evalWord A (List.ofFn ρ) :=
    (pgvwc07_boundary_word_matrix_identities_of_two_length_compatibility
      (A := A) (C := C)
      (Dmat := fun β : Fin K → Fin d => X * evalWord A (List.ofFn β))
      hUnital hCompat).2 ρ β
  calc
    (X * evalWord A (List.ofFn β)) * evalWord A (List.ofFn ρ)
        = evalWord A (List.ofFn β) * C ρ := (hCompat ρ β).symm
    _ = evalWord A (List.ofFn β) * E₀ * evalWord A (List.ofFn ρ) := hRect
    _ = evalWord A (List.ofFn β) * (E₀ * evalWord A (List.ofFn ρ)) := by
          rw [Matrix.mul_assoc]

end MPSTensor
