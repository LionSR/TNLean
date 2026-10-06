/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteAlphabetRows

/-!
# Residual functions of Boolean phase selectors

The product of two coefficient matrices with bond sizes `p` and `q`, followed
by an affine scalar change, factors through a bond of size `card p * card q + 1`.
When its entries are zero or one, the finite-alphabet row theorem applies.
For two bonds of size two this gives at most 32 residual functions.

This is a step of the additional diagonal circuit argument, not the general
conditioning theorem of arXiv:2508.08160. See
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`, Lemma 2.
-/

open scoped BigOperators
namespace Matrix
variable {K m n p q : Type*} [Field K] [Fintype p] [Fintype q]

/-- An affine function of the entrywise product of two bond factorizations
factors through the product bond together with one constant coordinate. -/
theorem exists_hadamard_affine_factorization (A : Matrix m p K) (B : Matrix p n K)
    (C : Matrix m q K) (E : Matrix q n K) (s t : K) :
    ∃ P : Matrix m ((p × q) ⊕ Unit) K,
      ∃ Q : Matrix ((p × q) ⊕ Unit) n K,
        P * Q = fun i j => s * ((A * B) i j * (C * E) i j) + t := by
  let P : Matrix m ((p × q) ⊕ Unit) K := fun i k =>
    Sum.elim (fun r => s * (A i r.1 * C i r.2)) (fun _ => t) k
  let Q : Matrix ((p × q) ⊕ Unit) n K := fun k j =>
    Sum.elim (fun r => B r.1 j * E r.2 j) (fun _ => 1) k
  refine ⟨P, Q, ?_⟩
  ext i j
  change (∑ k : (p × q) ⊕ Unit, P i k * Q k j) = _
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, P, Q,
    Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr, mul_one, mul_apply]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A zero-one affine product of bond sizes `p` and `q` has at most
`2 ^ (card p * card q + 1)` residual rows, independently of its scalar coefficients.
This is the Boolean-selector estimate in Lemma 2 of
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem card_range_hadamard_affine_le_two_pow [Finite n]
    (A : Matrix m p K) (B : Matrix p n K)
    (C : Matrix m q K) (E : Matrix q n K) (s t : K)
    (hM : ∀ i j, s * ((A * B) i j * (C * E) i j) + t = 0 ∨
      s * ((A * B) i j * (C * E) i j) + t = 1) :
    (Set.range (fun i j => s * ((A * B) i j * (C * E) i j) + t)).Finite ∧
      Nat.card (Set.range (fun i j => s * ((A * B) i j * (C * E) i j) + t)) ≤
        2 ^ (Fintype.card p * Fintype.card q + 1) := by
  obtain ⟨P, Q, hPQ⟩ := exists_hadamard_affine_factorization A B C E s t
  have hbool : ∀ i j, (P * Q) i j = 0 ∨ (P * Q) i j = 1 := by
    simpa only [hPQ] using hM
  have h := card_range_mul_le_two_pow ((p × q) ⊕ Unit) P Q hbool
  simpa only [hPQ, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit] using h

end Matrix
