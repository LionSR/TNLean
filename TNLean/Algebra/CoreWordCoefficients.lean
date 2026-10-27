/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PolynomialLinearFactor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Retained coefficients of ordered affine products

An ordered list of affine tensor-product factors has an expansion over
words in its interior alphabet. The retained coefficient of each word is
defined without the interior matrices. The expansion includes every word
length through the number of factors, with all matrix products in their
original order.

The empty factor list, the empty alphabet, and empty matrix index types are
included. The coefficient matrices need not commute.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333, and AKLV, arXiv:1301.1162v1, Lemma 4.2,
lines 646–653.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace Matrix

/-- The retained coefficient of a word. Interior operators do not enter this
recursion. Supporting algebra for ALVV, Proposition 5.7, lines 1324–1333. -/
def coreWordCoeff {ι m : Type*} [Fintype m] [DecidableEq m]
    (R : ι → Matrix m m ℂ) : List (Matrix m m ℂ × ℂ) → List ι → Matrix m m ℂ
  | [], [] => 1
  | [], _ :: _ => 0
  | (K, _) :: s, [] => K * coreWordCoeff R s []
  | (K, c) :: s, a :: w =>
      K * coreWordCoeff R s (a :: w) + (c • R a) * coreWordCoeff R s w

/-- A step whose constant part acts only on the retained space.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 646–653. -/
private noncomputable def coreStepPolynomial {ι m n : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (R : ι → Matrix m m ℂ) (N : ι → Matrix n n ℂ) (z : Matrix m m ℂ × ℂ) :
    Polynomial (Matrix (m × n) (m × n) ℂ) :=
  Polynomial.C (z.1 ⊗ₖ (1 : Matrix n n ℂ)) +
    Polynomial.C (∑ a, (z.2 • R a) ⊗ₖ N a) * Polynomial.X

/-- Every degree coefficient is an exact ordered-word sum with retained
coefficients fixed before the interior family is supplied. Empty lists and
empty alphabets are included. Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333, and AKLV, Lemma 4.2, lines 646–653. -/
private theorem coeff_prod_coreStepPolynomial
    {ι m n : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (R : ι → Matrix m m ℂ) (N : ι → Matrix n n ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (t : ℕ) :
    ((steps.map (coreStepPolynomial R N)).prod).coeff t =
      ∑ w : Fin t → ι,
        (coreWordCoeff R steps (List.ofFn w)) ⊗ₖ
          ((List.ofFn (fun j ↦ N (w j))).prod) := by
  induction steps generalizing t with
  | nil =>
    cases t with
    | zero => simp [coreWordCoeff]
    | succ t => simp [coreWordCoeff, List.ofFn_succ, Polynomial.coeff_one]
  | cons z s ih =>
    obtain ⟨K, c⟩ := z
    rw [List.map_cons, List.prod_cons, coreStepPolynomial]
    cases t with
    | zero =>
      rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero,
        mul_zero, add_zero, ih 0]
      simp only [List.ofFn_zero, List.prod_nil, Fintype.sum_unique,
        coreWordCoeff, ← mul_kronecker_mul, one_mul]
    | succ t =>
      rw [Polynomial.coeff_C_add_C_mul_X_mul_succ, ih (t + 1), ih t]
      have hhead (F : (Fin (t + 1) → ι) → Matrix (m × n) (m × n) ℂ) :
          (∑ w, F w) = ∑ a : ι, ∑ w : Fin t → ι, F (Fin.cons a w) := by
        simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
          ((Fin.consEquiv (fun _ : Fin (t + 1) ↦ ι)).sum_comp F).symm
      rw [Finset.mul_sum, Finset.sum_mul_sum]
      simp_rw [← mul_kronecker_mul, one_mul]
      simp_rw [hhead, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
        List.prod_cons, coreWordCoeff]
      simp_rw [add_kronecker, Finset.sum_add_distrib]

/-- A word longer than the step list has zero retained coefficient.
Supporting ordered-word algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. The interior family is not involved. -/
private theorem coreWordCoeff_eq_zero_of_length_lt
    {ι m : Type*} [Fintype m] [DecidableEq m]
    (R : ι → Matrix m m ℂ) (s : List (Matrix m m ℂ × ℂ)) (w : List ι)
    (h : s.length < w.length) : coreWordCoeff R s w = 0 := by
  induction s generalizing w with
  | nil =>
    cases w with
    | nil => exact (Nat.not_lt_zero _ h).elim
    | cons a w => rfl
  | cons z s ih =>
    obtain ⟨K, c⟩ := z
    cases w with
    | nil => exact (Nat.not_lt_zero _ h).elim
    | cons a w =>
      have htail : s.length < w.length := Nat.lt_of_succ_lt_succ h
      have hfull : s.length < (a :: w).length := htail.trans (Nat.lt_succ_self _)
      simp only [coreWordCoeff, ih (a :: w) hfull, ih w htail, mul_zero, add_zero]

/-- The ordered polynomial product has degree at most the number of steps.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. No nonzero coefficient or nontrivial matrix space is assumed. -/
private theorem natDegree_prod_coreStepPolynomial_le
    {ι m n : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (R : ι → Matrix m m ℂ) (N : ι → Matrix n n ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) :
    ((steps.map (coreStepPolynomial R N)).prod).natDegree ≤ steps.length := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro t ht
  rw [coeff_prod_coreStepPolynomial R N steps t]
  apply Finset.sum_eq_zero
  intro w _
  have hlen : steps.length < (List.ofFn w).length := by
    simpa only [List.length_ofFn] using ht
  have hzero := coreWordCoeff_eq_zero_of_length_lt R steps (List.ofFn w) hlen
  simp only [hzero, zero_kronecker]

/-- An ordered product is recovered from the retained word coefficients of
all degrees through the number of steps. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. Evaluation at one requires
no commutation between the matrix coefficients. -/
theorem prod_coreStep_eq_sum
    {ι m n : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (R : ι → Matrix m m ℂ) (N : ι → Matrix n n ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) :
    (steps.map (fun z ↦
      (z.1 ⊗ₖ (1 : Matrix n n ℂ)) + ∑ a, (z.2 • R a) ⊗ₖ N a)).prod =
      ∑ t ∈ Finset.range (steps.length + 1),
        ∑ w : Fin t → ι,
          (coreWordCoeff R steps (List.ofFn w)) ⊗ₖ
            ((List.ofFn (fun j ↦ N (w j))).prod) := by
  have heval : ((steps.map (coreStepPolynomial R N)).prod).eval
      (1 : Matrix (m × n) (m × n) ℂ) =
      (steps.map (fun z ↦
        (z.1 ⊗ₖ (1 : Matrix n n ℂ)) + ∑ a, (z.2 • R a) ⊗ₖ N a)).prod := by
    rw [← Polynomial.eval₂_id]
    simpa only [List.map_map, Function.comp_def, coreStepPolynomial,
      Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      RingHom.id_apply, mul_one] using
      (Polynomial.eval₂_list_prod_noncomm (RingHom.id _) (1 : Matrix (m × n) (m × n) ℂ)
        (steps.map (coreStepPolynomial R N)) (fun _ _ _ ↦ Commute.one_right _))
  calc
    _ = ((steps.map (coreStepPolynomial R N)).prod).eval 1 := heval.symm
    _ = ∑ t ∈ Finset.range (steps.length + 1),
        ((steps.map (coreStepPolynomial R N)).prod).coeff t := by
      simpa only [one_pow, mul_one] using
        (Polynomial.eval_eq_sum_range'
          (Nat.lt_succ_of_le (natDegree_prod_coreStepPolynomial_le R N steps))
          (1 : Matrix (m × n) (m × n) ℂ))
    _ = _ := by simp_rw [coeff_prod_coreStepPolynomial]

end Matrix

end
