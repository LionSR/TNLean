/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Lattice
import Mathlib.Tactic.Ring

/-!
# Natural-number functions bounded by a polynomial

A function `f : ℕ → ℕ` is polynomially bounded when `f n ≤ P (n + 1) ^ d` for all `n ≥ 1`,
with natural numbers `P` and `d` chosen before `n`. The class is closed under sums,
products, powers and pointwise domination, which is all that assembling the running time of
an algorithm from the costs of its steps needs.
-/

namespace TNLean

/-- `f n ≤ P (n + 1) ^ d` for all `n ≥ 1`, for some natural numbers `P` and `d`. -/
def IsNatPolynomialBounded (f : ℕ → ℕ) : Prop :=
  ∃ P d : ℕ, ∀ n : ℕ, 1 ≤ n → f n ≤ P * (n + 1) ^ d

namespace IsNatPolynomialBounded

theorem const (c : ℕ) : IsNatPolynomialBounded fun _ ↦ c :=
  ⟨c, 0, fun _ _ ↦ by simp⟩

theorem id : IsNatPolynomialBounded fun n ↦ n :=
  ⟨1, 1, fun n _ ↦ by rw [one_mul, pow_one]; exact Nat.le_succ n⟩

theorem of_le {f g : ℕ → ℕ} (hg : IsNatPolynomialBounded g) (h : ∀ n, 1 ≤ n → f n ≤ g n) :
    IsNatPolynomialBounded f := by
  obtain ⟨P, d, hP⟩ := hg
  exact ⟨P, d, fun n hn ↦ (h n hn).trans (hP n hn)⟩

theorem add {f g : ℕ → ℕ} (hf : IsNatPolynomialBounded f) (hg : IsNatPolynomialBounded g) :
    IsNatPolynomialBounded fun n ↦ f n + g n := by
  obtain ⟨P, d, hP⟩ := hf
  obtain ⟨Q, e, hQ⟩ := hg
  refine ⟨P + Q, max d e, fun n hn ↦ ?_⟩
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ max d e := Nat.pow_le_pow_right (by omega) (le_max_left d e)
  have h2 : (n + 1) ^ e ≤ (n + 1) ^ max d e := Nat.pow_le_pow_right (by omega) (le_max_right d e)
  calc f n + g n ≤ P * (n + 1) ^ d + Q * (n + 1) ^ e := Nat.add_le_add (hP n hn) (hQ n hn)
    _ ≤ P * (n + 1) ^ max d e + Q * (n + 1) ^ max d e :=
      Nat.add_le_add (Nat.mul_le_mul_left P h1) (Nat.mul_le_mul_left Q h2)
    _ = (P + Q) * (n + 1) ^ max d e := by ring

theorem mul {f g : ℕ → ℕ} (hf : IsNatPolynomialBounded f) (hg : IsNatPolynomialBounded g) :
    IsNatPolynomialBounded fun n ↦ f n * g n := by
  obtain ⟨P, d, hP⟩ := hf
  obtain ⟨Q, e, hQ⟩ := hg
  refine ⟨P * Q, d + e, fun n hn ↦ ?_⟩
  calc f n * g n ≤ (P * (n + 1) ^ d) * (Q * (n + 1) ^ e) := Nat.mul_le_mul (hP n hn) (hQ n hn)
    _ = P * Q * (n + 1) ^ (d + e) := by ring

theorem pow {f : ℕ → ℕ} (hf : IsNatPolynomialBounded f) (k : ℕ) :
    IsNatPolynomialBounded fun n ↦ f n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem max_one {f : ℕ → ℕ} (hf : IsNatPolynomialBounded f) :
    IsNatPolynomialBounded fun n ↦ max 1 (f n) := by
  refine (hf.add (const 1)).of_le fun n _ ↦ ?_
  simp only [max_le_iff]
  omega

/-- The bound can be taken with a positive coefficient. -/
theorem exists_one_le {f : ℕ → ℕ} (hf : IsNatPolynomialBounded f) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ n : ℕ, 1 ≤ n → f n ≤ P * (n + 1) ^ d := by
  obtain ⟨P, d, hP⟩ := hf
  exact ⟨P + 1, d, by omega, fun n hn ↦ (hP n hn).trans (Nat.mul_le_mul_right _ (by omega))⟩

end IsNatPolynomialBounded

end TNLean
