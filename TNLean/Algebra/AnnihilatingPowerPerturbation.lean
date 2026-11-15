/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Ring.Basic

/-!
# Exact power preservation by annihilating directions

A square-zero perturbation annihilated by an element on both sides preserves
all its powers of order at least two. This is the exact integration step for
the cyclic root-selection argument associated with arXiv:1708.00029,
Theorem 4.1; see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
Square equality together with annihilation by the original square also
preserves all higher powers, allowing anticommuting directions.
-/

/-- A perturbation whose square and two mixed products vanish preserves
every power of order at least two. Applied to channel endomorphisms, this
integrates an annihilating direction exactly, unlike a general direction
in the kernel of the linearized power map. Source context:
arXiv:1708.00029, Theorem 4.1, converse root-selection argument. -/
theorem add_pow_eq_of_annihilating_square_zero {A : Type*} [Semiring A]
    {F H : A} (hFH : F * H = 0) (hHF : H * F = 0) (hHH : H * H = 0)
    {p : ℕ} (hp : 2 ≤ p) : (F + H) ^ p = F ^ p := by
  have hAll (n : ℕ) : (F + H) ^ (n + 2) = F ^ (n + 2) := by
    induction n with
    | zero =>
      simp only [Nat.zero_add, pow_two, add_mul, mul_add, hFH, hHF, hHH,
        add_zero]
    | succ n ih =>
      have hZero : F ^ (n + 2) * H = 0 := by
        rw [pow_succ, mul_assoc, hFH, mul_zero]
      calc
        (F + H) ^ (n.succ + 2) = (F + H) ^ (n + 2) * (F + H) :=
          pow_succ _ (n + 2)
        _ = F ^ (n + 2) * (F + H) := by rw [ih]
        _ = F ^ (n + 2) * F := by rw [mul_add, hZero, add_zero]
        _ = F ^ (n.succ + 2) := (pow_succ F (n + 2)).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
  simpa only [Nat.add_comm] using hAll n

/-- Equality of squares and annihilation by the original square suffice
to preserve every higher power. This includes the exact integration of
the intermediate-sector perturbation in the cyclic root-selection
argument for arXiv:1708.00029, Theorem 4.1. -/
theorem add_pow_eq_of_sq_eq_of_sq_mul_eq_zero {A : Type*} [Semiring A]
    {F H : A} (hSq : (F + H) ^ 2 = F ^ 2) (hSqH : F ^ 2 * H = 0)
    {p : ℕ} (hp : 2 ≤ p) : (F + H) ^ p = F ^ p := by
  have hAll (n : ℕ) : (F + H) ^ (n + 2) = F ^ (n + 2) := by
    induction n with
    | zero => simpa only [Nat.zero_add] using hSq
    | succ n ih =>
      have hZero : F ^ (n + 2) * H = 0 := by
        calc
          F ^ (n + 2) * H = F ^ n * (F ^ 2 * H) := by rw [pow_add, mul_assoc]
          _ = 0 := by rw [hSqH, mul_zero]
      calc
        (F + H) ^ (n.succ + 2) = (F + H) ^ (n + 2) * (F + H) :=
          pow_succ _ (n + 2)
        _ = F ^ (n + 2) * (F + H) := by rw [ih]
        _ = F ^ (n + 2) * F := by rw [mul_add, hZero, add_zero]
        _ = F ^ (n.succ + 2) := (pow_succ F (n + 2)).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
  simpa only [Nat.add_comm] using hAll n

/-- Anticommuting square-zero perturbations preserve every power from the
square onward when the original square annihilates the perturbation.
This is the intermediate-sector integration step for the written cyclic
selection argument associated with arXiv:1708.00029, Theorem 4.1. -/
theorem add_pow_eq_of_anticommuting_square_zero {A : Type*} [Semiring A]
    {F H : A} (hMixed : F * H + H * F = 0) (hHH : H * H = 0)
    (hSqH : F ^ 2 * H = 0) {p : ℕ} (hp : 2 ≤ p) : (F + H) ^ p = F ^ p := by
  apply add_pow_eq_of_sq_eq_of_sq_mul_eq_zero ?_ hSqH hp
  calc
    (F + H) ^ 2 = F * F + (F * H + H * F) + H * H := by
      simp only [pow_two, add_mul, mul_add]
      ac_rfl
    _ = F ^ 2 := by simp only [hMixed, hHH, add_zero, pow_two]
