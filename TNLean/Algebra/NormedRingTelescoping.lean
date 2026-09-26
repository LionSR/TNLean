/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-!
# Telescoping powers of a perturbed idempotent

In a normed ring, if `E` is idempotent and `X` is `δ`-close to `E`, then
`‖X^M - E^M‖ ≤ c((1 + cδ)^M - 1)`, where `c` bounds `‖E‖` and `‖1‖`. This is the iteration of
arXiv:2103.13367, Supplemental Material, eqs. `final_eq` to `finished`. The file also records the
elementary real bounds that turn `(1 + y)^M - 1` into `M y e^{M y}` and a bound of the form
`C y e^{C y}` into a linear bound.

## Main declarations

* `pow_sub_pow_eq_sum_mul_sub_mul` — the telescoping identity.
* `norm_pow_sub_pow_le_of_isIdempotentElem` — the telescoping bound.
* `one_add_pow_sub_one_le_mul_exp` — `(1 + y)^M - 1 ≤ M y e^{M y}`.
* `le_mul_of_le_mul_exp_of_le` — `v ≤ C y e^{C y}` and `v ≤ B` give `v ≤ (C e^C + B) y`.
-/

/-- The telescoping identity `X^n - E^n = ∑_{k<n} X^k (X - E) E^{n-1-k}` in a ring.

arXiv:2103.13367, eq. `final_eq` (second line). -/
theorem pow_sub_pow_eq_sum_mul_sub_mul {R : Type*} [Ring R] (X E : R) (n : ℕ) :
    X ^ n - E ^ n = ∑ k ∈ Finset.range n, X ^ k * (X - E) * E ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.range n, X ^ k * (X - E) * E ^ (n - k) = (X ^ n - E ^ n) * E := by
      rw [ih, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.1 hk
      rw [mul_assoc (X ^ k * (X - E)), ← pow_succ, show n - 1 - k + 1 = n - k by omega]
    rw [h, pow_succ X n, pow_succ E n]
    noncomm_ring

/-- **Telescoping bound for a perturbed idempotent.** In a normed ring, let `E` be idempotent
with `‖E‖ ≤ c` and `‖1‖ ≤ c`, and let `‖X - E‖ ≤ δ`. Then
`‖X^M - E^M‖ ≤ c ((1 + cδ)^M - 1)`.

This is the iteration of arXiv:2103.13367, eqs. `final_eq`, `inequality`, `almost_done`, and
`finished`: `E^k = E` for `k ≥ 1` bounds every factor `E^k` by `c`, and
`‖X^k‖ ≤ c + ‖X^k - E^k‖` feeds the bound back into the telescoping sum. -/
theorem norm_pow_sub_pow_le_of_isIdempotentElem {R : Type*} [NormedRing R] {E X : R}
    (hE : IsIdempotentElem E) {c δ : ℝ} (hEc : ‖E‖ ≤ c) (h1c : ‖(1 : R)‖ ≤ c)
    (hδ : ‖X - E‖ ≤ δ) (M : ℕ) :
    ‖X ^ M - E ^ M‖ ≤ c * ((1 + c * δ) ^ M - 1) := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hEc
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hEpow : ∀ k : ℕ, ‖E ^ k‖ ≤ c := fun k => by
    rcases k with _ | k
    · simpa using h1c
    · rw [hE.pow_succ_eq]; exact hEc
  -- The closed form `b n = c ((1 + cδ)^n - 1)` solves `b n = ∑_{k<n} (c + b k) c δ`.
  have hclosed : ∀ n : ℕ, ∑ k ∈ Finset.range n, (c + c * ((1 + c * δ) ^ k - 1)) * δ * c =
      c * ((1 + c * δ) ^ n - 1) := fun n => by
    have hg := geom_sum_mul (1 + c * δ) n
    simp only [add_sub_cancel_left] at hg
    calc ∑ k ∈ Finset.range n, (c + c * ((1 + c * δ) ^ k - 1)) * δ * c
        = c * ((∑ k ∈ Finset.range n, (1 + c * δ) ^ k) * (c * δ)) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = c * ((1 + c * δ) ^ n - 1) := by rw [hg]
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rw [pow_sub_pow_eq_sum_mul_sub_mul, ← hclosed M]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk := Finset.mem_range.1 hk
    have hXk : ‖X ^ k‖ ≤ c + c * ((1 + c * δ) ^ k - 1) := by
      calc ‖X ^ k‖ = ‖E ^ k + (X ^ k - E ^ k)‖ := by rw [add_sub_cancel]
        _ ≤ ‖E ^ k‖ + ‖X ^ k - E ^ k‖ := norm_add_le _ _
        _ ≤ c + c * ((1 + c * δ) ^ k - 1) := add_le_add (hEpow k) (ih k hk)
    calc ‖X ^ k * (X - E) * E ^ (M - 1 - k)‖
        ≤ ‖X ^ k‖ * ‖X - E‖ * ‖E ^ (M - 1 - k)‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ (c + c * ((1 + c * δ) ^ k - 1)) * δ * c :=
          mul_le_mul (mul_le_mul hXk hδ (norm_nonneg _) ((norm_nonneg _).trans hXk)) (hEpow _)
            (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hXk) hδ0)

/-- `(1 + y)^M - 1 ≤ M y e^{M y}` for `y ≥ 0`: the last step of arXiv:2103.13367, eq.
`finished`, `ε_q + ε_q² (1 + ε_q/M)^{M-2} = ε_q + ε_q² e^{ε_q} (1 + O(ε_q/M))`. -/
theorem one_add_pow_sub_one_le_mul_exp {y : ℝ} (hy : 0 ≤ y) (M : ℕ) :
    (1 + y) ^ M - 1 ≤ M * y * Real.exp (M * y) := by
  have ht : 0 ≤ (M : ℝ) * y := mul_nonneg M.cast_nonneg hy
  have h1 : (1 + y) ^ M ≤ Real.exp (M * y) := by
    calc (1 + y) ^ M ≤ Real.exp y ^ M := by
          gcongr
          linarith [Real.add_one_le_exp y]
      _ = Real.exp (M * y) := (Real.exp_nat_mul y M).symm
  have h2 : Real.exp (M * y) - 1 ≤ M * y * Real.exp (M * y) := by
    have := Real.add_one_le_exp (-((M : ℝ) * y))
    have hprod : Real.exp (M * y) * Real.exp (-(M * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos ((M : ℝ) * y)]
  linarith

/-- A quantity bounded both by `C y e^{C y}` and by a constant `B` is at most `(C e^C + B) y`:
for `y ≤ 1` use the first bound, and for `y > 1` the second. This turns the explicit bounds of
arXiv:2307.01696, eq. (S9) and Lemma 1'(i), into their `O((N/q) e^{-γ q/ξ})` form. -/
theorem le_mul_of_le_mul_exp_of_le {C B v y : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hy : 0 ≤ y)
    (h₁ : v ≤ C * y * Real.exp (C * y)) (h₂ : v ≤ B) : v ≤ (C * Real.exp C + B) * y := by
  rcases le_or_gt y 1 with hy1 | hy1
  · have hexp : Real.exp (C * y) ≤ Real.exp C := Real.exp_le_exp.2 (by nlinarith)
    calc v ≤ C * y * Real.exp (C * y) := h₁
      _ ≤ C * y * Real.exp C := by gcongr
      _ ≤ (C * Real.exp C + B) * y := by nlinarith [Real.exp_pos C]
  · have : 0 ≤ C * Real.exp C * y := by positivity
    nlinarith
