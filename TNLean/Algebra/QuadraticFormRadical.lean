/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The radical of a nonnegative real quadratic form

Let `Q` be a real quadratic form with `Q x ≥ 0` for every `x`. A zero `x` of `Q` is orthogonal to
every vector for the polar form: otherwise `Q (x + t y) < 0` for a suitable real `t`. Hence the
zero set of `Q` is its radical, a linear subspace, and this subspace is proper once `Q ≠ 0`.

## Main results

* `QuadraticForm.polar_eq_zero_of_nonneg`: a zero of a nonnegative form is polar-orthogonal to
  every vector.
* `QuadraticForm.mem_radical_iff_of_nonneg`: the radical of a nonnegative form is its zero set.
* `QuadraticForm.radical_ne_top_of_ne_zero`: the radical of a nonzero form is proper.
-/

namespace QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A zero `x` of a nonnegative real quadratic form is orthogonal to every vector for the polar
form. -/
theorem polar_eq_zero_of_nonneg (Q : QuadraticForm ℝ V) (hQ : ∀ x, 0 ≤ Q x) {x : V}
    (hx : Q x = 0) (y : V) : QuadraticMap.polar Q x y = 0 := by
  let p := QuadraticMap.polar Q x y
  let t := -p / (Q y + 1)
  have hd : 0 < Q y + 1 := by linarith [hQ y]
  have heq : Q (x + t • y) = -(p * p) / (Q y + 1) ^ 2 := by
    rw [QuadraticMap.map_add (Q : V → ℝ) x (t • y), Q.map_smul,
      QuadraticMap.polar_smul_right, hx]
    simp only [zero_add, smul_eq_mul]
    change (t * t) * Q y + t * p = _
    dsimp [t]
    field_simp [ne_of_gt hd]
    ring
  have hnonneg := hQ (x + t • y)
  rw [heq] at hnonneg
  have hscaled := mul_nonneg hnonneg (le_of_lt (sq_pos_of_pos hd))
  have hp : p * p = 0 := by
    have hden : (Q y + 1) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hd)
    rw [div_mul_cancel₀ _ hden] at hscaled
    nlinarith [sq_nonneg p]
  exact (mul_self_eq_zero.mp hp : p = 0)

/-- The radical of a nonnegative real quadratic form is its zero set. -/
theorem mem_radical_iff_of_nonneg (Q : QuadraticForm ℝ V) (hQ : ∀ x, 0 ≤ Q x) (x : V) :
    x ∈ Q.radical ↔ Q x = 0 := by
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    change Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0
    refine ⟨hx, ?_⟩
    apply LinearMap.ext
    intro y
    exact polar_eq_zero_of_nonneg Q hQ hx y

/-- The radical of a nonzero real quadratic form is a proper subspace. -/
theorem radical_ne_top_of_ne_zero (Q : QuadraticForm ℝ V) (hQ : Q ≠ 0) : Q.radical ≠ ⊤ := by
  intro htop
  apply hQ
  ext x
  have hx : x ∈ Q.radical := by rw [htop]; trivial
  exact hx.1

end QuadraticForm
