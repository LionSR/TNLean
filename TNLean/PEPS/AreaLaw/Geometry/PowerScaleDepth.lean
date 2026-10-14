/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Depth and generation count of a power-contracting scale recursion

Let `f` be a scale map with `0 < f u ≤ u ^ ρ` for every scale `u` at least a
stopping scale `S_* > 1`, where `0 < ρ < 1`. Consider a recursion that starts at
scale `S` and passes from generation `i` to generation `i + 1` only when the
generation-`i` scale `f^[i] S` is at least `S_*`. While this holds,
`log f^[i] S ≤ ρ ^ i log S`, so the recursion has at most
`C + C log log (S + e)` generations. With boundedly many children per member,
the members of all generations number at most a fixed power of `log (S + e)`.

These are the scalar estimates behind the depth counts of the repair recursion
of the area-law manuscript and the cell recursion of the polynomial-PEPS
manuscript. They do not construct either recursion.

## Main statements

* `log_iterate_le_of_le_rpow`: `log f^[i] S ≤ ρ ^ i log S` along nonterminal generations.
* `exists_iterate_depth_bound`: at most `C + C log log (S + e)` generations.
* `exists_iterate_generation_count_bound`: `∑_{j ≤ m} b ^ j ≤ C (log (S + e)) ^ C`.
* `mul_rpow_le_max_mul_rpow`: change of the logarithmic size measure in such a count.
* `forall_le_iterate_of_le_iterate`: for a globally contracting map, a generation
  above the stopping scale has only ancestors above it.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, lines 668–686
  (`geometry:descendant-count`).
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`),
  `02-information.tex`, lines 302–311.

Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable {f : ℝ → ℝ} {ρ Sstar : ℝ}

/-- Along nonterminal generations of a recursion with `0 < f u ≤ u ^ ρ` above the
stopping scale, the generation-`i` scale satisfies `log f^[i] S ≤ ρ ^ i log S`.
Source: area-law Section 11, `10-geometry.tex`, lines 670–671; polynomial-PEPS
Lemma 3.2, `02-information.tex`, lines 302–308. -/
theorem log_iterate_le_of_le_rpow
    (hf : ∀ u, Sstar ≤ u → 0 < f u ∧ f u ≤ u ^ ρ) (hρ : 0 ≤ ρ) (hSstar : 0 < Sstar)
    {S : ℝ} {i : ℕ} (hi : ∀ k < i, Sstar ≤ f^[k] S) :
    Real.log (f^[i] S) ≤ ρ ^ i * Real.log S := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hx := hi i (Nat.lt_succ_self i)
    obtain ⟨hpos, hle⟩ := hf _ hx
    rw [Function.iterate_succ_apply']
    calc Real.log (f (f^[i] S)) ≤ Real.log ((f^[i] S) ^ ρ) := Real.log_le_log hpos hle
      _ = ρ * Real.log (f^[i] S) := Real.log_rpow (hSstar.trans_le hx) ρ
      _ ≤ ρ * (ρ ^ i * Real.log S) :=
          mul_le_mul_of_nonneg_left (ih fun k hk ↦ hi k (Nat.lt_succ_of_lt hk)) hρ
      _ = ρ ^ (i + 1) * Real.log S := by ring

/-- `log (S + e) ≥ 1` for every nonnegative `S`. -/
theorem one_le_log_add_exp_one {S : ℝ} (hS : 0 ≤ S) : 1 ≤ Real.log (S + Real.exp 1) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- **Depth of a power-contracting recursion.** If `0 < f u ≤ u ^ ρ` for every
`u ≥ S_*`, with `0 < ρ < 1` and `S_* > 1`, then there is a constant `C > 0` such
that every recursion from a positive scale `S` whose generations `0, …, m - 1`
are nonterminal has `m ≤ C + C log log (S + e)`.
Source: area-law Section 11, `10-geometry.tex`, lines 670–675; polynomial-PEPS
Lemma 3.2, `02-information.tex`, lines 302–308. -/
theorem exists_iterate_depth_bound
    (hf : ∀ u, Sstar ≤ u → 0 < f u ∧ f u ≤ u ^ ρ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hSstar : 1 < Sstar) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S → ∀ m : ℕ, (∀ i < m, Sstar ≤ f^[i] S) →
      (m : ℝ) ≤ C + C * Real.log (Real.log (S + Real.exp 1)) := by
  have hc : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  set a : ℝ := Real.log (Real.log Sstar)
  set A : ℝ := (|a| + 1) / -Real.log ρ with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A + 1, by positivity, fun S hS m hm => ?_⟩
  have hL0 : 0 ≤ Real.log (Real.log (S + Real.exp 1)) :=
    Real.log_nonneg (one_le_log_add_exp_one hS.le)
  cases m with
  | zero => simp only [CharP.cast_eq_zero]; positivity
  | succ n =>
    have h1 : Real.log Sstar ≤ ρ ^ n * Real.log S :=
      (Real.log_le_log (by linarith) (hm n (Nat.lt_succ_self n))).trans
        (log_iterate_le_of_le_rpow hf hρ.le (by linarith)
          fun k hk ↦ hm k (Nat.lt_succ_of_lt hk))
    have hlogS : 0 < Real.log S := by
      by_contra h
      have : ρ ^ n * Real.log S ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hρ.le n) (not_lt.mp h)
      linarith [Real.log_pos hSstar]
    have h2 : a ≤ n * Real.log ρ + Real.log (Real.log S) := by
      have := Real.log_le_log (Real.log_pos hSstar) h1
      rwa [Real.log_mul (pow_ne_zero _ hρ.ne') hlogS.ne', Real.log_pow] at this
    have hL : Real.log (Real.log S) ≤ Real.log (Real.log (S + Real.exp 1)) :=
      Real.log_le_log hlogS (Real.log_le_log hS (by linarith [Real.exp_pos 1]))
    have key : (n : ℝ) * -Real.log ρ ≤ (|a| + 1) * (1 + Real.log (Real.log (S + Real.exp 1))) := by
      nlinarith [neg_abs_le a, abs_nonneg a, mul_nonneg (abs_nonneg a) hL0]
    have hn : (n : ℝ) ≤ A + A * Real.log (Real.log (S + Real.exp 1)) := by
      calc (n : ℝ) ≤ (|a| + 1) * (1 + Real.log (Real.log (S + Real.exp 1))) / -Real.log ρ :=
            (le_div_iff₀ hc).mpr key
        _ = A + A * Real.log (Real.log (S + Real.exp 1)) := by rw [hA]; ring
    push_cast
    nlinarith

/-- **Generation count of a power-contracting recursion.** Under the hypotheses of
`exists_iterate_depth_bound`, for a branching bound `b ≥ 0` there is a constant
`C > 0` such that, whenever the generations `0, …, m - 1` from a positive scale
`S` are nonterminal, the at most `b ^ j` members of each generation `j ≤ m`
number in total at most `C (log (S + e)) ^ C`.
Source: area-law Section 11, `10-geometry.tex`, lines 676–682; polynomial-PEPS
Lemma 3.2, `02-information.tex`, lines 302–311. -/
theorem exists_iterate_generation_count_bound
    (hf : ∀ u, Sstar ≤ u → 0 < f u ∧ f u ≤ u ^ ρ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hSstar : 1 < Sstar) {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S → ∀ m : ℕ, (∀ i < m, Sstar ≤ f^[i] S) →
      ∑ j ∈ Finset.range (m + 1), b ^ j ≤ C * Real.log (S + Real.exp 1) ^ C := by
  obtain ⟨C₁, hC₁, hdepth⟩ := exists_iterate_depth_bound hf hρ hρ1 hSstar
  set B : ℝ := b + 2 with hB_def
  have hB : 2 ≤ B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  set p : ℝ := C₁ * Real.log B with hp_def
  have hp : 0 ≤ p := by positivity
  set K : ℝ := B ^ (C₁ + 1) with hK_def
  have hK : 0 < K := by positivity
  refine ⟨max K p, lt_max_of_lt_left hK, fun S hS m hm => ?_⟩
  set x : ℝ := Real.log (S + Real.exp 1) with hx_def
  have hx1 : 1 ≤ x := one_le_log_add_exp_one hS.le
  have hx0 : 0 < x := by linarith
  have hsum : ∑ j ∈ Finset.range (m + 1), b ^ j ≤ B ^ (m + 1) := by
    calc ∑ j ∈ Finset.range (m + 1), b ^ j ≤ ∑ j ∈ Finset.range (m + 1), B ^ j :=
          Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ hb (by linarith) j
      _ ≤ B ^ (m + 1) := by
          rw [geom_sum_eq (by linarith : B ≠ 1), div_le_iff₀ (by linarith)]
          have : (0 : ℝ) ≤ B ^ (m + 1) := by positivity
          nlinarith
  have hmC : ((m : ℝ) + 1) ≤ (C₁ + 1) + C₁ * Real.log x := by
    have := hdepth S hS m hm
    linarith
  have hpow : B ^ (m + 1) ≤ K * x ^ p := by
    calc B ^ (m + 1) = B ^ ((m : ℝ) + 1) := by
          rw [← Real.rpow_natCast]; push_cast; rfl
      _ ≤ B ^ ((C₁ + 1) + C₁ * Real.log x) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hmC
      _ = K * x ^ p := by
          rw [Real.rpow_add (by linarith), hK_def]
          congr 1
          rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hx0, hp_def]
          ring_nf
  calc ∑ j ∈ Finset.range (m + 1), b ^ j ≤ K * x ^ p := hsum.trans hpow
    _ ≤ K * x ^ max K p := by
        gcongr
        exact le_max_right _ _
    _ ≤ max K p * x ^ max K p := by
        gcongr
        exact le_max_left _ _

/-- A bound `C x ^ C` with `0 ≤ x ≤ 2 y` and `y ≥ 1` is a bound of the same form in `y`,
with the constant `max (C 2 ^ C) C`. Used to pass from `log (S + e)` to another
logarithmic size measure. -/
theorem mul_rpow_le_max_mul_rpow {C x y : ℝ} (hC : 0 < C) (hx : 0 ≤ x) (hxy : x ≤ 2 * y)
    (hy : 1 ≤ y) :
    C * x ^ C ≤ max (C * 2 ^ C) C * y ^ max (C * 2 ^ C) C := by
  calc C * x ^ C ≤ C * (2 * y) ^ C := by gcongr
    _ = C * 2 ^ C * y ^ C := by rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
    _ ≤ max (C * 2 ^ C) C * y ^ max (C * 2 ^ C) C := by
        gcongr
        all_goals first | exact le_max_left _ _ | exact le_max_right _ _

/-- For a scale map with `0 < f u ≤ u ^ ρ` at every positive scale, `0 < ρ ≤ 1`,
a scale below `S_* ≥ 1` has only descendants below `S_*`. Hence a generation
whose scale is at least `S_*` has all its ancestors at least `S_*`, i.e. the
earlier generations were nonterminal. -/
theorem forall_le_iterate_of_le_iterate
    (hf : ∀ u, 0 < u → 0 < f u ∧ f u ≤ u ^ ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hSstar : 1 ≤ Sstar) {S : ℝ} (hS : 0 < S) {m : ℕ} (hm : Sstar ≤ f^[m] S) :
    ∀ i ≤ m, Sstar ≤ f^[i] S := by
  have hpos : ∀ n, 0 < f^[n] S := by
    intro n
    induction n with
    | zero => simpa using hS
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hf _ ih).1
  have hstep : ∀ x, 0 < x → x < Sstar → f x < Sstar := fun x hx hxS ↦
    calc f x ≤ x ^ ρ := (hf x hx).2
      _ < Sstar ^ ρ := Real.rpow_lt_rpow hx.le hxS hρ
      _ ≤ Sstar ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hSstar hρ1
      _ = Sstar := Real.rpow_one Sstar
  intro i hi
  by_contra h
  have hbelow : ∀ k, f^[i + k] S < Sstar := by
    intro k
    induction k with
    | zero => exact not_le.mp h
    | succ k ih =>
      rw [← add_assoc, Function.iterate_succ_apply']
      exact hstep _ (hpos _) ih
  have := hbelow (m - i)
  rw [Nat.add_sub_cancel' hi] at this
  linarith

end TNLean.PEPS.AreaLaw.Geometry
