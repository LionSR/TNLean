/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Rényi entropy under geometric tail constraints

The Rényi version of the maximization step of Hastings' bootstrap lemma. Let `p` be a
probability vector on `Fin N`, read in decreasing order of the Schmidt coefficients, whose
mass beyond the first `K D^{2n}` entries is at most `x^{n+1}` for every `n`. For an order
`0 < α < 1` with `(D²)^{1-α} x^α < 1`, its Rényi entropy `(1 - α)⁻¹ ln ∑ p^α` is at most
`ln K - ln(1 - (D²)^{1-α} x^α) / (1 - α)`.

This is the extension to Rényi entropies at the end of the proof of Lemma 2 (`ble`) in
Hastings, arXiv:0705.2024v4, lines 392–410 of `References/0705.2024/law16.tex`. The source
maximizes `∑ p^α` under the tail constraints and observes that the resulting series converges
exactly when `exp[-2α/ξ'] (D²)^{1-α} < 1`. Here the entries are grouped into the blocks
between consecutive thresholds `K D^{2n}`. On each block the concavity of `t ↦ t^α` bounds
`∑ p^α` by `(block size)^{1-α} (block mass)^α`, and the block masses are bounded by the tail
constraints, so that the blocks sum to a geometric series of ratio `(D²)^{1-α} x^α`. The bound
differs from the von Neumann bound of `TNLean/MPS/AreaLaw/Hastings/TailEntropy.lean` only in
the term replacing `F(ξ', D)`, as the source states. For orders `α ≥ 1` the Rényi entropy is
at most the von Neumann entropy, so the von Neumann bound applies directly.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.sum_rpow_le_card_rpow_mul_sum_rpow`: on a finite set,
  `∑ p^α ≤ (card)^{1-α} (∑ p)^α` for `0 ≤ α ≤ 1`.
* `TNLean.MPS.AreaLaw.Hastings.sum_rpow_le_of_geometric_tails`: the bound on `∑ p^α`.
* `TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_geometric_tails`: the Rényi entropy bound.
* `TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_scale_tails`: the same bound in the form of
  Hastings' Lemma 2, with `x = exp (-2/ξ')`.
-/

open scoped BigOperators

namespace TNLean.MPS.AreaLaw.Hastings

open Finset

/-- **Power sums on a finite set.** For `0 ≤ α ≤ 1` and nonnegative `p`, the concavity of
`t ↦ t^α` gives `∑ p^α ≤ (card s)^{1-α} (∑ p)^α`. -/
theorem sum_rpow_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∑ i ∈ s, p i ^ α ≤ (s.card : ℝ) ^ (1 - α) * (∑ i ∈ s, p i) ^ α := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [sum_empty, card_empty, Nat.cast_zero]
    positivity
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hS : 0 ≤ ∑ i ∈ s, p i := sum_nonneg hp
  have hJ := (Real.concaveOn_rpow hα0 hα1).le_map_sum (t := s) (w := fun _ ↦ (s.card : ℝ)⁻¹)
    (fun _ _ ↦ by positivity) (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne'])
    (fun i hi ↦ Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul, ← mul_sum] at hJ
  rw [Real.mul_rpow (by positivity) hS, Real.inv_rpow hc.le] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hmul
  calc ∑ i ∈ s, p i ^ α ≤ s.card * (((s.card : ℝ) ^ α)⁻¹ * (∑ i ∈ s, p i) ^ α) := hmul
    _ = (s.card : ℝ) ^ (1 - α) * (∑ i ∈ s, p i) ^ α := by
      rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv, mul_assoc]

/-- **Power sums under geometric tail constraints.** Let `p` be a nonnegative vector on `Fin N`
of total mass at most one whose mass on the entries of index at least `K D^{2n}` is at most
`x^{n+1}` for every `n`, with `K ≥ 1`, `D ≥ 2` and `x ≥ 0`. For `0 < α < 1` with
`r = (D²)^{1-α} x^α < 1`, `∑ p^α ≤ K^{1-α} / (1 - r)`.
Hastings, arXiv:0705.2024v4, proof of Lemma 2, lines 397–405. -/
theorem sum_rpow_le_of_geometric_tails {N K D : ℕ} (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a ≤ 1) (hK : 1 ≤ K) (hD : 2 ≤ D) {x α : ℝ} (hx : 0 ≤ x) (hα0 : 0 < α)
    (hα1 : α < 1) (hr : ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α < 1)
    (htail : ∀ n : ℕ,
      ∑ a ∈ univ.filter (fun a : Fin N ↦ K * D ^ (2 * n) ≤ a.val), p a ≤ x ^ (n + 1)) :
    ∑ a, p a ^ α ≤ (K : ℝ) ^ (1 - α) / (1 - ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α) := by
  classical
  set T : ℕ → ℕ := fun n ↦ K * D ^ (2 * n) with hT
  set r : ℝ := ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α with hr_def
  have hTmono : StrictMono T := fun i j hij ↦
    (Nat.mul_lt_mul_left (by omega)).2 (Nat.pow_lt_pow_right (by omega) (by omega))
  have hTge : ∀ n, n < T n := fun n ↦
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ D ^ (2 * n) := Nat.pow_le_pow_left hD _
      _ ≤ T n := Nat.le_mul_of_pos_left _ (by omega)
  -- The block of an entry: the number of thresholds at or below it.
  set g : Fin N → ℕ := fun a ↦ ((range N).filter (fun n ↦ T n ≤ a.val)).card with hg
  have hg_le : ∀ a, g a ≤ N := fun a ↦ (card_filter_le _ _).trans (card_range N).le
  have hlt : ∀ a, a.val < T (g a) := by
    intro a
    by_contra h
    push Not at h
    have hgN : g a < N := (hTge _).trans_le (h.trans a.isLt.le)
    have hsub : range (g a + 1) ⊆ (range N).filter (fun n ↦ T n ≤ a.val) := by
      intro n hn
      rw [mem_range] at hn
      rw [mem_filter, mem_range]
      exact ⟨by omega, (hTmono.monotone (by omega)).trans h⟩
    have := card_le_card hsub
    rw [card_range] at this
    change g a + 1 ≤ g a at this
    omega
  have hge : ∀ a, 1 ≤ g a → T (g a - 1) ≤ a.val := by
    intro a h1
    by_contra h
    push Not at h
    have hsub : (range N).filter (fun n ↦ T n ≤ a.val) ⊆ range (g a - 1) := by
      intro n hn
      rw [mem_filter] at hn
      rw [mem_range]
      by_contra h'
      push Not at h'
      exact lt_irrefl _ (((hTmono.monotone h').trans hn.2).trans_lt h)
    have := card_le_card hsub
    rw [card_range] at this
    change g a ≤ g a - 1 at this
    omega
  have hr0 : 0 ≤ r := by positivity
  have hblock : ∀ j,
      ∑ a ∈ univ.filter (fun a ↦ g a = j), p a ^ α ≤ (K : ℝ) ^ (1 - α) * r ^ j := by
    intro j
    set S := univ.filter (fun a : Fin N ↦ g a = j) with hS
    have hcard : (S.card : ℝ) ≤ T j := by
      have : S.card ≤ (range (T j)).card :=
        card_le_card_of_injOn (fun a ↦ a.val)
          (fun a ha ↦ by
            rw [hS, coe_filter] at ha
            rw [coe_range, Set.mem_Iio, ← ha.2]
            exact hlt a)
          (fun a _ b _ h ↦ Fin.ext h)
      rw [card_range] at this
      exact_mod_cast this
    have hmass : ∑ a ∈ S, p a ≤ x ^ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [pow_zero]
        exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ hp _)).trans hsum
      · calc ∑ a ∈ S, p a
            ≤ ∑ a ∈ univ.filter (fun a : Fin N ↦ K * D ^ (2 * (j - 1)) ≤ a.val), p a :=
              sum_le_sum_of_subset_of_nonneg
                (fun a ha ↦ by
                  rw [hS, mem_filter] at ha
                  rw [mem_filter]
                  have := hge a (by omega)
                  rw [ha.2] at this
                  exact ⟨mem_univ _, this⟩)
                (fun _ _ _ ↦ hp _)
          _ ≤ x ^ (j - 1 + 1) := htail (j - 1)
          _ = x ^ j := by rw [Nat.sub_add_cancel hj]
    calc ∑ a ∈ S, p a ^ α ≤ (S.card : ℝ) ^ (1 - α) * (∑ a ∈ S, p a) ^ α :=
          sum_rpow_le_card_rpow_mul_sum_rpow S p (fun a _ ↦ hp a) hα0.le hα1.le
      _ ≤ (T j : ℝ) ^ (1 - α) * (x ^ j) ^ α :=
          mul_le_mul (Real.rpow_le_rpow (by positivity) hcard (by linarith))
            (Real.rpow_le_rpow (sum_nonneg fun a _ ↦ hp a) hmass hα0.le)
            (Real.rpow_nonneg (sum_nonneg fun a _ ↦ hp a) _) (by positivity)
      _ = (K : ℝ) ^ (1 - α) * r ^ j := by
          rw [hT, hr_def]
          push_cast
          rw [Real.mul_rpow (by positivity) (by positivity), pow_mul, mul_pow, mul_assoc,
            ← Real.rpow_pow_comm (by positivity), ← Real.rpow_pow_comm hx]
  calc ∑ a, p a ^ α
      = ∑ j ∈ range (N + 1), ∑ a ∈ univ.filter (fun a ↦ g a = j), p a ^ α :=
        (sum_fiberwise_of_maps_to (fun a _ ↦ mem_range.2 (Nat.lt_succ_of_le (hg_le a))) _).symm
    _ ≤ ∑ j ∈ range (N + 1), (K : ℝ) ^ (1 - α) * r ^ j := sum_le_sum fun j _ ↦ hblock j
    _ = (K : ℝ) ^ (1 - α) * ∑ j ∈ range (N + 1), r ^ j := (mul_sum _ _ _).symm
    _ ≤ (K : ℝ) ^ (1 - α) * (r ^ 0 / (1 - r)) := by
        gcongr
        rw [range_eq_Ico]
        exact geom_sum_Ico_le_of_lt_one hr0 hr
    _ = (K : ℝ) ^ (1 - α) / (1 - r) := by rw [pow_zero, mul_one_div]

/-- **Rényi entropy under geometric tail constraints.** Let `p` be a probability vector on
`Fin N` whose mass on the entries of index at least `K D^{2n}` is at most `x^{n+1}` for every
`n`, with `K ≥ 1`, `D ≥ 2` and `x ≥ 0`. For `0 < α < 1` with `(D²)^{1-α} x^α < 1`, the Rényi
entropy `(1 - α)⁻¹ ln ∑ p^α` is at most `ln K - ln(1 - (D²)^{1-α} x^α) / (1 - α)`.
Hastings, arXiv:0705.2024v4, proof of Lemma 2, lines 397–410. -/
theorem renyiEntropy_le_of_geometric_tails {N K D : ℕ} (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hK : 1 ≤ K) (hD : 2 ≤ D) {x α : ℝ} (hx : 0 ≤ x) (hα0 : 0 < α)
    (hα1 : α < 1) (hr : ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α < 1)
    (htail : ∀ n : ℕ,
      ∑ a ∈ univ.filter (fun a : Fin N ↦ K * D ^ (2 * n) ≤ a.val), p a ≤ x ^ (n + 1)) :
    (1 - α)⁻¹ * Real.log (∑ a, p a ^ α) ≤
      Real.log K - Real.log (1 - ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α) / (1 - α) := by
  have hpos : 0 < ∑ a, p a ^ α := by
    have hle : ∑ a, p a ≤ ∑ a, p a ^ α := sum_le_sum fun a _ ↦
      Real.self_le_rpow_of_le_one (hp a)
        (hsum ▸ single_le_sum (fun b _ ↦ hp b) (mem_univ a)) hα1.le
    linarith
  have hbound := sum_rpow_le_of_geometric_tails p hp hsum.le hK hD hx hα0 hα1 hr htail
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1r : 0 < 1 - ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_div (by positivity) h1r.ne', Real.log_rpow hKr] at hlog
  calc (1 - α)⁻¹ * Real.log (∑ a, p a ^ α)
      ≤ (1 - α)⁻¹ * ((1 - α) * Real.log K - Real.log (1 - ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = Real.log K - Real.log (1 - ((D : ℝ) ^ 2) ^ (1 - α) * x ^ α) / (1 - α) := by
        field_simp

/-- **Hastings' Rényi entropy bound at scale `m`.** Let `p` be a probability vector on `Fin N`
whose mass on the entries of index at least `k D^{2(m + 1 + n)}` is at most
`exp (-2 (n + 1) / ξ')` for every `n`, with `k ≥ 1` and `D ≥ 2`. For `0 < α < 1`
with `exp (-2α/ξ') (D²)^{1-α} < 1`, the Rényi entropy `(1 - α)⁻¹ ln ∑ p^α` is at most
`ln k + (2m + 2) ln D - ln(1 - (D²)^{1-α} exp (-2α/ξ')) / (1 - α)`.
Hastings, arXiv:0705.2024v4, proof of Lemma 2, lines 392–410: the constraint (`constraint2`)
at the scales `m + 1 + n` and the convergence condition of line 406. -/
theorem renyiEntropy_le_of_scale_tails {N k D m : ℕ} (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hk : 1 ≤ k) (hD : 2 ≤ D) {ξ' α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hconv : ((D : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ')) < 1)
    (htail : ∀ n : ℕ,
      ∑ a ∈ univ.filter (fun a : Fin N ↦ k * D ^ (2 * (m + 1 + n)) ≤ a.val), p a ≤
        Real.exp (-(2 * (n + 1) / ξ'))) :
    (1 - α)⁻¹ * Real.log (∑ a, p a ^ α) ≤
      Real.log k + (2 * m + 2) * Real.log D -
        Real.log (1 - ((D : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ'))) / (1 - α) := by
  set x := Real.exp (-(2 / ξ')) with hx
  have hxα : x ^ α = Real.exp (-(2 * α / ξ')) := by
    rw [hx, ← Real.exp_mul]
    congr 1
    ring
  have hK : 1 ≤ k * D ^ (2 * (m + 1)) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
  have hbound := renyiEntropy_le_of_geometric_tails p hp hsum hK hD (Real.exp_pos _).le hα0 hα1
    (hxα ▸ hconv) (fun n ↦ by
      have h := htail n
      rw [show k * D ^ (2 * (m + 1)) * D ^ (2 * n) = k * D ^ (2 * (m + 1 + n)) by ring]
      rw [← Real.exp_nat_mul]
      convert h using 2
      push_cast
      ring)
  rw [hxα] at hbound
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogK :
      Real.log ((k * D ^ (2 * (m + 1)) : ℕ) : ℝ) = Real.log k + (2 * m + 2) * Real.log D := by
    push_cast
    rw [Real.log_mul hkr.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlogK] at hbound
  exact hbound

end TNLean.MPS.AreaLaw.Hastings
