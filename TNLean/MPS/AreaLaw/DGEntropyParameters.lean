/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import QICLean.Analysis.ProbabilityEntropyRankTails

/-!
# Dyadic entropy estimates for the degenerate gapped area law

Cubic logarithmic bounds on approximation ranks yield one integer dyadic
rank majorant. Combined with the finite-probability tail estimate, this
bounds entropy by the logarithm of the ground-space dimension with
coefficient one, plus an explicit cubic logarithmic remainder. A final
scalar estimate absorbs the finite remainder into one gap-dependent term.

The physical tail estimates are not hypotheses about a Hamiltonian in this
module: the statements are scalar and finite-probability implications.
They support ALVV, arXiv:1602.08828v2, the proof of `thm:al-dg`,
lines 1085–1099.
-/

open scoped BigOperators

namespace Real

/-- Auxiliary to the entropy estimate in ALVV, arXiv:1602.08828v2,
proof of `thm:al-dg`, lines 1085–1087. Cubic logarithmic bounds at
dyadic numerical count bases admit one integer rank schedule. This is
a scalar statement and assumes no physical change of local dimension. -/
private theorem exists_cubic_dyadic_rank_majorant
    (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, log (D i : ℝ) ≤
      K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3) :
    let u : ℝ := 1 + log (q : ℝ) + log (1 / g)
    ∃ B : ℕ, 1 ≤ B ∧
      (B : ℝ) ≤ 26 * K * u ^ 3 / log 2 + 2 ∧
      ∀ i : ℕ, r * D 0 ^ 24 * D i ^ 2 ≤
        r * 2 ^ (B * (i + 1) ^ 3) := by
  intro u
  have hlog2pos : 0 < log 2 := log_pos (by norm_num)
  have hlog2le : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogbase (i : ℕ) : log ((q * 2 ^ i : ℕ) : ℝ) =
      log (q : ℝ) + (i : ℝ) * log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      log_mul hqpos.ne' (by positivity), log_pow]
  have hscale (i : ℕ) :
      1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g) ≤
        u * ((i : ℝ) + 1) := by
    rw [hlogbase]
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    dsimp only [u] at hu ⊢
    nlinarith
  have hlogDi (i : ℕ) : log (D i : ℝ) ≤
      K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
    calc
      log (D i : ℝ) ≤
          K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3 := hlogD i
      _ ≤ K * (u * ((i : ℝ) + 1)) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply pow_le_pow_left₀ _ (hscale i) 3
        linarith [log_natCast_nonneg (q * 2 ^ i)]
      _ = K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by ring
  let x : ℝ := 26 * K * u ^ 3 / log 2
  let B : ℕ := ⌈x⌉₊ + 1
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hBupper : (B : ℝ) ≤ x + 2 := by
    have hceil := (Nat.ceil_lt_add_one hx).le
    dsimp only [B]
    push_cast
    linarith
  have hcoef : 26 * K * u ^ 3 ≤ (B : ℝ) * log 2 := by
    have hxB : x ≤ (B : ℝ) := by
      have hceil := Nat.le_ceil x
      dsimp only [B]
      push_cast
      linarith
    exact (div_le_iff₀ hlog2pos).mp hxB
  refine ⟨B, hB, hBupper, ?_⟩
  intro i
  have hi : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ 3 := by
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [hi0] : (1 : ℝ) ≤ (i : ℝ) + 1) 3
    simpa using h
  have hlog0 : log (D 0 : ℝ) ≤ K * u ^ 3 := by simpa using hlogDi 0
  have hbudget : 24 * log (D 0 : ℝ) + 2 * log (D i : ℝ) ≤
      (B : ℝ) * ((i : ℝ) + 1) ^ 3 * log 2 := by
    have hbase : K * u ^ 3 ≤ K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ K * u ^ 3)
    have hfinal := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ ((i : ℝ) + 1) ^ 3)
    nlinarith [hlogDi i]
  have hDpos (j : ℕ) : 0 < (D j : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (hD j))
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hr)
  have hlogs : log ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) ≤
      log ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [log_mul (mul_pos hrpos (pow_pos (hDpos 0) _)).ne'
      (pow_pos (hDpos i) _).ne',
      log_mul hrpos.ne' (pow_pos (hDpos 0) _).ne',
      log_mul hrpos.ne' (by positivity), log_pow, log_pow, log_pow]
    push_cast
    nlinarith
  have hleftpos : 0 < ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact mul_pos (mul_pos hrpos (pow_pos (hDpos 0) _)) (pow_pos (hDpos i) _)
  have hrightpos : 0 < ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    push_cast
    exact mul_pos hrpos (by positivity)
  have hreal := (log_le_log_iff hleftpos hrightpos).mp hlogs
  exact_mod_cast hreal

end Real

namespace Entropy

/-- Cubic logarithmic bounds on approximation ranks and dyadic probability
tails give an entropy estimate with coefficient one on the logarithm of the
ground-space rank. This is a pure finite-probability auxiliary for ALVV,
arXiv:1602.08828v2, proof of `thm:al-dg`, lines 1085–1087. The probability
tail bounds are inputs here; no physical tail estimate is asserted. -/
theorem probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    {N : ℕ} (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, Real.log (D i : ℝ) ≤
      K * (1 + Real.log ((q * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3)
    (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (htail : ∀ i < N,
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * D 0 ^ 24 * D i ^ 2 ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1)) :
    let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    probabilityEntropy p ≤ Real.log (r : ℝ) + 676 * K * u ^ 3 + 54 * Real.log 2 := by
  intro u
  obtain ⟨B, hB, hBupper, hmajor⟩ :=
    Real.exists_cubic_dyadic_rank_majorant q r g K D hq hr hg hg1 hK hD hlogD
  have htailB (i : ℕ) (hi : i < N) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1) := by
    have hsubset :
        Finset.univ.filter (fun a : Fin N ↦ r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val) ⊆
        Finset.univ.filter (fun a : Fin N ↦ r * D 0 ^ 24 * D i ^ 2 ≤ a.val) := by
      intro a ha
      obtain ⟨hauniv, hlarge⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hauniv, (hmajor i).trans hlarge⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun a _ _ ↦ hp a)).trans (htail i hi)
  have hraw := probabilityEntropy_le_of_cubic_dyadic_rank_tail_bounds
    r B hr hB p hp hsum htailB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : (B : ℝ) * Real.log 2 ≤ 26 * K * u ^ 3 + 2 * Real.log 2 := by
    calc
      (B : ℝ) * Real.log 2 ≤
          (26 * K * u ^ 3 / Real.log 2 + 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hBupper hlog2.le
      _ = 26 * K * u ^ 3 + 2 * Real.log 2 := by
        rw [add_mul, div_mul_cancel₀ _ hlog2.ne']
  nlinarith only [hraw, hcoefficient]

end Entropy

namespace Real

/-- Absorb the finite dyadic entropy remainder into a uniform gap-dependent
coefficient. Auxiliary to ALVV, arXiv:1602.08828v2, entropy conclusion of
`thm:al-dg`, lines 1085–1087. -/
theorem dg_entropy_coefficient_bound
    (A g u S : ℝ) (r : ℕ) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 1 ≤ u)
    (hS : S ≤ log (r : ℝ) +
      676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
        54 * log 2) :
    S ≤ log (r : ℝ) +
      ((14872 * (A + 1) * (6 + 2 * log (A + 1)) + 54) / g) * u ^ 3 := by
  have hlog2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hu3 : 1 ≤ u ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hu 3
  have hscale : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by linarith)
  have hsmall : 54 * log 2 ≤ (54 : ℝ) / g * u ^ 3 := by
    calc
      54 * log 2 ≤ 54 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ ≤ 54 * (u ^ 3 / g) := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = 54 / g * u ^ 3 := by ring
  calc
    S ≤ log (r : ℝ) +
        676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
          54 * log 2 := hS
    _ ≤ log (r : ℝ) +
        676 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g) * u ^ 3 +
          54 / g * u ^ 3 := add_le_add_right hsmall _
    _ = log (r : ℝ) +
        ((14872 * (A + 1) * (6 + 2 * log (A + 1)) + 54) / g) * u ^ 3 := by ring

end Real
