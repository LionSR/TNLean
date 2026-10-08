/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SectorEncoder
import TNLean.MPS.Preparation.InjectivityCutoff

/-!
# All-accuracy compilation of coherent sector encoders

An exponentially accurate common-block conversion and an exact linear-depth whole-encoder
conversion give one logarithmic-depth unitary at every accuracy. The block scale accounts for
the square root in the polar-frame estimate. The exact branch acts on the entire canonical
encoder when this scale exceeds the physical ring length.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, discussion and outlook.
  The canonical whole-encoder conclusion is a precise enhancement of the conversion proposal.
-/

open Matrix MPSTensor QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace MPSPreparation

/-- A square-root exponential block error and an exact whole-encoder branch imply uniform
logarithmic-depth coherent conversion. All constants precede the length and accuracy. -/
theorem exists_log_depth_sectorEncoder_conversion_of_block_approximation
    {d b : ℕ} [NeZero d] {DA DB : Fin b → ℕ}
    (A : (j : Fin b) → MPSTensor d (DA j)) (B : (j : Fin b) → MPSTensor d (DB j))
    (L N₀ C : ℕ) (hN₀ : 2 ≤ N₀) (K r : ℝ) (hK : 1 ≤ K) (hr : 0 < r)
    (happrox : ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ q : ℕ, L ≤ q → q ≤ N →
      (N : ℝ) * Real.exp (-(r * q)) ≤ 1 →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ T ≤ C * q ∧
        ‖U * sectorEncoder A N - sectorEncoder B N‖ ≤
          K * Real.sqrt ((N : ℝ) * Real.exp (-(r * q))))
    (hexact : ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ T ≤ C * N ∧
        U * sectorEncoder A N = sectorEncoder B N) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        ‖U * sectorEncoder A N - sectorEncoder B N‖ ≤ ε := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hs : 0 < r / 2 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a := 1 / (r / 2)
  set bq : ℝ := max (Real.log K) 0 / (r / 2) + L + 1
  set c₀ := a + (bq + 1) / Real.log 2
  have ha : 0 < a := by positivity
  have hb : 1 ≤ bq := by
    have : 0 ≤ max (Real.log K) 0 / (r / 2) + L := by positivity
    dsimp [bq]; linarith
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨(C + 1) * c₀, by positivity, fun ε hε hε1 N _ hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (hN₀.trans hN)
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 < Real.log (N / ε) := hl2.trans_le hlog
  set Q := a * Real.log (N / ε) + bq
  set q := ⌈Q⌉₊
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hQ0 : 0 ≤ Q := by positivity
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one hQ0
  have hqL : L ≤ q := by
    have h0 : 0 ≤ a * Real.log (N / ε) + max (Real.log K) 0 / (r / 2) + 1 := by positivity
    have : (L : ℝ) ≤ q := by dsimp [Q, bq] at hQq; linarith
    exact_mod_cast this
  have hqlog : (q : ℝ) ≤ c₀ * Real.log (N / ε) := by
    have hbLog : bq + 1 ≤ (bq + 1) / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (by linarith)
    dsimp [c₀]
    rw [add_mul]
    dsimp [Q] at hqQ
    linarith
  have hdepth : ∀ T : ℕ, T ≤ C * q →
      (T : ℝ) ≤ ((C : ℝ) + 1) * c₀ * Real.log (N / ε) := by
    intro T hT
    have hT' : (T : ℝ) ≤ C * q := by exact_mod_cast hT
    calc (T : ℝ) ≤ C * q := hT'
      _ ≤ C * (c₀ * Real.log (N / ε)) := by gcongr
      _ ≤ (C + 1) * c₀ * Real.log (N / ε) := by nlinarith
  by_cases hqN : q ≤ N
  · set t := (N : ℝ) * Real.exp (-(r / 2 * q))
    have ht0 : 0 ≤ t := by positivity
    have hKt : K * t ≤ ε := by
      have h := mul_pow_mul_exp_neg_le_of_le (k := 1) hK0 hs (by linarith : (1 : ℝ) ≤ N)
        hε hε1 (a := a) (b := bq) (by simp [a])
        (by dsimp [bq]; have : (0 : ℝ) ≤ L := Nat.cast_nonneg _; linarith) hQq
      simpa only [pow_one] using h
    have ht1 : t ≤ 1 :=
      (le_mul_of_one_le_left ht0 hK).trans (hKt.trans hε1)
    have hexp : Real.exp (-(r / 2 * q)) ^ 2 = Real.exp (-(r * q)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hy : (N : ℝ) * Real.exp (-(r * q)) ≤ t ^ 2 := by
      dsimp [t]
      rw [mul_pow, hexp]
      gcongr
      nlinarith
    have hsmall : (N : ℝ) * Real.exp (-(r * q)) ≤ 1 :=
      hy.trans (by nlinarith)
    obtain ⟨U, T, hU, hT, herr⟩ := happrox N hN q hqL hqN hsmall
    refine ⟨U, T, hU, hdepth T hT, herr.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left ((Real.sqrt_le_left ht0).mpr hy) hK0.le).trans hKt
  · obtain ⟨U, T, hU, hT, heq⟩ := hexact N hN
    refine ⟨U, T, hU, hdepth T (hT.trans (Nat.mul_le_mul_left C (by omega))), ?_⟩
    rw [heq, sub_self, norm_zero]
    exact hε.le

end MPSPreparation
