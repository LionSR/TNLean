/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousExactPreparation
import TNLean.MPS.Preparation.InjectivityCutoff

/-!
# Accuracy-dependent inhomogeneous preparation under a uniform decay rate

An explicit pair-approximation bound `K N^k exp(-r q)`, with constants independent of the
ring length, gives preparation depth `O(log(N/ε))` at every positive ring length and every
`0 < ε ≤ 1`. Blocks have lengths between `q` and `2q`, so no divisibility assumption is
needed. If the chosen `q` exceeds `N`, exact linear-depth inhomogeneous preparation applies.

**Scope restriction (uniform rate):** arXiv:2307.01696 defines the inhomogeneous sequence by
convergence of its pair-approximation errors, without deriving the uniform exponential bound
assumed here. This is a conditional accuracy-dependent theorem, not a proof of that bound
from the source's finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main result

* `exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate`: the conditional
  accuracy-dependent depth bound, including every positive ring length.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and the choice of
  logarithmic blocking after Lemma 1 in the translation-invariant case.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- **Depth `O(log(N/ε))` under a uniform exponential pair-approximation rate.**
Suppose at every scale `1 ≤ q ≤ N` one family of inhomogeneous chains has a partition
with block lengths between `q` and `2q` and pair-approximation error at most
`K N^k exp(-r q)`, where `K,r > 0` and `k` are independent of the ring length. Then every normalized target state
has an approximation of error at most `ε` prepared in depth at most `C log(N/ε)`, for one
constant `C` and all positive ring lengths and `0 < ε ≤ 1`.

The uniform rate is an additional hypothesis, not a consequence proved here of the source's
finite-correlation assumption. See the scope restriction in the module docstring. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, VaryingBondChain d D N)
    (K r : ℝ) (k : ℕ) (hK : 0 < K) (hr : 0 < r)
    (hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (A N) hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D hd
  let a : ℝ := (k + 1) / r
  let b : ℝ := max (Real.log K) 0 / r + 3 * D + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 1 ≤ b := by
    have : 0 ≤ max (Real.log K) 0 / r + 3 * D := by positivity
    dsimp [b]
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c₀ := a + b / Real.log 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hc : 0 ≤ 4 * Cb * c₀ + Ce * c₀ := by positivity
  refine ⟨4 * Cb * c₀ + Ce * c₀, fun ε hε hε1 N _ => ?_⟩
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hn : ‖state (A N)‖ ≠ 0 := by
    obtain ⟨M, _, ℓ, hsum, _, _, hA⟩ := hrate N N hNpos le_rfl
    rw [state_eq_chainState, norm_chainState_eq _ hsum]
    exact norm_ne_zero_iff.mpr hA.1
  have hu : ‖(‖state (A N)‖ : ℂ)⁻¹ • state (A N)‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hn]
  have hself : 1 - ‖⟪(‖state (A N)‖ : ℂ)⁻¹ • state (A N),
      (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    simpa using hε.le
  by_cases hN1 : N = 1
  · subst N
    refine ⟨_, 0, hu, ?_, isPreparedInDepth_zero_one_site _, hself⟩
    have hlog : 0 ≤ Real.log ((1 : ℝ) / ε) :=
      Real.log_nonneg ((one_le_div hε).2 hε1)
    simpa using mul_nonneg hc hlog
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  let Q := a * Real.log (N / ε) + b
  have hQ1 : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQc : Q ≤ c₀ * Real.log (N / ε) := by
    have hbl : b ≤ b / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hb)
    dsimp [Q, c₀]
    rw [add_mul]
    linarith
  let q := ⌈Q⌉₊
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  by_cases hqN : q ≤ N
  · obtain ⟨M, hM, ℓ, hsum, hℓq, hℓ2q, happ⟩ := hrate N q hq0 hqN
    letI : NeZero M := ⟨hM.ne'⟩
    have h3Dq : 3 * D ≤ q := by
      have hbD : (3 * D : ℝ) ≤ b := by
        have : 0 ≤ max (Real.log K) 0 / r := by positivity
        dsimp [b]
        linarith
      have hDq : (3 * D : ℝ) ≤ q := by dsimp [Q] at hQq; nlinarith
      exact_mod_cast hDq
    obtain ⟨ψ, hψ, hprep, herr⟩ := hCb ℓ hsum (A N) (2 * q)
      (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))
      (fun j => h3Dq.trans (hℓq j)) hℓ2q happ
    refine ⟨ψ, Cb * (2 * q), hψ, ?_, hprep, herr.trans ?_⟩
    · push_cast
      have hCb0 : (0 : ℝ) ≤ Cb := Nat.cast_nonneg _
      have hCe : 0 ≤ Ce * c₀ * Real.log (N / ε) := by positivity
      calc (Cb : ℝ) * (2 * q) ≤ 4 * Cb * Q := by nlinarith
        _ ≤ 4 * Cb * (c₀ * Real.log (N / ε)) := by gcongr
        _ ≤ (4 * Cb * c₀ + Ce * c₀) * Real.log (N / ε) := by nlinarith
    · apply mul_mul_exp_neg_le_of_log_le hK (pow_pos hNpos' k) hε
      rw [Real.log_pow]
      have hrQ : r * Q = (k + 1) * Real.log (N / ε) + max (Real.log K) 0 +
          r * (3 * D + 1) := by
        dsimp [Q, a, b]
        field_simp
        ring
      have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
      have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
      have hprod : (k : ℝ) * Real.log ε ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hlogε
      rw [Real.log_div hNpos'.ne' hε.ne'] at hrQ
      have hq : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr.le
      have hmax := le_max_left (Real.log K) 0
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      nlinarith
  · obtain ⟨T, hT, hprep⟩ := hCe N (zeroPad (A N)) (by
      rw [← state_eq_chainState]
      exact norm_ne_zero_iff.mp hn)
    refine ⟨_, T, hu, ?_, ?_, hself⟩
    · have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
      have hT' : (T : ℝ) ≤ Ce * N := by exact_mod_cast hT
      have hCe0 : (0 : ℝ) ≤ Ce := Nat.cast_nonneg _
      have hCextra : 0 ≤ 4 * Cb * c₀ * Real.log (N / ε) := by positivity
      calc (T : ℝ) ≤ Ce * N := hT'
        _ ≤ Ce * Q := by gcongr
        _ ≤ Ce * (c₀ * Real.log (N / ε)) := by gcongr
        _ ≤ (4 * Cb * c₀ + Ce * c₀) * Real.log (N / ε) := by nlinarith
    · simpa only [← state_eq_chainState] using hprep

end MPSPreparation
