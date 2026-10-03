/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockApproximationError
import TNLean.MPS.Preparation.DepthLogBound
import TNLean.MPS.Preparation.ShortChainPreparation

/-!
# Preparation of a normal translation-invariant MPS in depth `O(log(N/ε))`, every chain length

This file proves eq. (1) of arXiv:2307.01696: a normal translation-invariant MPS on `N` sites is
prepared with error `ε` by a local circuit of depth `T = O(log(N/ε))`. It combines the depth
count for the approximating state (`MPSPreparation.exists_isPreparedInDepth_blockIsometryState`)
with the approximation error of Lemma 1'(i) (`MPSTensor.exists_blockApproximationError_le_mul`),
for the block length `q ∝ log(N/ε)` chosen after Lemma 1 of the source ("it follows that
$q = O (\log (N / \epsilon))$").

* `MPSPreparation.exists_isPreparedInDepth_le_log_of_mpvState_ne_zero`: for every normal tensor
  `A` there is `c`, depending only on `A`, such that for `N ≥ 2`, `0 < ε ≤ 1` and
  `|φ_N(A)⟩ ≠ 0`, a unit vector with error at most `ε` is prepared in depth at most
  `c log(N/ε)`. This is eq. (1) of the source.
* `MPSPreparation.exists_isPreparedInDepth_le_log`: the same for every `N ≥ N₀`, without the
  condition `|φ_N(A)⟩ ≠ 0`, which holds for all `N ≥ N₀`
  (`MPSPreparation.exists_mpvState_ne_zero_of_le`).

The case of a block length dividing `N`, with the approximating state of eq. (10) itself, is
`TNLean.MPS.Preparation.DepthLogBound`.

For a chain at least as long as the block length `q = ⌈a log(N/ε) + b⌉`, the chain is cut into
blocks "all of the same size, `q_N`, except for the last one, which may be larger", as in the
Supplemental Material, proof of Theorem 1: `N = (M - 1) q + q'` with `q ≤ q' < 2q`. A shorter
chain, `N < q`, carries no block of length `q`; there `|φ_N⟩` is prepared exactly, in depth `O(N)`
for `N` beyond the injectivity length (`MPSPreparation.exists_isPreparedInDepth_normalizedMPVState`)
and in bounded depth below it (`MPSPreparation.exists_isPreparedInDepth_of_norm_eq_one`). Since
`N < q ≤ a log(N/ε) + b + 1`, both depths are `O(log(N/ε))`.

**Local fix (nonvanishing periodic state):** the source takes `|φ_N⟩` to be the normalized
periodic state, which presupposes `|φ_N(A)⟩ ≠ 0`; the main theorem assumes it. It fails for some
normal tensors at small `N`, and holds for every `N ≥ N₀`. Documented in
`docs/paper-gaps/mswc24_depth_upper_bound_nonzero_state.tex`.

The tensor is not assumed to be in the gauge of eq. (5) of the source: a normal tensor is brought
into it by a gauge transformation and a rescaling
(`MPSTensor.exists_isPrimitiveMPS_gauge_of_isNormal`), which change the normalized state
`|φ_N⟩` only by a phase.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

variable {d : ℕ}

/-- **Preparation in depth `O(log(N/ε))`** (arXiv:2307.01696, eq. (1)). For every normal tensor
`A` there is `c`, depending only on `A`, with the following property. For every `N ≥ 2` and
`0 < ε ≤ 1` such that the periodic state `|φ_N(A)⟩` does not vanish, some unit vector `|ψ⟩` with
`ε(ψ, φ_N) = 1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a product state in depth at most
`c log(N/ε)`.

arXiv:2307.01696, eq. (1) (`T=O(\log (N/\eps))`), with the block length
`q = ⌈a log(N/ε) + b⌉` of the sentence after Lemma 1 ("it follows that
$q = O (\log (N / \epsilon))$"). If `q ≤ N`, the chain is cut into blocks "all of the same size,
`q_N`, except for the last one, which may be larger" (Supplemental Material, proof of
Theorem 1), `N = (M - 1) q + q'` with `q ≤ q' < 2q`; the approximating state of these blocks has
error at most `K M e^{-r q} ≤ ε` (`MPSTensor.exists_blockApproximationError_le_mul`) and depth
at most `C q' ≤ 2 C q` (`exists_isPreparedInDepth_blockIsometryState`). If `N < q`, then
`N < a log(N/ε) + b` and `|φ_N⟩` itself is prepared in depth `O(N)`
(`exists_isPreparedInDepth_normalizedMPVState`), or in bounded depth when `N` is below the
injectivity length plus `3D` (`exists_isPreparedInDepth_of_norm_eq_one`).

The periodic state is assumed nonzero, as the source's normalization `c_N > 0` presupposes; see
the Local fix of the module docstring. -/
theorem exists_isPreparedInDepth_le_log_of_mpvState_ne_zero {D : ℕ} (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → mpvState A N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧ 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  -- Degenerate dimensions: the periodic state vanishes.
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext s; simp [mpvState_apply, Matrix.trace]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext s; exact (s ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩).elim0
  have : NeZero D := ⟨hD.ne'⟩
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_blockIsometryState d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedMPVState d D
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, hinj⟩ :=
    exists_normalGaugeData hA
  obtain ⟨Ks, hKs⟩ := exists_isPreparedInDepth_of_norm_eq_one hd (L + 3 * D)
  -- Lemma 1'(i) with `γ = 1/4`, for blocks of unequal lengths.
  obtain ⟨K, hK, herr⟩ := exists_blockApproximationError_le_mul B hNB hLC hσ htr hfix hlam
    (by rw [hnorm]; exact ht1.le) (γ := 1 / 4) (by norm_num) (by norm_num)
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a := 1 / r with ha
  set b : ℝ := max (Real.log K) 0 / r + L + 3 * D + 1 with hb
  have ha0 : 0 < a := by positivity
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hb1 : 1 ≤ b := by have : (0 : ℝ) ≤ L + 3 * D := by positivity
                         linarith
  set c₀ := a + b / Real.log 2
  have hc₀ : 0 ≤ c₀ := by positivity
  refine ⟨4 * Cb * c₀ + Ce * c₀ + Ks / Real.log 2, fun ε hε hε1 N _ hN h0 => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  set Q := a * Real.log (N / ε) + b with hQ
  have hQ1 : 1 ≤ Q := by have : 0 ≤ a * Real.log (N / ε) := by positivity
                         linarith
  have hQc : Q ≤ c₀ * Real.log (N / ε) := by
    have hbl : b ≤ b / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hb1)
    simp only [c₀, add_mul]
    linarith
  -- Each depth bound below is a multiple of `log(N/ε)`.
  have hc : ∀ T : ℕ, ((T : ℝ) ≤ 4 * Cb * c₀ * Real.log (N / ε) ∨
      (T : ℝ) ≤ Ce * c₀ * Real.log (N / ε) ∨ (T : ℝ) ≤ Ks / Real.log 2 * Real.log (N / ε)) →
      (T : ℝ) ≤ (4 * Cb * c₀ + Ce * c₀ + Ks / Real.log 2) * Real.log (N / ε) := by
    intro T hT
    have h1 : 0 ≤ 4 * Cb * c₀ * Real.log (N / ε) := by positivity
    have h2 : 0 ≤ Ce * c₀ * Real.log (N / ε) := by positivity
    have h3 : 0 ≤ Ks / Real.log 2 * Real.log (N / ε) := by positivity
    rw [add_mul, add_mul]
    rcases hT with h | h | h <;> linarith
  -- The error is unchanged by the gauge and the rescaling.
  have hphase := norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv N)
  have hself : ∀ v : MPVSpace d N, ‖v‖ = 1 → 1 - ‖⟪v, v⟫_ℂ‖ ≤ ε := fun v hv => by
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num [hε.le]
  set q := ⌈Q⌉₊ with hqdef
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  by_cases hqN : q ≤ N
  · -- Long chains: `M - 1` blocks of length `q` and one of length `q' = q + N % q < 2q`.
    obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
      ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq0)).symm⟩
    set q' := q + N % q
    set ℓ : Fin (m + 1) → ℕ := fun k => if k = Fin.last m then q' else q
    have hsum : ∑ k, ℓ k = N := by
      rw [Fin.sum_univ_castSucc]
      simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ite_true]
      have := Nat.div_add_mod N q
      rw [hm] at this
      simp only [q']
      linarith
    have hℓq : ∀ k, q ≤ ℓ k := fun k => by simp only [ℓ]; split_ifs <;> omega
    have hℓ2 : ∀ k, ℓ k ≤ 2 * q := fun k => by
      have := Nat.mod_lt N hq0
      simp only [ℓ, q']; split_ifs <;> omega
    have hLq : (L : ℝ) ≤ q := by
      have : (0 : ℝ) ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r + 3 * D + 1 := by positivity
      linarith
    have hDq : ((3 * D : ℕ) : ℝ) ≤ q := by
      push_cast
      have : (0 : ℝ) ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r + L + 1 := by positivity
      linarith
    have hinjℓ : ∀ k, Kraus.IsInjective (blockTensor B (ℓ k)) := fun k =>
      hinj _ ((show L ≤ q by exact_mod_cast hLq).trans (hℓq k))
    have h3D : ∀ k, 3 * D ≤ ℓ k := fun k =>
      (show 3 * D ≤ q by exact_mod_cast hDq).trans (hℓq k)
    have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    refine ⟨blockIsometryState B (fixedPointPair σ) hsum, Cb * (2 * q),
      norm_blockIsometryState B hω hsum hinjℓ, hc _ (Or.inl ?_),
      hCb B _ hω ℓ hsum (2 * q) h3D hℓ2 hinjℓ, ?_⟩
    · push_cast
      have : (0 : ℝ) ≤ Cb := Nat.cast_nonneg _
      nlinarith
    · rw [← hphase]
      refine (herr (m + 1) ℓ hsum q hℓq hinjℓ).trans ?_
      rw [hexp]
      -- `K M e^{-r q} ≤ ε` from `M ≤ N` and `r q ≥ log K + log(N/ε)`.
      have hMN : ((m + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hN0 : (0 : ℝ) < N := by linarith
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr0.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * (L + 3 * D + 1) := by
          simp only [Q, b, a]; field_simp; ring
        rw [Real.log_div hN0.ne' hε.ne'] at h2
        have : 0 ≤ r * (L + 3 * D + 1) := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hN0 hε hrq
  · -- Short chains: `N < a log(N/ε) + b`, and `|φ_N⟩` is prepared exactly.
    have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    have hB0 : mpvState B N ≠ 0 := by
      intro h
      apply h0
      ext s
      have := congrArg (fun v : MPVSpace d N => v s) h
      simp only [mpvState_apply, hmpv, PiLp.zero_apply] at this
      simpa [pow_ne_zero N hζ] using this
    by_cases hNL : L + 3 * D ≤ N
    · refine ⟨normalizedMPVState B N, Ce * N, norm_normalizedMPVState hB0,
        hc _ (Or.inr (Or.inl ?_)), hCe B N (by omega) (hinj N (by omega)) hB0, ?_⟩
      · push_cast
        have : (0 : ℝ) ≤ Ce := Nat.cast_nonneg _
        calc (Ce : ℝ) * N ≤ Ce * Q := by gcongr
          _ ≤ Ce * (c₀ * Real.log (N / ε)) := by gcongr
          _ = Ce * c₀ * Real.log (N / ε) := by ring
      · rw [← hphase]
        exact hself _ (norm_normalizedMPVState hB0)
    · refine ⟨normalizedMPVState A N, Ks, norm_normalizedMPVState h0,
        hc _ (Or.inr (Or.inr ?_)), hKs N hN (by omega) _ (norm_normalizedMPVState h0),
        hself _ (norm_normalizedMPVState h0)⟩
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)

/-- **The periodic state of a normal tensor does not vanish on long chains.** For a normal
tensor `A` there is `N₀` with `|φ_N(A)⟩ ≠ 0` for all `N ≥ N₀`: in the gauge of eq. (5) of
arXiv:2307.01696, `‖φ_N‖² = Tr E^N → 1` (Supplemental Material, proof of Lemma 1'(i):
`|c_N - 1| = O(e^{-N/ξ})`). -/
theorem exists_mpvState_ne_zero_of_le {D : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → mpvState A N ≠ 0 := by
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, -⟩ :=
    exists_normalGaugeData hA
  obtain ⟨K, hK, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le B hNB hLC hσ htr hfix hlam
    (γ := 1 / 4) (by norm_num) (by norm_num)
  set x := Real.exp (-(1 / 4) / correlationLength (t : ℂ))
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [Real.exp_lt_one_iff, neg_div_correlationLength, hnorm]
    exact mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg ht0 ht1)
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (K + 1) by positivity) hx1
  refine ⟨N₀, fun N hN h0 => ?_⟩
  have hB0 : mpvState B N = 0 := by
    ext s
    rw [mpvState_apply, hmpv]
    have := congrArg (fun v : MPVSpace d N => v s) h0
    simp only [mpvState_apply, PiLp.zero_apply] at this
    rw [this, mul_zero, PiLp.zero_apply]
  have h1 := hc N
  rw [hB0, norm_zero] at h1
  have h2 : x ^ N ≤ x ^ N₀ := pow_le_pow_of_le_one hx0 hx1.le hN
  have h3 : K * x ^ N < 1 := by
    calc K * x ^ N ≤ K * x ^ N₀ := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ (K + 1) * x ^ N₀ := by nlinarith [pow_nonneg hx0 N₀]
      _ < (K + 1) * (1 / (K + 1)) := by gcongr
      _ = 1 := by field_simp
  norm_num at h1
  linarith

/-- **Preparation in depth `O(log(N/ε))`, long chains** (arXiv:2307.01696, eq. (1)). For every
normal tensor `A` with `D ≥ 1` there are `c` and `N₀`, depending only on `A`, such that for every
`N ≥ N₀` and `0 < ε ≤ 1`, some unit vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a
product state in depth at most `c log(N/ε)`.

This is `exists_isPreparedInDepth_le_log_of_mpvState_ne_zero` together with
`exists_mpvState_ne_zero_of_le`; eq. (1) is an asymptotic statement, and no condition on `N` or
`ε` other than `N ≥ N₀` is needed. -/
theorem exists_isPreparedInDepth_le_log {D : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ (c : ℝ) (N₀ : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧ 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨c, hc⟩ := exists_isPreparedInDepth_le_log_of_mpvState_ne_zero A hA
  obtain ⟨N₀, hN₀⟩ := exists_mpvState_ne_zero_of_le A hA
  exact ⟨c, max N₀ 2, fun ε hε hε1 N _ hN =>
    hc ε hε hε1 N (le_of_max_le_right hN) (hN₀ N (le_of_max_le_left hN))⟩

end MPSPreparation
