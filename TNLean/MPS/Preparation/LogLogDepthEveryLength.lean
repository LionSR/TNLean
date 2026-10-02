/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.LogDepthPreparation
import TNLean.MPS.Preparation.UnequalTreePreparation

/-!
# Preparation with measurements in depth `O(log log(N/ε))`, every chain length

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 concludes that "this gives
a preparation algorithm for short-range correlated MPS with depth `O(log log(N/ε))`". This file
proves it for normal tensors and every chain length `N ≥ 2`.

* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero`:
  for every normal tensor `A` there is `c`, depending only on `A`, such that for `N ≥ 2`,
  `0 < ε ≤ 1` and `|φ_N(A)⟩ ≠ 0`, a unit vector with error at most `ε` is prepared with
  measurement rounds in depth at most `c log(log(N/ε) + 1)`, which is `O(log log(N/ε))`.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log`: the same for every
  `N ≥ N₀`, without the condition `|φ_N(A)⟩ ≠ 0`.

The block length is `q = ⌈a log(N/ε) + b⌉`, chosen after Lemma 1 of the source. For a chain at
least as long as `q`, the chain is cut into blocks "all of the same size, `q_N`, except for the
last one, which may be larger" (Supplemental Material, proof of Theorem 1), `q ≤ q' < 2q`; the
approximating state of these blocks has error at most `ε` by Lemma 1'(i) for blocks of unequal
lengths (`MPSTensor.exists_blockApproximationError_le_mul`), and it is prepared with measurements
by trees of `h + 1` coarse depths with `2^{h+2} s ≤ q < 2^{h+3} s`, on leaves of unequal widths
(`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState`), in depth
`C (h + 1) = O(log q)`. A shorter chain is one block, and `|φ_N⟩` itself is the state of that block
with the pair `ω ∝ P |𝟙⟩` (`MPSPreparation.blockIsometryState_normalizedTracePair`); a chain of
fewer than `4s` sites is prepared in bounded depth
(`MPSPreparation.exists_isPreparedInDepth_of_norm_eq_one`).

The register length `s` is the injectivity length of the tensor in the gauge of eq. (5) plus
`2`, so that a leg of a pair fits in a register with one site to spare.

**Local fix (nonvanishing periodic state):** as for eq. (1), the source takes `|φ_N⟩` to be the
normalized periodic state, which presupposes `|φ_N(A)⟩ ≠ 0`; the main theorem assumes it, and it
holds for every `N ≥ N₀`. Documented in
`docs/paper-gaps/mswc24_depth_upper_bound_nonzero_state.tex`.

## Main results

* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero`.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eqs. (1), (5), (10)–(12) and (16), Lemma 1 and
  Lemma 1'(i), the paragraph "Tree-RG circuit with measurements", and Supplemental Material,
  proof of Theorem 1.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

variable {d : ℕ}

/-- The depth `C (h + 1)` of trees with `2^h ≤ a X + b + 1` is at most a constant times
`log(X + 1)`, for `X ≥ log 2`. -/
private theorem natCast_mul_succ_le_mul_log {C h : ℕ} {a b X : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hX : Real.log 2 ≤ X) (hh : (2 : ℝ) ^ h ≤ a * X + b + 1) :
    ((C * (h + 1) : ℕ) : ℝ) ≤ C * ((1 + Real.logb 2 (a + b + 1)) / Real.log (1 + Real.log 2) +
      1 / Real.log 2) * Real.log (X + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hX0 : 0 ≤ X := hl2.le.trans hX
  have hμ : 0 < Real.log (1 + Real.log 2) := Real.log_pos (by linarith)
  have hLX : Real.log (1 + Real.log 2) ≤ Real.log (X + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos : 0 < a * X + b + 1 := by positivity
  have hh' : (h : ℝ) ≤ Real.logb 2 (a * X + b + 1) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hpos, Real.rpow_natCast]
    exact hh
  have hmul : a * X + b + 1 ≤ (a + b + 1) * (X + 1) := by nlinarith
  have hlog : Real.logb 2 (a * X + b + 1) ≤ Real.logb 2 (a + b + 1) + Real.logb 2 (X + 1) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact Real.logb_le_logb_of_le one_lt_two hpos hmul
  have hκ : 0 ≤ Real.logb 2 (a + b + 1) := Real.logb_nonneg one_lt_two (by linarith)
  set κ := 1 + Real.logb 2 (a + b + 1)
  have hκμ : κ ≤ κ / Real.log (1 + Real.log 2) * Real.log (X + 1) := by
    calc κ = κ / Real.log (1 + Real.log 2) * Real.log (1 + Real.log 2) := by field_simp
      _ ≤ κ / Real.log (1 + Real.log 2) * Real.log (X + 1) := by gcongr
  have hb2 : Real.logb 2 (X + 1) = 1 / Real.log 2 * Real.log (X + 1) := by
    rw [Real.logb]; ring
  have hsucc : (h : ℝ) + 1 ≤
      (κ / Real.log (1 + Real.log 2) + 1 / Real.log 2) * Real.log (X + 1) := by
    simp only [κ] at hκμ ⊢
    nlinarith
  push_cast
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  calc (C : ℝ) * (h + 1) ≤ C * ((κ / Real.log (1 + Real.log 2) + 1 / Real.log 2) *
        Real.log (X + 1)) := mul_le_mul_of_nonneg_left hsucc hC
    _ = _ := by ring

/-- A tree of `h + 1` coarse depths with `2^{h+2} s ≤ Y < 2^{h+3} s`, for `Y ≥ 4s`. -/
private theorem exists_two_pow_le {s Y : ℕ} (hs : 0 < s) (hY : 4 * s ≤ Y) :
    ∃ h : ℕ, 2 ^ (h + 2) * s ≤ Y ∧ Y < 2 ^ (h + 1) * (4 * s) := by
  have hq : Y / (4 * s) ≠ 0 := (Nat.div_pos hY (by omega)).ne'
  refine ⟨Nat.log 2 (Y / (4 * s)), ?_, ?_⟩
  · have h1 := Nat.pow_log_le_self 2 hq
    have h2 := Nat.div_mul_le_self Y (4 * s)
    calc 2 ^ (Nat.log 2 (Y / (4 * s)) + 2) * s = 2 ^ Nat.log 2 (Y / (4 * s)) * (4 * s) := by
          rw [pow_add]; ring
      _ ≤ Y / (4 * s) * (4 * s) := Nat.mul_le_mul_right _ h1
      _ ≤ Y := h2
  · have h1 := Nat.lt_pow_succ_log_self (b := 2) one_lt_two (Y / (4 * s))
    have h2 : Y < (Y / (4 * s) + 1) * (4 * s) := by
      have := Nat.lt_div_mul_add (a := Y) (b := 4 * s) (by omega)
      linarith
    calc Y < (Y / (4 * s) + 1) * (4 * s) := h2
      _ ≤ 2 ^ (Nat.log 2 (Y / (4 * s)) + 1) * (4 * s) := Nat.mul_le_mul_right _ h1

/-- **Preparation with measurements in depth `O(log log(N/ε))`, every chain length**
(arXiv:2307.01696, paragraph "Tree-RG circuit with measurements": "this gives a preparation
algorithm for short-range correlated MPS with depth `O(log log(N/ε))`"). For every normal tensor
`A` there is `c`, depending only on `A`, with the following property. For every `N ≥ 2` and
`0 < ε ≤ 1` such that the periodic state `|φ_N(A)⟩` does not vanish, some unit vector `|ψ⟩`
with `ε(ψ, φ_N) = 1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared with measurement rounds in depth at most
`c log(log(N/ε) + 1)`. No outcome is post-selected.

The block length is `q = ⌈a log(N/ε) + b⌉` (the sentence after Lemma 1: "$q = O (\log (N /
\epsilon))$"). If `q ≤ N`, the chain is cut into blocks "all of the same size, `q_N`, except for
the last one, which may be larger" (Supplemental Material, proof of Theorem 1), the error is at
most `ε` by Lemma 1'(i) (`MPSTensor.exists_blockApproximationError_le_mul`), and the trees of the
blocks have `O(log q)` depths
(`exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState`). If `N < q`, then `|φ_N⟩`
itself is prepared, by the tree of one block, or in bounded depth on fewer than `4s` sites.

The periodic state is assumed nonzero, as the source's normalization `c_N > 0` presupposes; see
the Local fix of the module docstring. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero {D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → mpvState A N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  -- Degenerate dimensions: the periodic state vanishes.
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext s; simp [mpvState_apply, Matrix.trace]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext s; exact (s ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩).elim0
  have : NeZero D := ⟨hD.ne'⟩
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, hinj⟩ :=
    exists_normalGaugeData hA
  set s := L + 2 with hsdef
  have hs0 : 0 < s := by omega
  have hinjs : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor B m) := fun m hm => hinj m (by omega)
  obtain ⟨C, hC⟩ := exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState d s (8 * s)
    (by omega)
  obtain ⟨Ks, hKs⟩ := exists_isPreparedInDepth_of_norm_eq_one hd (4 * s)
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
  set b : ℝ := max (Real.log K) 0 / r + 4 * s + 1 with hb
  have ha0 : 0 < a := by positivity
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hμ : 0 < Real.log (1 + Real.log 2) := Real.log_pos (by linarith)
  set c₀ := (C : ℝ) * ((1 + Real.logb 2 (a + b + 1)) / Real.log (1 + Real.log 2) +
    1 / Real.log 2)
  have hc₀ : 0 ≤ c₀ := by
    have : 0 ≤ Real.logb 2 (a + b + 1) := Real.logb_nonneg one_lt_two (by linarith)
    positivity
  refine ⟨c₀ + Ks / Real.log (1 + Real.log 2), fun ε hε hε1 N _ hN h0 => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  have hLX : Real.log (1 + Real.log 2) ≤ Real.log (Real.log (N / ε) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hLX0 : 0 ≤ Real.log (Real.log (N / ε) + 1) := hμ.le.trans hLX
  -- Each depth bound below is `c₀ log(log(N/ε) + 1)` or a bounded depth.
  have hc : ∀ T : ℕ, ((T : ℝ) ≤ c₀ * Real.log (Real.log (N / ε) + 1) ∨ T ≤ Ks) →
      (T : ℝ) ≤ (c₀ + Ks / Real.log (1 + Real.log 2)) * Real.log (Real.log (N / ε) + 1) := by
    intro T hT
    have h1 : 0 ≤ c₀ * Real.log (Real.log (N / ε) + 1) := by positivity
    have h2 : (Ks : ℝ) ≤ Ks / Real.log (1 + Real.log 2) * Real.log (Real.log (N / ε) + 1) := by
      calc (Ks : ℝ) = Ks / Real.log (1 + Real.log 2) * Real.log (1 + Real.log 2) := by
            field_simp
        _ ≤ _ := by gcongr
    have h3 : 0 ≤ Ks / Real.log (1 + Real.log 2) * Real.log (Real.log (N / ε) + 1) := by
      positivity
    rw [add_mul]
    rcases hT with h | h
    · linarith
    · have : (T : ℝ) ≤ Ks := by exact_mod_cast h
      linarith
  -- The error is unchanged by the gauge and the rescaling.
  have hphase := norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv N)
  have hself : ∀ v : MPVSpace d N, ‖v‖ = 1 → 1 - ‖⟪v, v⟫_ℂ‖ ≤ ε := fun v hv => by
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num [hε.le]
  have hB0 : mpvState B N ≠ 0 := by
    intro h
    apply h0
    ext x
    have := congrArg (fun v : MPVSpace d N => v x) h
    simp only [mpvState_apply, hmpv, PiLp.zero_apply] at this
    simpa [pow_ne_zero N hζ] using this
  set Q := a * Real.log (N / ε) + b with hQ
  set q := ⌈Q⌉₊ with hqdef
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by positivity)
  have h4s : 4 * s ≤ q := by
    have : ((4 * s : ℕ) : ℝ) ≤ q := by
      push_cast
      have : (0 : ℝ) ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r + 1 := by positivity
      linarith
    exact_mod_cast this
  by_cases hqN : q ≤ N
  · -- Long chains: `M - 1` blocks of length `q` and one of length `q' = q + N % q < 2q`.
    have hq0 : 0 < q := by omega
    obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
      ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq0)).symm⟩
    set ℓ : Fin (m + 1) → ℕ := fun k => if k = Fin.last m then q + N % q else q
    have hsum : ∑ k, ℓ k = N := by
      rw [Fin.sum_univ_castSucc]
      simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ite_true]
      have := Nat.div_add_mod N q
      rw [hm] at this
      linarith
    have hℓq : ∀ k, q ≤ ℓ k := fun k => by simp only [ℓ]; split_ifs <;> omega
    have hℓ2 : ∀ k, ℓ k ≤ 2 * q := fun k => by
      have := Nat.mod_lt N hq0
      simp only [ℓ]; split_ifs <;> omega
    have hinjℓ : ∀ k, Kraus.IsInjective (blockTensor B (ℓ k)) := fun k =>
      hinjs _ ((by omega : s ≤ q).trans (hℓq k))
    have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 h4s
    refine ⟨blockIsometryState B (fixedPointPair σ) hsum, C * (h + 1),
      norm_blockIsometryState B hω hsum hinjℓ, hc _ (Or.inl ?_),
      hC B hinjs _ hω h ℓ hsum (fun k => hh1.trans (hℓq k))
        (fun k => (hℓ2 k).trans (by nlinarith)), ?_⟩
    · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
      have : (2 : ℝ) ^ h ≤ q := by
        have : 2 ^ h ≤ q := by
          calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
            _ ≤ q := hh1
        exact_mod_cast this
      linarith
    · rw [← hphase]
      refine (herr (m + 1) ℓ hsum q hℓq hinjℓ).trans ?_
      rw [hexp]
      -- `K M e^{-r q} ≤ ε` from `M ≤ N` and `r q ≥ log K + log(N/ε)`.
      have hMN : ((m + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hN0 : (0 : ℝ) < N := by linarith
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr0.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * (4 * s + 1) := by
          simp only [Q, b, a]; field_simp; ring
        rw [Real.log_div hN0.ne' hε.ne'] at h2
        have : 0 ≤ r * (4 * s + 1) := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hN0 hε hrq
  · -- Short chains: `N < q`, and `|φ_N⟩` itself is prepared.
    have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    by_cases hN4 : 4 * s ≤ N
    · -- one block of `N` sites, with the pair `ω ∝ P |𝟙⟩`
      have hN1 : ∑ _ : Fin 1, N = N := by simp
      have hid := blockIsometryState_normalizedTracePair B N hN1
      have hinjN := hinjs N (by omega)
      have hω : ∑ p, star (normalizedTracePair B N p) * normalizedTracePair B N p = 1 := by
        have h := sum_star_blockIsometryState B (normalizedTracePair B N) hN1 fun _ => hinjN
        rw [pow_one, hid, sum_star_mul_self_eq_norm_sq, norm_normalizedMPVState hB0] at h
        rw [← h]; simp
      obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 hN4
      refine ⟨normalizedMPVState B N, C * (h + 1), norm_normalizedMPVState hB0,
        hc _ (Or.inl ?_), ?_, ?_⟩
      · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
        have : (2 : ℝ) ^ h ≤ N := by
          have : 2 ^ h ≤ N := by
            calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                  rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
              _ ≤ N := hh1
          exact_mod_cast this
        linarith
      · rw [← hid]
        exact hC B hinjs _ hω h (fun _ : Fin 1 => N) hN1 (fun _ => hh1)
          (fun _ => by nlinarith)
      · rw [← hphase]
        exact hself _ (norm_normalizedMPVState hB0)
    · -- fewer than `4s` sites: bounded depth
      have hψ := norm_normalizedMPVState h0
      refine ⟨normalizedMPVState A N, Ks, hψ, hc _ (Or.inr le_rfl),
        isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth
          (isPreparedWithMeasurementsInDepth_of_isPreparedInDepth
            (hKs N hN (by omega) _ hψ) fun h' => ?_), hself _ hψ⟩
      have : normalizedMPVState A N = 0 := by
        ext x; exact congrFun h' x
      rw [this, norm_zero] at hψ
      exact zero_ne_one hψ

/-- **Preparation with measurements in depth `O(log log(N/ε))`, long chains**
(arXiv:2307.01696, paragraph "Tree-RG circuit with measurements"). For every normal tensor `A`
with `D ≥ 1` there are `c` and `N₀`, depending only on `A`, such that for every `N ≥ N₀` and
`0 < ε ≤ 1`, some unit vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared with measurement rounds
in depth at most `c log(log(N/ε) + 1)`.

This is `exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero` together
with `exists_mpvState_ne_zero_of_le`. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_le_log_log {D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ (c : ℝ) (N₀ : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨c, hc⟩ := exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero
    A hA
  obtain ⟨N₀, hN₀⟩ := exists_mpvState_ne_zero_of_le A hA
  exact ⟨c, max N₀ 2, fun ε hε hε1 N _ hN =>
    hc ε hε hε1 N (le_of_max_le_right hN) (hN₀ N (le_of_max_le_left hN))⟩

end MPSPreparation
