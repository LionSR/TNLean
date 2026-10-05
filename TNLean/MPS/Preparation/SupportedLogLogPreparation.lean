/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CoherentBlockTreePreparation
import TNLean.MPS.Preparation.InjectivityCutoff
import TNLean.MPS.Preparation.LogLogDepthBound
import TNLean.MPS.Preparation.ShortChainPreparation

/-!
# Double-logarithmic compilation of supported block approximations

An exponentially accurate coherent block approximation, together with eventual support
injectivity, yields measurement-assisted preparation in double-logarithmic depth at every
admissible length. The exact whole-ring branch uses a supported pair only at `M = 1`.
Small rings below the fixed support scale use bounded exact synthesis.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements", "Long-range MPS using measurements",
  and Supplemental Material, proof of Theorem 1.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- Compile a coherent supported block approximation with error `K M exp(-r q)` to
all-length double-logarithmic measurement depth. Constants precede the length and accuracy;
the exact one-block hypothesis imposes no support condition at unused ring sizes. -/
theorem exists_log_log_preparation_of_supported_block_approximation
    {d D b : ℕ} (hd : 2 ≤ d) (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
    (L : ℕ) (hinj : ∀ m, L ≤ m → IsInjectiveOn (blockTensor A m) (S : Set _))
    (ω : Fin b → Fin D × Fin D → ℂ)
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0)
    (hωS : ∀ j {M : ℕ} (x : Fin M → Fin D × Fin D),
      pairProductState (ω j) x ≠ 0 → ∀ k, x k ∈ S)
    (target : ∀ N, MPVSpace d N) (admissible : ℕ → Prop)
    (htarget : ∀ N, admissible N → ‖target N‖ = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (happrox : ∀ N [NeZero N], admissible N → ∃ α : Fin b → ℂ,
      (∑ j, star (α j) * α j = 1) ∧
      ∀ M [NeZero M] (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N) (q : ℕ),
        L ≤ q → (∀ k, q ≤ ℓ k) →
        ‖∑ j, α j • blockIsometryState A (ω j) hN‖ = 1 ∧
        1 - ‖⟪∑ j, α j • blockIsometryState A (ω j) hN, target N⟫_ℂ‖ ≤
          K * (M * Real.exp (-(r * q))))
    (hexact : ∀ N [NeZero N], admissible N → L ≤ N →
      ∀ hN : ∑ _ : Fin 1, N = N, ∃ ω₁ : Fin D × Fin D → ℂ,
        (∑ p, star (ω₁ p) * ω₁ p = 1) ∧
        (∀ x : Fin 1 → Fin D × Fin D, pairProductState ω₁ x ≠ 0 → ∀ k, x k ∈ S) ∧
        blockIsometryState A ω₁ hN = target N) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → admissible N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, target N⟫_ℂ‖ ≤ ε := by
  classical
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨s, C, hs, hLs, hC⟩ :=
    exists_supported_block_preparation_constants hd A S (b + 1) L hinj
  have hs0 : 0 < s := by omega
  obtain ⟨Ks, hKs⟩ := exists_isPreparedInDepth_of_norm_eq_one hd0 (4 * s)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a := 1 / r with ha
  set bq : ℝ := max (Real.log K) 0 / r + 4 * s + 1 with hb
  have ha0 : 0 < a := by positivity
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hb0 : 0 ≤ bq := by positivity
  have hμ : 0 < Real.log (1 + Real.log 2) := Real.log_pos (by linarith)
  set c₀ := (C : ℝ) * ((1 + Real.logb 2 (a + bq + 1)) / Real.log (1 + Real.log 2) +
    1 / Real.log 2)
  have hc₀ : 0 ≤ c₀ := by
    have : 0 ≤ Real.logb 2 (a + bq + 1) := Real.logb_nonneg one_lt_two (by linarith)
    positivity
  refine ⟨c₀ + Ks / Real.log (1 + Real.log 2), fun ε hε hε1 N _ hN hvalid => ?_⟩
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
  have hself : 1 - ‖⟪target N, target N⟫_ℂ‖ ≤ ε := by
    rw [inner_self_eq_norm_sq_to_K, htarget N hvalid]
    norm_num [hε.le]
  set Q := a * Real.log (N / ε) + bq with hQ
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
    obtain ⟨α, hα, hαapprox⟩ := happrox N hvalid
    obtain ⟨hnorm, herr⟩ := hαapprox (m + 1) ℓ hsum q (by omega) hℓq
    obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 h4s
    set ψ := ∑ j, α j • blockIsometryState A (ω j) hsum
    have hψ : (fun x => ψ x) = fun x => ∑ j, α j * blockIsometryState A (ω j) hsum x := by
      funext x
      simp only [ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    refine ⟨ψ, C * (h + 1), hnorm, hc _ (Or.inl ?_), ?_, ?_⟩
    · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
      have : (2 : ℝ) ^ h ≤ q := by
        have : 2 ^ h ≤ q := by
          calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
            _ ≤ q := hh1
        exact_mod_cast this
      linarith
    · rw [hψ]
      exact hC (by omega) h ℓ hsum (fun k => hh1.trans (hℓq k))
        (fun k => (hℓ2 k).trans (by nlinarith)) ω hω (fun j x => hωS j x) α hα
    · refine herr.trans ?_
      -- `K M e^{-r q} ≤ ε` from `M ≤ N` and `r q ≥ log K + log(N/ε)`.
      have hMN : ((m + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hN0 : (0 : ℝ) < N := by linarith
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * (4 * s + 1) := by
          simp only [Q, bq, a]; field_simp; ring
        rw [Real.log_div hN0.ne' hε.ne'] at h2
        have : 0 ≤ r * (4 * s + 1) := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hN0 hε hrq
  · -- A whole-ring supported tree, even when the accuracy scale exceeds `N`.
    have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    by_cases hN4 : 4 * s ≤ N
    · have hN1 : ∑ _ : Fin 1, N = N := by simp
      obtain ⟨ω₁, hω₁, hω₁S, heq⟩ := hexact N hvalid (by omega) hN1
      obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 hN4
      refine ⟨target N, C * (h + 1), htarget N hvalid, hc _ (Or.inl ?_), ?_, hself⟩
      · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
        have : (2 : ℝ) ^ h ≤ N := by
          have : 2 ^ h ≤ N := by
            calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                  rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
              _ ≤ N := hh1
          exact_mod_cast this
        linarith
      · have hp := hC (b := 1) (by omega) h (fun _ : Fin 1 => N) hN1 (fun _ => hh1)
          (fun _ => by nlinarith) (fun _ => ω₁)
          (fun j j' => by simpa [Subsingleton.elim j j'] using hω₁)
          (fun _ x => hω₁S x) (fun _ => 1) (by simp)
        simpa only [Fin.sum_univ_one, one_mul, heq] using hp
    · have hψ := htarget N hvalid
      refine ⟨target N, Ks, hψ, hc _ (Or.inr le_rfl),
        isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth
          (isPreparedWithMeasurementsInDepth_of_isPreparedInDepth
            (hKs N hN (by omega) _ hψ) fun h' => ?_), hself⟩
      have : target N = 0 := by
        ext x; exact congrFun h' x
      rw [this, norm_zero] at hψ
      exact zero_ne_one hψ


end MPSPreparation
