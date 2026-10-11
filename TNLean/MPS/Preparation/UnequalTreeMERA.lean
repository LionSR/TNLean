/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.UnequalMERA
import TNLean.MPS.Preparation.PolarIsometryTree
import TNLean.MPS.Preparation.LogDepthPreparation
import TNLean.MPS.Preparation.RemainderBlocks

/-!
# Finite-range MERA approximations at every positive chain length

For a normal tensor, the virtual dimensions and the maximum physical leaf width can
be fixed before choosing either the chain length or the accuracy. Unequal blocks carry
binary polar trees with vertex-dependent isometries. Their contraction is the unequal-block
approximating state, so its existing overlap estimate applies without a divisibility condition.

If the accuracy-selected block length exceeds the chain length, one polar tree represents
the normalized state exactly, with the normalized trace pair at its root. Its leaf width
remains uniformly bounded. The finitely shorter chains use a bond-one bounded leaf.

The layer bound is `C (1 + log(1 + max(0, log(N/ε))))`. This regularized expression includes
single-site chains and accuracies above one; asymptotically it is `O(log log(N/ε))`.
The periodic state must be nonzero for its normalization to be defined as a unit vector.

Source: arXiv:2307.01696, eqs. (10), (16), the paragraph "Connection to MERA", and the
Supplemental Material, proof of Theorem 1, with its possibly larger last block.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

private theorem exists_power_mul_bounds {s Y : ℕ} (hs : 0 < s) (hY : s ≤ Y) :
    ∃ h : ℕ, 2 ^ h * s ≤ Y ∧ Y < 2 ^ h * (2 * s) := by
  have hq : Y / s ≠ 0 := (Nat.div_pos hY hs).ne'
  refine ⟨Nat.log 2 (Y / s), ?_, ?_⟩
  · exact (Nat.mul_le_mul_right s (Nat.pow_log_le_self 2 hq)).trans (Nat.div_mul_le_self Y s)
  · have h1 := Nat.lt_pow_succ_log_self (b := 2) one_lt_two (Y / s)
    have h2 : Y < (Y / s + 1) * s := by
      have := Nat.lt_div_mul_add (a := Y) (b := s) hs
      nlinarith
    calc Y < (Y / s + 1) * s := h2
      _ ≤ 2 ^ (Nat.log 2 (Y / s) + 1) * s := Nat.mul_le_mul_right s h1
      _ = 2 ^ Nat.log 2 (Y / s) * (2 * s) := by rw [pow_succ]; ring

private theorem tree_height_bound {a b X : ℝ} {h : ℕ} (ha : 0 < a) (hb : 0 ≤ b)
    (hX : 0 ≤ X) (hh : (2 : ℝ) ^ h ≤ a * X + b + 1) :
    ((h + 2 : ℕ) : ℝ) ≤ (2 + Real.logb 2 (a + b + 1) + 1 / Real.log 2) *
      (1 + Real.log (X + 1)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp : 0 < a * X + b + 1 := by positivity
  have hh' : (h : ℝ) ≤ Real.logb 2 (a * X + b + 1) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hp, Real.rpow_natCast]
    exact hh
  have hmul : a * X + b + 1 ≤ (a + b + 1) * (X + 1) := by nlinarith
  have hlog : Real.logb 2 (a * X + b + 1) ≤
      Real.logb 2 (a + b + 1) + Real.logb 2 (X + 1) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact Real.logb_le_logb_of_le one_lt_two hp hmul
  have hk : 0 ≤ Real.logb 2 (a + b + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have ht : 0 ≤ 1 / Real.log 2 := by positivity
  have hL : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hb2 : Real.logb 2 (X + 1) = 1 / Real.log 2 * Real.log (X + 1) := by
    rw [Real.logb]; ring
  rw [hb2] at hlog
  have hcross : 0 ≤ (2 + Real.logb 2 (a + b + 1)) * Real.log (X + 1) :=
    mul_nonneg (by linarith) hL
  push_cast
  nlinarith

private theorem exists_polarForest {d D s h c M N : ℕ} (A : MPSTensor d D)
    (hD : 0 < D) (hs : 0 < s) (hM : 0 < M)
    (hinj : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m))
    (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N)
    (hlower : ∀ k, 2 ^ h * s ≤ ℓ k) (hupper : ∀ k, ℓ k ≤ 2 ^ h * c)
    (ω : Fin D × Fin D → ℂ) (hω : ∑ p, star (ω p) * ω p = 1) :
    ∃ 𝓜 : UnequalMERA d D c h N, 𝓜.state = blockIsometryState A ω hN := by
  classical
  choose T hT using fun k =>
    exists_isometryTree_matrix_eq_cfgPolarIso A hs hinj h (ℓ k) c (hlower k) (hupper k)
  exact UnequalMERA.exists_of_trees_eq_blockIsometryState hD A hM hN T hT ω hω

/-- **Every-length bounded-dimension MERA approximation.** For a normal tensor, there are
constants `R ≥ 1` and `C ≥ 2`, independent of `N` and `ε`, such that every nonzero periodic
state on a positive chain has, for every `ε > 0`, a unit MERA state with error at most `ε`.
Each top-pair leg has dimension at most `D`, internal tree legs have dimension at most `D²`,
every physical leaf has at most `R` sites, and the total
number of layers is bounded by `C (1 + log(1 + max(0, log(N/ε))))`.

The forest is explicitly a tree of isometries, including its unitary top disentangler.
All lower disentanglers are identities. The regularization includes single-site chains and
accuracies above one; the large-size bound is `O(log log(N/ε))`.

Source: arXiv:2307.01696, eq. (16), the paragraph "Connection to MERA", and the unequal-block
partition in the proof of Theorem 1.

**Local fix (nonvanishing periodic state):** The nonzero-state hypothesis is required
for normalization. See `docs/paper-gaps/mswc24_depth_upper_bound_nonzero_state.tex`. -/
theorem exists_unequalMERA_every_length {d D : ℕ} (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ R : ℕ, 1 ≤ R ∧ ∃ C : ℝ, 2 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ∀ (N : ℕ) [NeZero N], mpvState A N ≠ 0 →
        ∃ (D' h : ℕ) (𝓜 : UnequalMERA d D' R h N), D' ≤ D ∧
          ((h + 2 : ℕ) : ℝ) ≤ C * (1 + Real.log (1 + max 0 (Real.log (N / ε)))) ∧
          1 - ‖⟪𝓜.state, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨1, le_rfl, 2, le_rfl, fun ε _ N _ h0 => absurd ?_ h0⟩
    ext s; simp [mpvState_apply, Matrix.trace]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, le_rfl, 2, le_rfl, fun ε _ N _ h0 => absurd ?_ h0⟩
    ext s; exact (s ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩).elim0
  have : NeZero D := ⟨hD.ne'⟩
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, hinj⟩ :=
    exists_normalGaugeData hA
  set s := L + 1 with hsdef
  have hs0 : 0 < s := by omega
  have hinjs : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor B m) := fun m hm => hinj m (by omega)
  obtain ⟨K, hK, herr⟩ := exists_blockApproximationError_le_mul B hNB hLC hσ htr hfix hlam
    (by rw [hnorm]; exact ht1.le) (γ := 1 / 2) (by norm_num) (by norm_num)
  set r := -Real.log t with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(2 * (1 / 2)) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  set a := 1 / r with ha
  set b : ℝ := max (Real.log K) 0 / r + s + 1 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set C := 2 + Real.logb 2 (a + b + 1) + 1 / Real.log 2 with hCdef
  have hC : 2 ≤ C := by
    have : 0 ≤ Real.logb 2 (a + b + 1) := Real.logb_nonneg one_lt_two (by linarith)
    have hden : 0 ≤ 1 / Real.log 2 := by
      have : 0 < Real.log 2 := Real.log_pos one_lt_two
      positivity
    dsimp [C]
    linarith
  refine ⟨4 * s, by omega, C, hC, fun ε hε N _ h0 => ?_⟩
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcap : (2 : ℝ) ≤ C * (1 + Real.log (1 + max 0 (Real.log (N / ε)))) := by
    have hlog : 0 ≤ Real.log (1 + max 0 (Real.log (N / ε))) :=
      Real.log_nonneg (by linarith [le_max_left 0 (Real.log (N / ε))])
    have : 0 ≤ C * Real.log (1 + max 0 (Real.log (N / ε))) :=
      mul_nonneg (by linarith) hlog
    nlinarith
  by_cases hε1 : ε ≤ 1
  swap
  · obtain ⟨𝓜⟩ := UnequalMERA.nonempty_bond_one hd hN0 (by omega : 1 ≤ 4 * s)
    refine ⟨1, 0, 𝓜, hD, hcap, ?_⟩
    have := norm_nonneg ⟪𝓜.state, normalizedMPVState A N⟫_ℂ
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hlog0 : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg (hN1.trans (le_div_self (by positivity) hε hε1))
  have hdepth : ∀ h : ℕ, (2 : ℝ) ^ h ≤ a * Real.log (N / ε) + b + 1 →
      ((h + 2 : ℕ) : ℝ) ≤ C * (1 + Real.log (1 + max 0 (Real.log (N / ε)))) := by
    intro h hh
    simpa only [max_eq_right hlog0, add_comm (1 : ℝ) (Real.log (N / ε))] using
      (tree_height_bound ha0 hb0 hlog0 hh)
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
  have hsq : s ≤ q := by
    have : (s : ℝ) ≤ q := by
      have hnonneg : 0 ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r + 1 := by positivity
      dsimp [Q, b] at hQq
      linarith
    exact_mod_cast this
  by_cases hqN : q ≤ N
  · have hq0 : 0 < q := hs0.trans_le hsq
    obtain ⟨m, ℓ, hm, hsum, hℓq, hℓ2⟩ := exists_remainderBlocks hq0 hqN
    have hinjℓ : ∀ k, Kraus.IsInjective (blockTensor B (ℓ k)) := fun k =>
      hinjs _ (hsq.trans (hℓq k))
    have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    obtain ⟨h, hh1, hh2⟩ := exists_power_mul_bounds hs0 hsq
    obtain ⟨𝓜, h𝓜⟩ := exists_polarForest (c := 4 * s) B hD hs0 (Nat.succ_pos m) hinjs ℓ hsum
      (fun k => hh1.trans (hℓq k)) (fun k => (hℓ2 k).trans (by nlinarith))
      (fixedPointPair σ) hω
    refine ⟨D, h, 𝓜, le_rfl, hdepth h ?_, ?_⟩
    · have hp : 2 ^ h ≤ q := (Nat.le_mul_of_pos_right _ hs0).trans hh1
      have hp' : (2 : ℝ) ^ h ≤ q := by exact_mod_cast hp
      linarith
    · rw [h𝓜, ← hphase]
      refine (herr (m + 1) ℓ hsum q hℓq hinjℓ).trans ?_
      rw [hexp]
      have hMN : ((m + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr0.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * (s + 1) := by
          simp only [Q, b, a]; field_simp; ring
        rw [Real.log_div hNpos.ne' hε.ne'] at h2
        have : 0 ≤ r * (s + 1) := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hNpos hε hrq
  · have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    by_cases hsN : s ≤ N
    · have hsum : ∑ _ : Fin 1, N = N := by simp
      have hid := blockIsometryState_normalizedTracePair B N hsum
      have hinjN := hinjs N hsN
      have hω : ∑ p, star (normalizedTracePair B N p) * normalizedTracePair B N p = 1 := by
        have hv := sum_star_blockIsometryState B (normalizedTracePair B N) hsum fun _ => hinjN
        rw [pow_one, hid, sum_star_mul_self_eq_norm_sq, norm_normalizedMPVState hB0] at hv
        rw [← hv]; simp
      obtain ⟨h, hh1, hh2⟩ := exists_power_mul_bounds hs0 hsN
      obtain ⟨𝓜, h𝓜⟩ := exists_polarForest (c := 4 * s) B hD hs0 (by decide : 0 < 1) hinjs
        (fun _ : Fin 1 => N) hsum (fun _ => hh1) (fun _ => by nlinarith)
        (normalizedTracePair B N) hω
      refine ⟨D, h, 𝓜, le_rfl, hdepth h ?_, ?_⟩
      · have hp : 2 ^ h ≤ N := (Nat.le_mul_of_pos_right _ hs0).trans hh1
        have hp' : (2 : ℝ) ^ h ≤ N := by exact_mod_cast hp
        linarith
      · rw [h𝓜, hid, ← hphase]
        exact hself _ (norm_normalizedMPVState hB0)
    · obtain ⟨𝓜, h𝓜⟩ := UnequalMERA.exists_single_leaf hN0 (by omega : N ≤ 4 * s)
        (normalizedMPVState A N) (norm_normalizedMPVState h0)
      exact ⟨1, 0, 𝓜, hD, hcap, by rw [h𝓜]; exact hself _ (norm_normalizedMPVState h0)⟩

/-- Every sufficiently long chain of a normal tensor has the bounded-dimension MERA
approximation, without an additional nonvanishing assumption. -/
theorem exists_unequalMERA_of_normal {d D : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ R : ℕ, 1 ≤ R ∧ ∃ C : ℝ, 2 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ ε : ℝ, 0 < ε → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
        ∃ (D' h : ℕ) (𝓜 : UnequalMERA d D' R h N), D' ≤ D ∧
          ((h + 2 : ℕ) : ℝ) ≤ C * (1 + Real.log (1 + max 0 (Real.log (N / ε)))) ∧
          1 - ‖⟪𝓜.state, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨R, hR, C, hC, hall⟩ := exists_unequalMERA_every_length A hA
  obtain ⟨N₀, hN₀⟩ := exists_mpvState_ne_zero_of_le A hA
  exact ⟨R, hR, C, hC, N₀, fun ε hε N _ hN => hall ε hε N (hN₀ N hN)⟩

end MPSPreparation
