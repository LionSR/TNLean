/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.PrintedAreaLawSource
import TNLean.MPS.AreaLaw.Hastings.RenyiBootstrapLemma
import TNLean.MPS.AreaLaw.Hastings.RelentGapped
import TNLean.MPS.AreaLaw.Hastings.MPSGroundState

/-!
# Consequences of Hastings' area law at a common source length

Put `s = max (80 * (chainLRVelocity R J - 1) / Δ) 80` and `ξ' = 6s`.
The physical Lieb–Robinson velocity is proportional to the interaction strength `J`,
and its decay length is numerical. Lemma 1, the bootstrap bounds, the entropy gain,
and the matrix product state approximation below all use this same pair.
In particular, the matrix product state threshold uses the printed entropy bound
`c₀ ξ' log ξ' log q 2^(ξ' log q)`.

Source: Hastings, arXiv:0705.2024v4, lines 96–144, 234–267, 280–410,
413–503 and 505–557.

**Local fix (Lieb–Robinson convention):** the time-cone bound is read as
`exp(-d/ξ_C)` for `|t| ≤ d/v`, as recorded in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`.

**Local fix (explicit constants):** the entropy gain uses `2 C₁` and
`relentConst`, and the squared matrix product state error has `exp(2/ξ')`.
See `docs/paper-gaps/hastings07_relent_constants.tex`,
`docs/paper-gaps/hastings07_mps_error_measure.tex`, and
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

namespace TNLean.MPS.AreaLaw

open Hastings Matrix TNLean.Lattice Real
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

/-- Lemma 2 at the length of the order-`J` source pair.
Hastings, arXiv:0705.2024v4, lines 280–311. -/
theorem exists_entropy_le_of_overlap_schmidtRank_mixture_source (R : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 j) Ω ≤
          Real.log k + 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) *
            Real.log
              (2 * (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3) ^ 2 / P) *
              Real.log q +
            bootstrapRemainder (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80)) q := by
  obtain ⟨K, -, hF⟩ := exists_projectorFactorization_source R
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs j k r hk w ψ hw hrank hnorm P hP hPdef
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have hs : 80 ≤ (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := le_max_right _ _
  have hξ : 0 < 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := by linarith
  have hC₁ : 1 ≤ max K 1 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (by linarith))
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q ≤ 1` the entropy vanishes and the right side is nonnegative.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    refine (regionEntropy_le_card_mul_log hΩ _).trans ?_
    have hk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hξ0 : 0 ≤ Real.log
        (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) / 2 + 1) :=
      Real.log_nonneg (by linarith)
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero, bootstrapRemainder, one_pow,
      sub_self, Real.log_zero, zero_add]
    linarith
  · refine entropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt hq hΩ j hξ hC₁
      (fun m ↦ ?_) hk w ψ hw hrank hnorm hP hPdef
    obtain ⟨OB, OL, OR, hFm⟩ := hF hJ hΔ h hgs j m
    exact ⟨OB, OL, OR, hFm.mono (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos (by linarith) 3).le)
      (Real.exp_pos _).le)⟩

/-- The Rényi bootstrap bound for `0 < α < 1` at the same source pair.
Hastings, arXiv:0705.2024v4, lines 392–410. -/
theorem exists_renyiEntropy_le_of_overlap_schmidtRank_mixture_source (R : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ {α : ℝ}, 0 < α → α < 1 →
      ((q : ℝ) ^ 2) ^ (1 - α) *
        Real.exp (-(2 * α / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80)))) < 1 →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        renyiEntropy (cutMatrix Ω j * (cutMatrix Ω j)ᴴ)
            (posSemidef_self_mul_conjTranspose (cutMatrix Ω j)).isHermitian α ≤
          Real.log k + 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) *
            Real.log
              (2 * (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3) ^ 2 / P) *
              Real.log q +
            4 * Real.log q -
            Real.log (1 - ((q : ℝ) ^ 2) ^ (1 - α) *
              Real.exp
                (-(2 * α / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80))))) /
              (1 - α) := by
  obtain ⟨K, -, hF⟩ := exists_projectorFactorization_source R
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs α hα0 hα1 hconv j k r hk w ψ hw hrank hnorm P hP hPdef
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have hs : 80 ≤ (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := le_max_right _ _
  have hξ : 0 < 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := by linarith
  have hC₁ : 1 ≤ max K 1 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (by linarith))
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q = 1` the Rényi entropy is at most zero and the right side is nonnegative.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    refine (renyiEntropy_cutMatrix_nonpos_of_one hΩ j hα0 hα1).trans ?_
    have hk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    simp only [Nat.cast_one, one_pow, Real.one_rpow, one_mul, Real.log_one, mul_zero,
      add_zero] at hconv ⊢
    have hx0 := Real.exp_pos
      (-(2 * α / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80))))
    have hlog : Real.log (1 - Real.exp
        (-(2 * α / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80))))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have h2 : Real.log (1 - Real.exp
        (-(2 * α / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80))))) /
        (1 - α) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (by linarith)
    linarith
  · exact renyiEntropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt hq hΩ j hξ hC₁
      hα0 hα1 hconv (fun m ↦ by
        obtain ⟨OB, OL, OR, hFm⟩ := hF hJ hΔ h hgs j m
        exact ⟨OB, OL, OR, hFm.mono (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos (by linarith) 3).le)
          (Real.exp_pos _).le)⟩) hk w ψ hw hrank hnorm hP hPdef

/-- The Rényi bootstrap bound for `α > 1` at the same source pair.
Hastings, arXiv:0705.2024v4, lines 392–410. -/
theorem exists_renyiEntropy_le_of_overlap_schmidtRank_mixture_of_one_lt_source (R : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ {α : ℝ}, 1 < α →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        renyiEntropy (cutMatrix Ω j * (cutMatrix Ω j)ᴴ)
            (posSemidef_self_mul_conjTranspose (cutMatrix Ω j)).isHermitian α ≤
          Real.log k + 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) *
            Real.log
              (2 * (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3) ^ 2 / P) *
              Real.log q +
            bootstrapRemainder (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80)) q := by
  obtain ⟨K, hK, hL2⟩ := exists_entropy_le_of_overlap_schmidtRank_mixture_source R
  refine ⟨K, hK, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs α hα j k r hk w ψ hw hrank hnorm P hP hPdef
  exact (renyiEntropy_cutMatrix_le_regionEntropy_of_one_lt hgs.1 j hα).trans
    (hL2 hJ hΔ h hgs j hk w ψ hw hrank hnorm hP hPdef)

namespace Hastings

/-- The entropy gain at the same source pair, with the explicit constants of
`docs/paper-gaps/hastings07_relent_constants.tex`.
Hastings, arXiv:0705.2024v4, eq. `relent`, lines 234–242 and 413–503. -/
theorem exists_relent_of_isGappedGroundState_source (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ c l : ℕ, c + l ≤ L →
      (l + 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) *
          Real.log (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3)) * Real.log q +
          bootstrapRemainder (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80)) q ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 c) Ω →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) (c + l)) Ω ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) c) Ω +
          Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L c (c + l)) Ω -
          (1 - 2 * ((2 * (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3)) *
            Real.exp (-(l / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80)))))) *
            (l / (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80))) +
          Real.log
            (2 * (K * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3)) +
            relentConst := by
  obtain ⟨K₀, hK₀, hF⟩ := exists_projectorFactorization_source R
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs c l hcl hS
  have hζ8 : 80 ≤ (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := le_max_right _ _
  have hξ : 0 < 6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) := by linarith
  have hpow : 1 ≤ (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3 :=
    one_le_pow₀ (by linarith)
  have hC₁ : 1 ≤ (K₀ + 1) * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) ^ 3 := by
    nlinarith
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q = 1` the window condition fails: the entropy vanishes and `F(ξ', 1) > 0`.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    have hS0 := TNLean.Lattice.regionEntropy_le_card_mul_log hgs.1 (interval L 0 c)
    have hξ0 : 0 ≤ Real.log
        (6 * (max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80) / 2 + 1) :=
      Real.log_nonneg (by linarith)
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_add, bootstrapRemainder, one_pow,
      sub_self, Real.log_zero, add_zero] at hS hS0
    exfalso
    linarith
  refine relent_of_projectorFactorization_of_le_entropy hq hgs.1 hcl hξ hC₁ (fun m _ ↦ ?_) hS
  obtain ⟨OB, OL, OR, hF'⟩ := hF hJ hΔ h hgs c m
  refine ⟨OB, OL, OR, hF'.mono (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)⟩
  nlinarith


/-- Matrix product state approximation with the printed entropy threshold and the
same order-`J` Lieb–Robinson pair as Lemma 1. Hastings, arXiv:0705.2024v4,
lines 130–144 and 505–557. The squared error and the factor `exp(2/ξ')`
have the local corrections described in the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState_source (R : ℕ) :
    ∃ c₀ K : ℝ, 0 < c₀ ∧ 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80
      let ξ' := 6 * s
      let C₁ := max (K * s ^ 3) 1
      let Smax := c₀ * ξ' * log ξ' * log q * (2 : ℝ) ^ (ξ' * log q)
      ∀ {k' : ℕ}, ⌈exp (2 * Smax) / 2⌉₊ ≤ k' →
        let k₀ := ⌈exp (2 * Smax) / 2⌉₊
        let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
          (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
            Ω).leadingEigenprojection k'
        let Φ := sequentialTruncation P (L - 1) Ω
        IsOpenMPS L q k' (fun x ↦ Φ x) ∧
          ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
            (4 * C₁ ^ 2 * exp (2 / ξ') *
              ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  obtain ⟨c₀, hc₀, hS⟩ := exists_regionEntropy_prefix_le_source R
  obtain ⟨K, hK, hF⟩ := exists_projectorFactorization_source R
  refine ⟨c₀, K, hc₀, hK, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs s ξ' C₁ Smax k' hk'
  have hs : 80 ≤ s := le_max_right _ _
  have hξ : 0 < ξ' := by dsimp [ξ']; linarith
  refine isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy hgs.1 hξ
    (fun j _ m _ ↦ ?_) (fun j _ ↦ ?_) hk'
  · obtain ⟨OB, OL, OR, hfac⟩ := hF hJ hΔ h hgs j m
    exact ⟨OB, OL, OR, hfac.mono
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)⟩
  · have hj := hS hJ hΔ h hgs j
    rw [← leftBlock_eq_interval] at hj
    calc exp (2 * Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) / 2
        ≤ exp (2 * Smax) / 2 := by gcongr
      _ ≤ ⌈exp (2 * Smax) / 2⌉₊ := Nat.le_ceil _

end Hastings

end TNLean.MPS.AreaLaw
