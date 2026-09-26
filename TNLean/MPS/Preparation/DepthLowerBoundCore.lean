/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExpectationOverlap
import TNLean.MPS.Preparation.BlockVariance

/-!
# The averaging step of the depth lower bound

This file carries out, for one system size `N` and one depth `T`, the comparison of averages of
translated observables in the normalized periodic vector `φ_N` of a normal tensor and in a unit
vector `ψ` prepared in depth `T`, in the chapter's proof of `thm:ldp_depth_lower_bound` (the
chapter's version of arXiv:2307.01696, Theorem 1).

With `e = ⟨𝒪_1⟩_φ`, `e' = ⟨𝒪'_{s'}⟩_φ`, the centred observables `𝒪 - e` and `𝒪' - e'` are
placed on the windows starting at `kΔ` and `kΔ + s' - 1`, `k < n`, with `Δ = s' + L + 2T` and
`n = ⌊N/Δ⌋`. If `|⟨φ_N|ψ⟩| ≥ 1/2`, the expectation-overlap inequality
(`LinearMap.IsSymmetric.norm_inner_mul_norm_sub_le`, chapter entry `lem:ldp_expectation_overlap`)
applied to the averages `Z₁ = (1/n) ∑ ±(𝒪 - e)^{(k)}` and
`Z₂ = (1/n) ∑ (𝒪 - e)^{(k)} (𝒪' - e')^{(k)}` gives
`|G_N(𝒪, 𝒪'; s')| ≤ 6S/√n` (`norm_mpvConnectedCorrelator_le_of_overlap`), where `S/√n` bounds
the standard deviations of such averages in both states
(`exists_norm_sub_inner_smul_add_le_div_sqrt`).

## Main results

* `MPSPreparation.sum_norm_inner_div_le_of_overlap`: the sign-choice step for `Z₁`.
* `MPSTensor.mpvExpectation_centred_pair`: the pair expectations in `φ_N` equal the connected
  correlator.
* `MPSTensor.exists_norm_sub_inner_smul_add_le_div_sqrt`: standard deviations of averages.
* `MPSTensor.norm_mpvConnectedCorrelator_le_of_overlap`: the bound `|G_N| ≤ 6S/√n`.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator ComplexOrder

namespace MPSPreparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The sign-choice step.** Let `φ, ψ` be unit vectors with `|⟨φ|ψ⟩| ≥ 1/2`, and let
`T_k`, `k < n`, be symmetric operators with `⟨T_k⟩_φ = 0`. If the standard deviations of every
average `Z = ∑ c_k T_k` with real `|c_k| ≤ 1/n` in `φ` and `ψ` add up to at most `S`, then
`(1/n) ∑ |⟨T_k⟩_ψ| ≤ 2S`.

This is the step "the choice `ε_k = sign x_k` gives `(1/n) ∑ |x_k| ≤ C₂ n^{-1/2}`" of the
chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696,
Theorem 1). -/
theorem sum_norm_inner_div_le_of_overlap {φ ψ : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hov : 1 / 2 ≤ ‖⟪φ, ψ⟫_ℂ‖) {n : ℕ} (T : Fin n → E →ₗ[ℂ] E) (hT : ∀ k, (T k).IsSymmetric)
    (h0 : ∀ k, ⟪φ, T k φ⟫_ℂ = 0) {S : ℝ}
    (hS : ∀ c : Fin n → ℝ, (∀ k, |c k| ≤ 1 / n) →
      ‖(∑ k, (c k : ℂ) • T k) φ - ⟪φ, (∑ k, (c k : ℂ) • T k) φ⟫_ℂ • φ‖ +
        ‖(∑ k, (c k : ℂ) • T k) ψ - ⟪ψ, (∑ k, (c k : ℂ) • T k) ψ⟫_ℂ • ψ‖ ≤ S) :
    (∑ k, ‖⟪ψ, T k ψ⟫_ℂ‖) / n ≤ 2 * S := by
  classical
  set x : Fin n → ℂ := fun k ↦ ⟪ψ, T k ψ⟫_ℂ with hx_def
  let ε : Fin n → ℝ := fun k ↦ if 0 ≤ (x k).re then 1 else -1
  have hεx : ∀ k, (ε k : ℂ) * x k = (‖x k‖ : ℂ) := by
    intro k
    have hx : ((x k).re : ℂ) = x k := (hT k).coe_re_inner_self_apply ψ
    have hn : ‖x k‖ = |(x k).re| := by
      conv_lhs => rw [← hx]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hn]
    simp only [ε]
    split_ifs with h
    · rw [abs_of_nonneg h, ← hx]; simp
    · rw [abs_of_neg (not_le.mp h)]
      conv_lhs => rw [← hx]
      push_cast
      ring
  let c : Fin n → ℝ := fun k ↦ ε k / n
  have hc : ∀ k, |c k| ≤ 1 / n := by
    intro k
    simp only [c, ε, abs_div, Nat.abs_cast]
    split_ifs <;> simp
  have hZsym : (∑ k, (c k : ℂ) • T k).IsSymmetric :=
    LinearMap.isSymmetric_sum _ fun k _ ↦ (hT k).smul (Complex.conj_ofReal _)
  have hZφ : ⟪φ, (∑ k, (c k : ℂ) • T k) φ⟫_ℂ = 0 := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right, h0,
      mul_zero, Finset.sum_const_zero]
  have hZψ : ⟪ψ, (∑ k, (c k : ℂ) • T k) ψ⟫_ℂ = (((∑ k, ‖x k‖) / n : ℝ) : ℂ) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [c]
    push_cast
    rw [div_mul_eq_mul_div, hεx]
  have hov1 := hZsym.norm_inner_mul_norm_sub_le hφ hψ
  have hdiff : ‖⟪φ, (∑ k, (c k : ℂ) • T k) φ⟫_ℂ - ⟪ψ, (∑ k, (c k : ℂ) • T k) ψ⟫_ℂ‖ =
      (∑ k, ‖x k‖) / n := by
    rw [hZφ, hZψ, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hdiff] at hov1
  have h1 := mul_le_mul_of_nonneg_right hov
    (by positivity : (0 : ℝ) ≤ (∑ k, ‖x k‖) / n)
  have h2 := hS c hc
  change (∑ k, ‖x k‖) / n ≤ 2 * S
  linarith

/-- For a symmetric `Z` and unit vectors with `|⟨φ|ψ⟩| ≥ 1/2`,
`|⟨Z⟩_φ| ≤ 2 (σ_φ(Z) + σ_ψ(Z)) + |⟨Z⟩_ψ|` (chapter's proof of `thm:ldp_depth_lower_bound`,
from `lem:ldp_expectation_overlap`). -/
theorem norm_inner_le_of_overlap {φ ψ : E} (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hov : 1 / 2 ≤ ‖⟪φ, ψ⟫_ℂ‖) {Z : E →ₗ[ℂ] E} (hZ : Z.IsSymmetric) :
    ‖⟪φ, Z φ⟫_ℂ‖ ≤
      2 * (‖Z φ - ⟪φ, Z φ⟫_ℂ • φ‖ + ‖Z ψ - ⟪ψ, Z ψ⟫_ℂ • ψ‖) + ‖⟪ψ, Z ψ⟫_ℂ‖ := by
  have hov1 := hZ.norm_inner_mul_norm_sub_le hφ hψ
  have h1 := mul_le_mul_of_nonneg_right hov (norm_nonneg (⟪φ, Z φ⟫_ℂ - ⟪ψ, Z ψ⟫_ℂ))
  have h2 := norm_le_norm_sub_add ⟪φ, Z φ⟫_ℂ ⟪ψ, Z ψ⟫_ℂ
  linarith

end MPSPreparation

namespace MPSTensor

variable {d D : ℕ}

/-! ### Linearity and reality of normalized expectations -/

theorem mpvExpectation_sub (A : MPSTensor d D) (N : ℕ) (O O' : Matrix (Cfg d N) (Cfg d N) ℂ) :
    mpvExpectation A N (O - O') = mpvExpectation A N O - mpvExpectation A N O' := by
  simp only [mpvExpectation, map_sub, LinearMap.sub_apply, inner_sub_right]

theorem mpvExpectation_add (A : MPSTensor d D) (N : ℕ) (O O' : Matrix (Cfg d N) (Cfg d N) ℂ) :
    mpvExpectation A N (O + O') = mpvExpectation A N O + mpvExpectation A N O' := by
  simp only [mpvExpectation, map_add, LinearMap.add_apply, inner_add_right]

theorem mpvExpectation_smul (A : MPSTensor d D) (N : ℕ) (c : ℂ)
    (O : Matrix (Cfg d N) (Cfg d N) ℂ) :
    mpvExpectation A N (c • O) = c * mpvExpectation A N O := by
  simp only [mpvExpectation, map_smul, LinearMap.smul_apply, inner_smul_right]
  ring

/-- The normalized expectation of the identity is `1` when `φ_N(A) ≠ 0`. -/
theorem mpvExpectation_one (A : MPSTensor d D) {N : ℕ} (h : mpvState A N ≠ 0) :
    mpvExpectation A N 1 = 1 := by
  have hχ := norm_inv_smul_mpvState h
  simp only [mpvExpectation, Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  rw [inner_self_eq_norm_sq_to_K, hχ]
  norm_num

/-- The normalized expectation of a Hermitian operator is real. -/
theorem star_mpvExpectation_of_isHermitian (A : MPSTensor d D) {N : ℕ}
    {O : Matrix (Cfg d N) (Cfg d N) ℂ} (hO : O.IsHermitian) :
    star (mpvExpectation A N O) = mpvExpectation A N O := by
  have hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hO
  have h := hS.coe_re_inner_self_apply (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)
  change star ⟪_, _⟫_ℂ = ⟪_, _⟫_ℂ
  rw [← h]
  exact Complex.conj_ofReal _

/-- A Hermitian matrix minus a real multiple of the identity is Hermitian. -/
theorem _root_.Matrix.IsHermitian.sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {e : ℂ} (he : star e = e) :
    (X - e • (1 : Matrix n n ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hX.eq, he]

/-- Subtracting `e` times the identity changes the operator norm by at most `‖e‖`. -/
theorem _root_.Matrix.norm_toEuclideanCLM_sub_smul_one_le {n : Type*} [Fintype n]
    [DecidableEq n] (X : Matrix n n ℂ) (e : ℂ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (X - e • 1)‖ ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X‖ + ‖e‖ := by
  rw [map_sub, map_smul, map_one]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le

/-! ### Pair expectations -/

/-- **Centred pairs.** With `e = ⟨𝒪_1⟩_φ` and `e' = ⟨𝒪'_{s'}⟩_φ`, the expectation in `φ_N` of
`(𝒪 - e)` on the window starting at `b` times `(𝒪' - e')` on the window starting at
`b + s' - 1` is the connected correlator `G_N(𝒪, 𝒪'; s')`, whatever `b`.

This is "`⟨φ_N|𝒪^{(k)} 𝒪'^{(k)}|φ_N⟩ = G_N(𝒪, 𝒪'; s')`" in the chapter's proof of
`thm:ldp_depth_lower_bound` (arXiv:2307.01696, eq. (TI-MPS2), translation invariance). -/
theorem mpvExpectation_centred_pair (A : MPSTensor d D) {L N b s : ℕ} (hL : 0 < L)
    (hLs : L + 1 ≤ s) (hb : b + (s - 1) + L ≤ N) (hne : mpvState A N ≠ 0)
    (O O' : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) {e e' : ℂ}
    (he : e = mpvExpectation A N (chainWindowOperator N 0 O))
    (he' : e' = mpvExpectation A N (chainWindowOperator N (s - 1) O')) :
    mpvExpectation A N ((chainWindowOperator N b O - e • 1) *
        (chainWindowOperator N (b + (s - 1)) O' - e' • 1)) =
      mpvConnectedCorrelator A N 0 (s - 1) O O' := by
  have hmul := mpvExpectation_chainWindowOperator_mul_eq A hL (N := N) (a := b)
    (m := s - 1 - L) (by omega) O O'
  rw [show L + (s - 1 - L) = s - 1 by omega] at hmul
  have hP : mpvExpectation A N (chainWindowOperator N b O) = e := by
    rw [he, mpvExpectation_chainWindowOperator_eq A hL (by omega) O]
  have hQ : mpvExpectation A N (chainWindowOperator N (b + (s - 1)) O') = e' := by
    rw [he', mpvExpectation_chainWindowOperator_eq A hL (by omega) O',
      mpvExpectation_chainWindowOperator_eq A hL (a := s - 1) (by omega) O']
  simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, one_mul, mul_one,
    mpvExpectation_sub, mpvExpectation_smul, mpvExpectation_one A hne, hmul, hP, hQ]
  rw [mpvConnectedCorrelator, ← he, ← he']
  ring

/-! ### Standard deviations of averages -/

/-- **Standard deviations of averages in both states.** For a normal tensor in the gauge
`eq:ldp_normal_gauge` there is `S ≥ 0` such that: for a Hermitian operator `X` of norm at most
`4` on `w` sites, placed on the windows starting at `kΔ`, `k < n`, with `w < Δ`,
`w + 2T ≤ Δ`, `nΔ ≤ N` and `n ≥ 1`, and for real weights `|c_k| ≤ 1/n`, the average
`Z = ∑ c_k X^{(k)}` satisfies `σ_φ(Z) + σ_ψ(Z) ≤ S/√n` in the normalized vector `φ = φ_N` and in
any unit vector `ψ` prepared in depth `T`.

This combines the two variance bounds of the chapter's proof of `thm:ldp_depth_lower_bound`
("every average of `n` of these operators … has variance at most `C₁/n` in `φ_N`" and "by
factorization its variance there is at most `4/n`"; the chapter's version of
arXiv:2307.01696, Theorem 1). -/
theorem exists_norm_sub_inner_smul_add_le_div_sqrt [NeZero D] {A : MPSTensor d D} {L₀ : ℕ}
    (hL1 : 1 ≤ L₀) (hL : Kraus.IsNBlkInjective A L₀) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hlt1 : ‖lam₂‖ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (T w Δ n N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      MPSPreparation.IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 → 0 < w → w < Δ →
      w + 2 * T ≤ Δ → n * Δ ≤ N → 0 < n → mpvState A N ≠ 0 →
      ∀ X : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ, X.IsHermitian →
        ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) X‖ ≤ 4 →
        ∀ c : Fin n → ℝ, (∀ k, |c k| ≤ 1 / n) →
          ‖(∑ k : Fin n, (c k : ℂ) • Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N) -
              ⟪((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N,
                (∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                  (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)⟫_ℂ •
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)‖ +
            ‖(∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                (WithLp.toLp 2 ψ) -
              ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N)),
                (∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                  (WithLp.toLp 2 ψ)⟫_ℂ • (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))‖ ≤
            S / Real.sqrt n := by
  set r : ℝ := (‖lam₂‖ + 1) / 2 with hr_def
  obtain ⟨C', hC'0, hvarφ⟩ := exists_norm_sub_inner_smul_sq_le_mpv hL1 hL hA hρ hρfix hρtr hmax
    (r := r) (by rw [hr_def]; linarith) (by rw [hr_def]; linarith) (M := 4) (by norm_num)
  refine ⟨Real.sqrt (3 * C') + Real.sqrt (3 * (2 * 4 ^ 2)), by positivity, ?_⟩
  intro T w Δ n N _ ψ hψ hψ1 hw hwΔ hwT hnΔ hn hne X hX hXn c hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ : ∀ {v a : ℝ}, 0 ≤ v → 0 ≤ a → v ^ 2 ≤ (1 / n) ^ 2 * (3 * n * a) →
      v ≤ Real.sqrt (3 * a) / Real.sqrt n := by
    intro v a hv ha h
    have e1 : (1 / (n : ℝ)) ^ 2 * (3 * n * a) = (Real.sqrt (3 * a) / Real.sqrt n) ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hn0.le]
      field_simp
    rw [e1] at h
    exact (pow_le_pow_iff_left₀ hv (by positivity) two_ne_zero).mp h
  have h1 := hσ (norm_nonneg _) hC'0 (hvarφ w Δ n N hw hwΔ hnΔ hne X hX hXn c (1 / n) hc)
  have h2 := hσ (norm_nonneg _) (by norm_num)
    (MPSPreparation.norm_sub_inner_smul_sq_le_of_isPreparedInDepth hw hwT hnΔ hψ hψ1 hX hXn c hc)
  rw [add_div]
  exact add_le_add h1 h2

/-! ### The correlator bound -/

/-- **The averaging bound.** Let `S` bound the standard deviations of averages as in
`exists_norm_sub_inner_smul_add_le_div_sqrt`, let `𝒪, 𝒪'` be Hermitian of norm one on `L`
sites, let `2T + L + 1 ≤ s'`, `Δ = s' + L + 2T` and `n = ⌊N/Δ⌋ ≥ 1`. If a unit vector `ψ`
prepared in depth `T` satisfies `|⟨φ_N|ψ⟩| ≥ 1/2`, then `|G_N(𝒪, 𝒪'; s')| ≤ 6S/√n`.

This is the right-hand inequality of eq. `eq:ldp_depth_contradiction` in the chapter's proof of
`thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696, Theorem 1). -/
theorem norm_mpvConnectedCorrelator_le_of_overlap {A : MPSTensor d D} {S : ℝ}
    (hS : ∀ (T w Δ n N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      MPSPreparation.IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 → 0 < w → w < Δ →
      w + 2 * T ≤ Δ → n * Δ ≤ N → 0 < n → mpvState A N ≠ 0 →
      ∀ X : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ, X.IsHermitian →
        ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) X‖ ≤ 4 →
        ∀ c : Fin n → ℝ, (∀ k, |c k| ≤ 1 / n) →
          ‖(∑ k : Fin n, (c k : ℂ) • Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N) -
              ⟪((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N,
                (∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                  (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)⟫_ℂ •
                (((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N)‖ +
            ‖(∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                (WithLp.toLp 2 ψ) -
              ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N)),
                (∑ k : Fin n, (c k : ℂ) •
                  Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
                  (WithLp.toLp 2 ψ)⟫_ℂ • (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))‖ ≤
            S / Real.sqrt n)
    {T N L s' : ℕ} [NeZero N] {ψ : Cfg d N → ℂ} (hψ : MPSPreparation.IsPreparedInDepth T ψ)
    (hψ1 : star ψ ⬝ᵥ ψ = 1) (hne : mpvState A N ≠ 0)
    {O O' : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ} (hOh : O.IsHermitian)
    (hO'h : O'.IsHermitian) (hOn : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O‖ = 1)
    (hO'n : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O'‖ = 1) (hL0 : 0 < L)
    (hs' : 2 * T + L + 1 ≤ s') (hN : s' + L + 2 * T ≤ N)
    (hov : 1 / 2 ≤ ‖⟪((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N,
      (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖) :
    ‖mpvConnectedCorrelator A N 0 (s' - 1) O O'‖ ≤
      6 * (S / Real.sqrt (N / (s' + L + 2 * T) : ℕ)) := by
  classical
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = s' + L + 2 * T := ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n, n = N / Δ := ⟨_, rfl⟩
  rw [← hΔ, ← hn_def]
  have hΔpos : 0 < Δ := by omega
  have hnΔ : n * Δ ≤ N := hn_def ▸ Nat.div_mul_le_self N Δ
  have hn1 : 0 < n := hn_def ▸ Nat.div_pos (by omega) hΔpos
  set φ : EuclideanSpace ℂ (Cfg d N) := ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N with hφ_def
  set χ : EuclideanSpace ℂ (Cfg d N) := WithLp.toLp 2 ψ with hχ_def
  have hφ : ‖φ‖ = 1 := norm_inv_smul_mpvState hne
  have hχ : ‖χ‖ = 1 := MPSPreparation.norm_toLp_eq_one hψ1
  /- The centred observables. -/
  obtain ⟨e, he⟩ : ∃ e, e = mpvExpectation A N (chainWindowOperator N 0 O) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e', e' = mpvExpectation A N (chainWindowOperator N (s' - 1) O') :=
    ⟨_, rfl⟩
  have hes : star e = e := he ▸ star_mpvExpectation_of_isHermitian A
    (chainWindowOperator_isHermitian (by omega) (by omega) hOh)
  have hes' : star e' = e' := he' ▸ star_mpvExpectation_of_isHermitian A
    (chainWindowOperator_isHermitian (by omega) (by omega) hO'h)
  have heN : ‖e‖ ≤ 1 := he ▸ (norm_mpvExpectation_le A N _).trans
    ((norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) O).trans hOn.le)
  have he'N : ‖e'‖ ≤ 1 := he' ▸ (norm_mpvExpectation_le A N _).trans
    ((norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) O').trans hO'n.le)
  obtain ⟨X, hX_def⟩ : ∃ X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, X = O - e • 1 :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY_def⟩ : ∃ Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, Y = O' - e' • 1 :=
    ⟨_, rfl⟩
  have hX : X.IsHermitian := hX_def ▸ hOh.sub_smul_one hes
  have hY : Y.IsHermitian := hY_def ▸ hO'h.sub_smul_one hes'
  have hXn : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) X‖ ≤ 2 := by
    rw [hX_def]
    exact (Matrix.norm_toEuclideanCLM_sub_smul_one_le O e).trans (by rw [hOn]; linarith)
  have hYn : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Y‖ ≤ 2 := by
    rw [hY_def]
    exact (Matrix.norm_toEuclideanCLM_sub_smul_one_le O' e').trans (by rw [hO'n]; linarith)
  /- The pair operator on `w = s' - 1 + L` sites. -/
  obtain ⟨w, hw_def⟩ : ∃ w, w = s' - 1 + L := ⟨_, rfl⟩
  obtain ⟨W, hW_def⟩ : ∃ W : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ,
      W = chainWindowOperator w 0 X * chainWindowOperator w (s' - 1) Y := ⟨_, rfl⟩
  have hcomm : Commute (chainWindowOperator w 0 X) (chainWindowOperator w (s' - 1) Y) := by
    refine MPSPreparation.commute_of_mem_supportedOperators ?_
      (MPSPreparation.chainWindowOperator_mem_supportedOperators_window (by omega) (by omega) X)
      (MPSPreparation.chainWindowOperator_mem_supportedOperators_window (by omega) (by omega) Y)
    rw [Set.disjoint_left]
    rintro k ⟨-, hk⟩ ⟨hk', -⟩
    omega
  have hW : W.IsHermitian := by
    rw [Matrix.IsHermitian, hW_def, Matrix.conjTranspose_mul,
      (chainWindowOperator_isHermitian (by omega) (by omega) hY).eq,
      (chainWindowOperator_isHermitian (by omega) (by omega) hX).eq]
    exact hcomm.eq.symm
  have hWn : ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) W‖ ≤ 4 := by
    rw [hW_def]
    refine (Matrix.norm_toEuclideanCLM_mul_le _ _).trans ?_
    have h1 := (norm_toEuclideanCLM_chainWindowOperator_le (N := w) (a := 0) (by omega)
      (by omega) X).trans hXn
    have h2 := (norm_toEuclideanCLM_chainWindowOperator_le (N := w) (a := s' - 1) (by omega)
      (by omega) Y).trans hYn
    calc _ ≤ 2 * 2 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  /- The block operators. -/
  have hwinL := fun k : Fin n ↦ MPSPreparation.window_lt_and_le (N := N) (w := L) hL0
    (by omega) hnΔ k.isLt
  have hwinW := fun k : Fin n ↦ MPSPreparation.window_lt_and_le (N := N) (w := w) (by omega)
    (by omega) hnΔ k.isLt
  have hQwin : ∀ k : Fin n, k.val * Δ + (s' - 1) < N ∧ k.val * Δ + (s' - 1) + L ≤ N := by
    intro k
    have := hwinW k
    omega
  have hPQ : ∀ k : Fin n, chainWindowOperator N (k.val * Δ) W =
      chainWindowOperator N (k.val * Δ) X * chainWindowOperator N (k.val * Δ + (s' - 1)) Y := by
    intro k
    rw [hW_def, chainWindowOperator_mul (hwinW k).1 (hwinW k).2,
      chainWindowOperator_chainWindowOperator (hwinW k).1 (hwinW k).2 (by omega) (by omega),
      chainWindowOperator_chainWindowOperator (hwinW k).1 (hwinW k).2 (by omega) (by omega),
      add_zero]
  /- The first average: `(1/n) ∑ |x_k| ≤ 2S/√n`. -/
  have hTsym : ∀ k : Fin n,
      (Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X)).IsSymmetric := fun k ↦
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwinL k).1 (hwinL k).2 hX)
  have hx0 : ∀ k : Fin n,
      ⟪φ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) φ⟫_ℂ = 0 := by
    intro k
    change mpvExpectation A N (chainWindowOperator N (k.val * Δ) X) = 0
    rw [hX_def, chainWindowOperator_sub_smul_one (hwinL k).1 (hwinL k).2, mpvExpectation_sub,
      mpvExpectation_smul, mpvExpectation_one A hne, he,
      mpvExpectation_chainWindowOperator_eq A hL0 (hwinL k).2 O, mul_one, sub_self]
  have hsum := MPSPreparation.sum_norm_inner_div_le_of_overlap hφ hχ hov _ hTsym hx0
    (S := S / Real.sqrt n) fun c hc ↦ hS T L Δ n N ψ hψ hψ1 hL0 (by omega) (by omega) hnΔ hn1 hne
      X hX (hXn.trans (by norm_num)) c hc
  /- The second average. -/
  have hZ₂sym : (∑ k : Fin n, (((1 : ℝ) / n : ℝ) : ℂ) •
      Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W)).IsSymmetric :=
    LinearMap.isSymmetric_sum _ fun k _ ↦
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (chainWindowOperator_isHermitian (hwinW k).1 (hwinW k).2 hW)).smul (Complex.conj_ofReal _)
  have hZ₂φ : ⟪φ, (∑ k : Fin n, (((1 : ℝ) / n : ℝ) : ℂ) •
      Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W)) φ⟫_ℂ =
      mpvConnectedCorrelator A N 0 (s' - 1) O O' := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
    have h0 : ∀ k : Fin n,
        ⟪φ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) φ⟫_ℂ =
          mpvConnectedCorrelator A N 0 (s' - 1) O O' := by
      intro k
      change mpvExpectation A N (chainWindowOperator N (k.val * Δ) W) = _
      rw [hPQ k, hX_def, hY_def, chainWindowOperator_sub_smul_one (hwinL k).1 (hwinL k).2,
        chainWindowOperator_sub_smul_one (hQwin k).1 (hQwin k).2]
      exact mpvExpectation_centred_pair A hL0 (by omega) (hQwin k).2 hne O O' he he'
    simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hZ₂χ : ‖⟪χ, (∑ k : Fin n, (((1 : ℝ) / n : ℝ) : ℂ) •
      Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W)) χ⟫_ℂ‖ ≤
      2 * ((∑ k : Fin n, ‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ‖) /
        n) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
    have hfac : ∀ k : Fin n,
        ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) χ⟫_ℂ =
          ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ *
            ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ + (s' - 1)) Y) χ⟫_ℂ := by
      intro k
      have hsep : MPSPreparation.IsSeparatedBy (MPSPreparation.window N (k.val * Δ) L)
          (MPSPreparation.window N (k.val * Δ + (s' - 1)) L) (2 * T) :=
        MPSPreparation.isSeparatedBy_window (by omega) (by have := hwinW k; omega)
      have h := MPSPreparation.expect_mul_eq_of_isPreparedInDepth hψ hψ1 hsep
        (MPSPreparation.chainWindowOperator_mem_supportedOperators_window (hwinL k).1
          (hwinL k).2 X)
        (MPSPreparation.chainWindowOperator_mem_supportedOperators_window (hQwin k).1
          (hQwin k).2 Y)
      rw [hPQ k, hχ_def, MPSPreparation.inner_toLp_toEuclideanLin,
        MPSPreparation.inner_toLp_toEuclideanLin, MPSPreparation.inner_toLp_toEuclideanLin, h]
    have hy : ∀ k : Fin n,
        ‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ + (s' - 1)) Y) χ⟫_ℂ‖ ≤
          2 :=
      fun k ↦ (MPSPreparation.norm_inner_apply_le (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        (chainWindowOperator N (k.val * Δ + (s' - 1)) Y)) hχ).trans
        ((norm_toEuclideanCLM_chainWindowOperator_le (hQwin k).1 (hQwin k).2 Y).trans hYn)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin n, ‖(((1 : ℝ) / n : ℝ) : ℂ) *
          ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) χ⟫_ℂ‖
        ≤ ∑ k : Fin n,
          ‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ‖ * 2 / n := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [norm_mul, hfac k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
          calc 1 / (n : ℝ) *
                (‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ‖ *
                  ‖⟪χ, Matrix.toEuclideanLin
                    (chainWindowOperator N (k.val * Δ + (s' - 1)) Y) χ⟫_ℂ‖)
              ≤ 1 / (n : ℝ) *
                (‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ‖ * 2) := by
                gcongr
                exact hy k
            _ = _ := by ring
      _ = _ := by rw [← Finset.sum_div, ← Finset.sum_mul]; ring
  have hvar2 := hS T w Δ n N ψ hψ hψ1 (by omega) (by omega) (by omega) hnΔ hn1 hne W hW hWn
    (fun _ ↦ (1 : ℝ) / n) fun _ ↦ le_of_eq (abs_of_nonneg (by positivity))
  beta_reduce at hvar2
  rw [← hφ_def, ← hχ_def] at hvar2
  have hov2 := MPSPreparation.norm_inner_le_of_overlap hφ hχ hov hZ₂sym
  rw [← hZ₂φ]
  linarith

end MPSTensor
