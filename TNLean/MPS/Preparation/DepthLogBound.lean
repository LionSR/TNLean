/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence
import TNLean.MPS.Preparation.DepthUpperBound

/-!
# Preparation of a normal translation-invariant MPS in depth `O(log(N/ε))`

This file combines the depth count for the approximating state
(`MPSPreparation.exists_isPreparedInDepth_approximatingMPVState`) with the approximation error of
arXiv:2307.01696, Lemma 1'(i) (`MPSTensor.exists_approximationError_le_mul`), for the block
length `q ∝ log(N/ε)` chosen after Lemma 1 of the source ("it follows that
$q = O (\log (N / \epsilon))$"). This is the content of eq. (1) of the source,
`T = O(log(N/ε))`, for chains whose length is a multiple of the block length.

* `MPSPreparation.exists_isPreparedInDepth_approximationError_le`: there is `C`, depending only
  on `d` and `D`, such that for every normal tensor `A` there are `a > 0` and `b ≥ 1`, depending
  only on `A`, such that on `N` sites, for every block length `q` dividing `N` with
  `q ≥ a log(N/ε) + b`, a unit vector with error at most `ε` against `|φ_N⟩` is prepared in
  depth `C q`.
* `MPSPreparation.exists_isPreparedInDepth_le_log`: with `q` moreover at most
  `2 (a log(N/ε) + b)`, for example `q = ⌈a log(N/ε) + b⌉` when it divides `N`, the depth is at
  most `c log(N/ε)` with `c` depending only on `A`.

**Scope restriction (block length dividing the chain length):** the approximating state of the
source, eq. (10), `⊗_{i=1}^{N/q} U_i`, has `N/q` blocks of `q` sites, and both theorems here ask
that the block length divide `N`. The source's eq. (1) is stated for every `N`. Documented in
`docs/paper-gaps/mswc24_depth_upper_bound_divisible_length.tex`.

The tensor is not assumed to be in the gauge of eq. (5) of the source: a normal tensor is brought
into it by a gauge transformation and a rescaling
(`MPSTensor.exists_isPrimitiveMPS_gauge_of_isNormal`), which change the normalized state
`|φ_N⟩` only by a phase.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

variable {d N : ℕ}

/-- Rescaling the periodic vector by `ζ^N ≠ 0` changes the normalized state `|φ_N⟩` by a phase,
so the error `1 - |⟨ψ|φ_N⟩|` is unchanged. -/
theorem norm_inner_normalizedMPVState_of_mpv_eq {D D' : ℕ} {A : MPSTensor d D}
    {B : MPSTensor d D'} {ζ : ℂ} (hζ : ζ ≠ 0)
    (h : ∀ σ : Cfg d N, mpv B σ = ζ ^ N * mpv A σ) (ψ : MPVSpace d N) :
    ‖⟪ψ, normalizedMPVState B N⟫_ℂ‖ = ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ := by
  have hv : mpvState B N = ζ ^ N • mpvState A N := by
    ext σ
    rw [PiLp.smul_apply, mpvState_apply, mpvState_apply, smul_eq_mul, h]
  have hz : ‖ζ ^ N‖ ≠ 0 := norm_ne_zero_iff.2 (pow_ne_zero _ hζ)
  simp only [normalizedMPVState, hv, norm_smul, inner_smul_right, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_norm]
  rcases eq_or_ne ‖mpvState A N‖ 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- **Error `ε` in depth `O(q)` with `q ∝ log(N/ε)`.** There is `C`, depending only on `d` and
`D`, such that for every normal tensor `A` there are `a > 0` and `b ≥ 1`, depending only on `A`,
with the following property. For `0 < ε ≤ 1` and every block length `q` dividing `N ≥ 1` with
`q ≥ a log(N/ε) + b`, some unit vector `|ψ⟩` on `N` sites with
`ε(ψ, φ_N) = 1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a product state in depth at most `C q`.

arXiv:2307.01696, after Lemma 1: "Using \cref{lm:1}, it follows that
$q = O (\log (N / \epsilon))$", combined with the depth `T = O(q)` of the paragraph
"The sequential-RG circuit". The vector `|ψ⟩` is the approximating state `|φ'_N⟩` of eq. (10)
for a gauge-equivalent rescaling of `A` in the gauge of eq. (5). The bond dimension is positive,
as it is for the source's normal tensors, whose transfer matrix has the leading eigenvalue `1`.
The block length divides `N`, the scope restriction recorded in the module docstring. -/
theorem exists_isPreparedInDepth_approximationError_le (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, ∀ A : MPSTensor d D, Kraus.IsNormal A →
      ∃ a b : ℝ, 0 < a ∧ 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (N q : ℕ) [NeZero N], q ∣ N → a * Real.log (N / ε) + b ≤ q →
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧ IsPreparedInDepth (C * q) (fun s => ψ s) ∧
            1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_approximatingMPVState d D
  refine ⟨C, fun A hA => ?_⟩
  -- The gauge of eq. (5).
  obtain ⟨B, ζ, ρ, hζ, hGauge, hmpv, hP, hρ, -⟩ := exists_isPrimitiveMPS_gauge_of_isNormal hA
  have hNB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  have hLC : IsLeftCanonical B := hP.norm
  set σ := (Matrix.trace ρ)⁻¹ • ρ with hσdef
  have hPσ := hP.smul_inv_trace hρ
  have hσ : σ.PosDef := hρ.inv_trace_smul
  have htr : σ.trace = 1 := Matrix.trace_inv_trace_smul (ne_of_gt hρ.trace_pos)
  have hfix : Kraus.transferMap B σ = σ := hPσ.fixedPoint_is_fixed
  -- A bound `t < 1` on the subleading eigenvalues.
  have hNT := isNormalTensor_of_isNormal_leftCanonical B hNB hLC
  have hCh := Kraus.isChannel_mapLM B hLC
  obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
    (Module.End.finite_hasEigenvalue (Kraus.transferMap B)) fun μ hμ hne =>
      lt_of_le_of_ne (hCh.eigenvalue_norm_le_one μ hμ)
        fun h => hne (hNT.primitive_transfer.unique_peripheral μ hμ h)
  set t := max (1 - δ) (1 / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by norm_num)
  have ht1 : t < 1 := max_lt (by linarith) (by norm_num)
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 →
      ‖μ‖ ≤ ‖(t : ℂ)‖ := fun μ hμ hne => by
    rw [hnorm]; exact (hgap μ hμ hne).trans (le_max_left _ _)
  -- Lemma 1'(i) with `γ = 1/4`.
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul B hNB hLC hσ htr hfix hlam
    (γ := 1 / 4) (by norm_num) (by norm_num)
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  obtain ⟨L, hLpos, hL⟩ := hNB
  refine ⟨1 / r, max (Real.log K) 0 / r + L + 3 * D + 1, by positivity,
    le_add_of_nonneg_left (by positivity),
    fun ε hε hε1 N q _ hqN hq => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog0 : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hbq : max (Real.log K) 0 / r + L + 3 * D + 1 ≤ q := by
    have : 0 ≤ 1 / r * Real.log (N / ε) := by positivity
    linarith
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hLq : L ≤ q := by exact_mod_cast (show (L : ℝ) ≤ q by linarith)
  have h3D : 3 * D ≤ q := by exact_mod_cast (show ((3 * D : ℕ) : ℝ) ≤ q by push_cast; linarith)
  have hq1 : (1 : ℝ) ≤ q := by linarith
  obtain ⟨M, hM⟩ := hqN
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hB : Kraus.IsInjective (blockTensor B q) :=
    (isNBlkInjective_iff_blockTensor_isInjective B q).1 (isNBlkInjective_of_le hLpos hL hLq)
  refine ⟨approximatingMPVState B σ q M, norm_approximatingMPVState B hB hσ.posSemidef htr M,
    hC B σ hσ.posSemidef htr q h3D hB M, ?_⟩
  rw [← norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv (M * q))]
  refine (herr q M).trans ?_
  rw [hexp]
  -- `K M e^{-r q} ≤ ε` from `r q ≥ log K + log(Mq/ε) ≥ log K + log(M/ε)`.
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hlogN : Real.log ((M * q : ℕ) / ε) = Real.log M + Real.log q - Real.log ε := by
    push_cast
    rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by positivity) (by positivity)]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hrq : Real.log K + Real.log M - Real.log ε ≤ r * q := by
    have h1 : r * (1 / r * Real.log ((M * q : ℕ) / ε) + max (Real.log K) 0 / r) ≤ r * q := by
      refine mul_le_mul_of_nonneg_left ?_ hr0.le
      have : (0 : ℝ) ≤ L + 3 * D + 1 := by positivity
      linarith
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hr0.ne', one_mul,
      mul_div_cancel₀ _ hr0.ne', hlogN] at h1
    linarith [le_max_left (Real.log K) 0]
  calc K * (M * Real.exp (-(r * q)))
      = Real.exp (Real.log K + Real.log M - r * q) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hK, Real.exp_log (by positivity),
          Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (by linarith)
    _ = ε := Real.exp_log hε

/-- **Preparation in depth `O(log(N/ε))`**, arXiv:2307.01696, eq. (1), for block lengths
dividing the chain length. For every normal tensor `A` there are `a > 0`, `b ≥ 1` and `c`,
depending only on `A`, with the following property. For `N ≥ 2`, `0 < ε ≤ 1`, and a block length
`q` dividing `N` with `a log(N/ε) + b ≤ q ≤ 2 (a log(N/ε) + b)`, for example
`q = ⌈a log(N/ε) + b⌉` when it divides `N` (the upper bound holds because `b ≥ 1`), some unit
vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a product state in depth at most
`c log(N/ε)`.

arXiv:2307.01696, eq. (1) (`T=O(\log (N/\eps))`) and the sentence after Lemma 1 ("it follows
that $q = O (\log (N / \epsilon))$"); the depth is `C q` with `C` depending only on `d` and `D`
(`exists_isPreparedInDepth_approximationError_le`). The block length divides `N`, the scope
restriction recorded in the module docstring. -/
theorem exists_isPreparedInDepth_le_log {D : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ a b c : ℝ, 0 < a ∧ 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N q : ℕ) [NeZero N], 2 ≤ N → q ∣ N → a * Real.log (N / ε) + b ≤ q →
        (q : ℝ) ≤ 2 * (a * Real.log (N / ε) + b) →
          ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
            IsPreparedInDepth T (fun s => ψ s) ∧ 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_approximationError_le d D
  obtain ⟨a, b, ha, hb, h⟩ := hC A hA
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨a, b, C * (2 * a + 2 * b / Real.log 2), ha, hb, fun ε hε hε1 N q _ hN hqN hq hq2 => ?_⟩
  obtain ⟨ψ, hψ, hprep, herr⟩ := h ε hε hε1 N q hqN hq
  refine ⟨ψ, C * q, hψ, ?_, hprep, herr⟩
  have hl : Real.log 2 ≤ Real.log (N / ε) := by
    refine Real.log_le_log two_pos ?_
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact this.trans (le_div_self (by positivity) hε hε1)
  have hbl : b ≤ b / Real.log 2 * Real.log (N / ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hl (zero_le_one.trans hb)
  push_cast
  calc (C : ℝ) * q ≤ C * (2 * (a * Real.log (N / ε) + b)) :=
        mul_le_mul_of_nonneg_left hq2 (Nat.cast_nonneg _)
    _ ≤ C * ((2 * a + 2 * b / Real.log 2) * Real.log (N / ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have e : (2 * a + 2 * b / Real.log 2) * Real.log (N / ε) =
            2 * (a * Real.log (N / ε)) + 2 * (b / Real.log 2 * Real.log (N / ε)) := by ring
        rw [e]
        linarith
    _ = _ := by ring

end MPSPreparation
