/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence
import TNLean.MPS.Preparation.DepthUpperBound

/-!
# Preparation in depth `O(log(N/ε))` with blocks of equal length

This file combines the depth count for the approximating state
(`MPSPreparation.exists_isPreparedInDepth_approximatingMPVState`) with the approximation error of
arXiv:2307.01696, Lemma 1'(i) (`MPSTensor.exists_approximationError_le_mul`), for the block
length `q ∝ log(N/ε)` chosen after Lemma 1 of the source ("it follows that
$q = O (\log (N / \epsilon))$"), for chains whose length is a multiple of the block length, as
for the `N/q` equal blocks of eq. (10).

* `MPSPreparation.exists_isPreparedInDepth_approximationError_le_of_slope`: the preparation below
  holds with every slope `a > ξ/2`, where `ξ = -1/log t` is the correlation length at a bound
  `t < 1` on the moduli of the transfer eigenvalues other than `1` in the gauge of eq. (5).
  Project result; the source's block length has slope `2 ξ`.
* `MPSPreparation.exists_isPreparedInDepth_approximationError_le`: there is `C`, depending only
  on `d` and `D`, such that for every normal tensor `A` there are `a > 0` and `b ≥ 1`, depending
  only on `A`, such that on `N` sites, for every block length `q` dividing `N` with
  `q ≥ a log(N/ε) + b`, a unit vector with error at most `ε` against `|φ_N⟩` is prepared in
  depth `C q`.
* `MPSPreparation.exists_isPreparedInDepth_le_log_of_dvd`: with `q` moreover at most
  `2 (a log(N/ε) + b)`, for example `q = ⌈a log(N/ε) + b⌉` when it divides `N`, the depth is at
  most `c log(N/ε)` with `c` depending only on `A`.
* `MPSPreparation.exists_normalGaugeData`: the gauge of eq. (5) of the source, with the bound on
  the subleading eigenvalues and the injectivity length used by these proofs and by those of
  `TNLean.MPS.Preparation.LogDepthPreparation`, where eq. (1) is proved for every chain length.

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

/-! ### The gauge of eq. (5) -/

/-- **The gauge of eq. (5).** A normal tensor `A` with `D ≥ 1` has a gauge-equivalent rescaling
`B`, with `|φ_N(B)⟩ = ζ^N |φ_N(A)⟩`, which is normal and left canonical with a positive definite
fixed point `σ` of trace one, together with a bound `t < 1` on the moduli of the eigenvalues of
its transfer map other than `1` and a length `L` from which on its blocked tensors are
injective.

arXiv:2307.01696, eq. (5) and the remark after it: the transfer map of a normal tensor in this
gauge has `1` as its only eigenvalue of modulus `1`. -/
theorem exists_normalGaugeData {D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (σ : Matrix (Fin D) (Fin D) ℂ) (t : ℝ) (L : ℕ),
      ζ ≠ 0 ∧ (∀ (N : ℕ) (s : Fin N → Fin d), mpv B s = ζ ^ N * mpv A s) ∧
      Kraus.IsNormal B ∧ IsLeftCanonical B ∧ σ.PosDef ∧ σ.trace = 1 ∧
      Kraus.transferMap B σ = σ ∧ 0 < t ∧ t < 1 ∧
      (∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 → ‖μ‖ ≤ ‖(t : ℂ)‖) ∧
      ‖(t : ℂ)‖ = t ∧ ∀ n, L ≤ n → Kraus.IsInjective (blockTensor B n) := by
  obtain ⟨B, ζ, ρ, hζ, hGauge, hmpv, hP, hρ, -⟩ := exists_isPrimitiveMPS_gauge_of_isNormal hA
  have hNB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  have hLC : IsLeftCanonical B := hP.norm
  have hPσ := hP.smul_inv_trace hρ
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
  obtain ⟨L, hLpos, hL⟩ := hNB
  refine ⟨B, ζ, (Matrix.trace ρ)⁻¹ • ρ, t, L, hζ, hmpv, ⟨L, hLpos, hL⟩, hLC,
    hρ.inv_trace_smul, Matrix.trace_inv_trace_smul (ne_of_gt hρ.trace_pos),
    hPσ.fixedPoint_is_fixed, ht0, ht1, fun μ hμ hne => ?_, hnorm, fun n hn =>
      (isNBlkInjective_iff_blockTensor_isInjective B n).1 (isNBlkInjective_of_le hLpos hL hn)⟩
  rw [hnorm]; exact (hgap μ hμ hne).trans (le_max_left _ _)

/-- **Block length `a log(N/ε) + b` for every slope `a > ξ/2`.** There is `C`, depending only on
`d` and `D`, with the following property. Let `B` be a normal left-canonical tensor with a
positive definite fixed point `σ` of trace one, with `|φ_N(B)⟩ = ζ^N |φ_N(A)⟩` for some
`ζ ≠ 0`, and let `0 < t < 1` bound the moduli of the eigenvalues of its transfer map other
than `1`, with correlation length `ξ = -1/log t`. Then for every `a > ξ/2` there is `b ≥ 1`
such that for `0 < ε ≤ 1` and every block length `q` dividing `N ≥ 1` with
`q ≥ a log(N/ε) + b`, some unit vector `|ψ⟩` on `N` sites with
`ε(ψ, φ_N(A)) = 1 - |⟨ψ|φ_N(A)⟩| ≤ ε` is prepared from a product state in depth at most `C q`.
`exists_normalGaugeData` provides such data for every normal `A`, with `t` arbitrarily close
to the largest modulus of the eigenvalues other than `1` when that modulus is positive; `ξ` is
the correlation length at this bound `t`.

Project result. arXiv:2307.01696, in the paragraph after Lemma 1, takes
`q = ⌈2 ξ (1 + η) ln N⌉`, a slope `2 ξ` in `log N`, and arXiv:2606.24475, App. B4, eq. (S54),
takes `q = O(ξ log(Γ L/ε))` in its notation. Here the rate `2γ/ξ` with `γ = ξ/(2a) < 1` of
`exists_approximationError_le_mul` gives every slope `a > ξ/2`. The vector
`|ψ⟩` is the approximating state `|φ'_N⟩` of eq. (10) for `B`, prepared in depth `C q` as in
the paragraph "The sequential-RG circuit" of the source. -/
theorem exists_isPreparedInDepth_approximationError_le_of_slope (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, ∀ (A B : MPSTensor d D) (ζ : ℂ) (σ : Matrix (Fin D) (Fin D) ℂ) (t : ℝ),
      ζ ≠ 0 → (∀ (N : ℕ) (s : Fin N → Fin d), mpv B s = ζ ^ N * mpv A s) →
      Kraus.IsNormal B → IsLeftCanonical B → σ.PosDef → σ.trace = 1 →
      Kraus.transferMap B σ = σ → 0 < t → t < 1 →
      (∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 → ‖μ‖ ≤ t) →
      ∀ a : ℝ, correlationLength t / 2 < a →
        ∃ b : ℝ, 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ (N q : ℕ) [NeZero N], q ∣ N → a * Real.log (N / ε) + b ≤ q →
            ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧ IsPreparedInDepth (C * q) (fun s => ψ s) ∧
              1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_approximatingMPVState d D
  refine ⟨C, fun A B ζ σ t hζ hmpv hNB hLC hσ htr hfix ht0 ht1 hlam a ha => ?_⟩
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  have ha0 : 0 < a := by linarith
  obtain ⟨L, hLpos, hL⟩ := hNB
  have hinj : ∀ n, L ≤ n → Kraus.IsInjective (blockTensor B n) := fun n hn =>
    (isNBlkInjective_iff_blockTensor_isInjective B n).1 (isNBlkInjective_of_le hLpos hL hn)
  -- Lemma 1'(i) at rate `2γ/ξ` with `γ = ξ/(2a) < 1`.
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul B ⟨L, hLpos, hL⟩ hLC hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (γ := correlationLength (t : ℂ) / (2 * a)) (by positivity)
    ((div_lt_one (by positivity)).2 (by linarith))
  have hexp : ∀ q : ℕ, Real.exp (-(2 * (correlationLength (t : ℂ) / (2 * a))) * q /
      correlationLength (t : ℂ)) = Real.exp (-(q / a)) := fun q => by
    congr 1
    field_simp
  refine ⟨a * max (Real.log K) 0 + L + 3 * D + 1, le_add_of_nonneg_left (by positivity),
    fun ε hε hε1 N q _ hqN hq => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog0 : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hbq : a * max (Real.log K) 0 + L + 3 * D + 1 ≤ q := by
    have : 0 ≤ a * Real.log (N / ε) := by positivity
    linarith
  have hmax : 0 ≤ a * max (Real.log K) 0 := by positivity
  have hLq : L ≤ q := by exact_mod_cast (show (L : ℝ) ≤ q by linarith)
  have h3D : 3 * D ≤ q := by exact_mod_cast (show ((3 * D : ℕ) : ℝ) ≤ q by push_cast; linarith)
  have hq1 : (1 : ℝ) ≤ q := by linarith
  obtain ⟨M, hM⟩ := hqN
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hB : Kraus.IsInjective (blockTensor B q) := hinj q hLq
  refine ⟨approximatingMPVState B σ q M, norm_approximatingMPVState B hB hσ.posSemidef htr M,
    hC B σ hσ.posSemidef htr q h3D hB M, ?_⟩
  rw [← norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv (M * q))]
  refine (herr q M).trans ?_
  rw [hexp]
  -- `K M e^{-q/a} ≤ ε` from `q ≥ a (log K + log(Mq/ε)) ≥ a (log K + log(M/ε))`.
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hlogN : Real.log ((M * q : ℕ) / ε) = Real.log M + Real.log q - Real.log ε := by
    push_cast
    rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by positivity) (by positivity)]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hrq : Real.log K + Real.log M - Real.log ε ≤ q / a := by
    rw [le_div_iff₀ ha0]
    have : (0 : ℝ) ≤ L + 3 * D + 1 := by positivity
    have hKm : a * Real.log K ≤ a * max (Real.log K) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) ha0.le
    have hq' : a * Real.log q ≥ 0 := by positivity
    rw [hlogN] at hq
    nlinarith
  calc K * (M * Real.exp (-(q / a)))
      = Real.exp (Real.log K + Real.log M - q / a) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hK, Real.exp_log (by positivity),
          Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (by linarith)
    _ = ε := Real.exp_log hε

/-- **Error `ε` in depth `O(q)` with `q ∝ log(N/ε)`.** There is `C`, depending only on `d` and
`D`, such that for every normal tensor `A` there are `a > 0` and `b ≥ 1`, depending only on `A`,
with the following property. For `0 < ε ≤ 1` and every block length `q` dividing `N ≥ 1` with
`q ≥ a log(N/ε) + b`, some unit vector `|ψ⟩` on `N` sites with
`ε(ψ, φ_N) = 1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a product state in depth at most `C q`.

arXiv:2307.01696, after Lemma 1: "Using \cref{lm:1}, it follows that
$q = O (\log (N / \epsilon))$", combined with the depth `T = O(q)` of the paragraph
"The sequential-RG circuit". The bond dimension is positive, as it is for the source's normal
tensors, whose transfer matrix has the leading eigenvalue `1`. The block length divides `N`,
so that the `N/q` blocks of eq. (10) all have length `q`; for general `N` see
`exists_isPreparedInDepth_le_log_of_mpvState_ne_zero`. Any slope `a > ξ/2` is admissible
(`exists_isPreparedInDepth_approximationError_le_of_slope`); this statement takes `a = ξ`. -/
theorem exists_isPreparedInDepth_approximationError_le (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, ∀ A : MPSTensor d D, Kraus.IsNormal A →
      ∃ a b : ℝ, 0 < a ∧ 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (N q : ℕ) [NeZero N], q ∣ N → a * Real.log (N / ε) + b ≤ q →
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧ IsPreparedInDepth (C * q) (fun s => ψ s) ∧
            1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_approximationError_le_of_slope d D
  refine ⟨C, fun A hA => ?_⟩
  obtain ⟨B, ζ, σ, t, -, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, -⟩ :=
    exists_normalGaugeData hA
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  obtain ⟨b, hb, h⟩ := hC A B ζ σ t hζ hmpv hNB hLC hσ htr hfix ht0 ht1
    (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm) _ (half_lt_self hξ)
  exact ⟨_, b, hξ, hb, h⟩

/-- **Preparation in depth `O(log(N/ε))` with equal blocks**, arXiv:2307.01696, eq. (1), for
block lengths dividing the chain length. For every normal tensor `A` there are `a > 0`, `b ≥ 1`
and `c`, depending only on `A`, with the following property. For `N ≥ 2`, `0 < ε ≤ 1`, and a
block length `q` dividing `N` with `a log(N/ε) + b ≤ q ≤ 2 (a log(N/ε) + b)`, for example
`q = ⌈a log(N/ε) + b⌉` when it divides `N` (the upper bound holds because `b ≥ 1`), some unit
vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared from a product state in depth at most
`c log(N/ε)`.

arXiv:2307.01696, eq. (1) (`T=O(\log (N/\eps))`) and the sentence after Lemma 1 ("it follows
that $q = O (\log (N / \epsilon))$"); the depth is `C q` with `C` depending only on `d` and `D`
(`exists_isPreparedInDepth_approximationError_le`). The block length divides `N`; for general
`N` see `exists_isPreparedInDepth_le_log_of_mpvState_ne_zero`. -/
theorem exists_isPreparedInDepth_le_log_of_dvd {D : ℕ} [NeZero D] (A : MPSTensor d D)
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
