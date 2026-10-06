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

* `MPSPreparation.exists_approximationError_le_of_slope`: for every slope `a > ξ/2` there is
  `b₀ ≥ 0` such that the approximating state of eq. (10) has error at most `ε` once the block
  length satisfies `q ≥ a log(Mq/ε) + b₀`; it is shared with the preparation with measurements
  of `TNLean.MPS.Preparation.LogLogDepthPreparation`.
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
  obtain ⟨t, ht0, ht1, hgap⟩ := exists_eigenvalue_norm_le_of_isNormal B hNB hLC
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨L, hLpos, hL⟩ := hNB
  refine ⟨B, ζ, (Matrix.trace ρ)⁻¹ • ρ, t, L, hζ, hmpv, ⟨L, hLpos, hL⟩, hLC,
    hρ.inv_trace_smul, Matrix.trace_inv_trace_smul (ne_of_gt hρ.trace_pos),
    hPσ.fixedPoint_is_fixed, ht0, ht1, fun μ hμ hne => ?_, hnorm, fun n hn =>
      (isNBlkInjective_iff_blockTensor_isInjective B n).1 (isNBlkInjective_of_le hLpos hL hn)⟩
  rw [hnorm]; exact hgap μ hμ hne

/-- **The error at block length `q ≥ a log(Mq/ε) + b₀` for every slope `a > ξ/2`.** Let `B` be a
normal left-canonical tensor with a positive definite fixed point `σ` of trace one, with
`|φ_N(B)⟩ = ζ^N |φ_N(A)⟩` for some `ζ ≠ 0`, and let `0 < t < 1` bound the moduli of the
eigenvalues of its transfer map other than `1`, with correlation length `ξ = -1/log t`. Then for
every `a > ξ/2` there is `b₀ ≥ 0` such that for `ε > 0`, every block length `q ≥ 1` and every
number of blocks `M ≥ 1` with `q ≥ a log(Mq/ε) + b₀`, the approximating state `|φ'_N⟩` of
eq. (10) for `B` on `N = Mq` sites has error `1 - |⟨φ'_N|φ_N(A)⟩| ≤ ε`.

Project result: the rate `2γ/ξ` with `γ = ξ/(2a) < 1` of `exists_approximationError_le_mul`,
which strengthens Lemma 1'(i) of arXiv:2307.01696. -/
theorem exists_approximationError_le_of_slope {D : ℕ} {A B : MPSTensor d D} {ζ : ℂ}
    {σ : Matrix (Fin D) (Fin D) ℂ} {t : ℝ} (hζ : ζ ≠ 0)
    (hmpv : ∀ (N : ℕ) (s : Fin N → Fin d), mpv B s = ζ ^ N * mpv A s)
    (hNB : Kraus.IsNormal B) (hLC : IsLeftCanonical B) (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap B σ = σ) (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 → ‖μ‖ ≤ t)
    {a : ℝ} (ha : correlationLength t / 2 < a) :
    ∃ b₀ : ℝ, 0 ≤ b₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (q M : ℕ) [NeZero M], 1 ≤ q →
      a * Real.log (M * q / ε) + b₀ ≤ q →
        1 - ‖⟪approximatingMPVState B σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤ ε := by
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  have ha0 : 0 < a := by linarith
  -- Lemma 1'(i) at rate `2γ/ξ` with `γ = ξ/(2a) < 1`.
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul B hNB hLC hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (γ := correlationLength (t : ℂ) / (2 * a)) (by positivity)
    ((div_lt_one (by positivity)).2 (by linarith))
  have hexp : ∀ q : ℕ, Real.exp (-(2 * (correlationLength (t : ℂ) / (2 * a))) * q /
      correlationLength (t : ℂ)) = Real.exp (-(q / a)) := fun q => by
    congr 1
    field_simp
  refine ⟨a * max (Real.log K) 0, by positivity, fun ε hε q M _ hq1 hq => ?_⟩
  rw [← norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv (M * q))]
  refine (herr q M).trans ?_
  rw [hexp]
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  exact mul_mul_exp_neg_div_le_of_le hK hM1 (by exact_mod_cast hq1) ha0 hε le_rfl hq

/-- **Block length `a log(N/ε) + b` for every slope `a > ξ/2`.** There is `C`, depending only on
`d` and `D`, with the following property. Let `B` be a normal left-canonical tensor with a
positive definite fixed point `σ` of trace one, with `|φ_N(B)⟩ = ζ^N |φ_N(A)⟩` for some
`ζ ≠ 0`, and let `0 < t < 1` bound the moduli of the eigenvalues of its transfer map other
than `1`, with correlation length `ξ = -1/log t`. Then for every `a > ξ/2` there is `b ≥ 1`
such that for `0 < ε ≤ 1` and every block length `q` dividing `N ≥ 1` with
`q ≥ a log(N/ε) + b`, some unit vector `|ψ⟩` on `N` sites with
`ε(ψ, φ_N(A)) = 1 - |⟨ψ|φ_N(A)⟩| ≤ ε` is prepared from a product state in depth at most `C q`.
`exists_normalGaugeData` provides such data for every normal `A`, with some admissible bound
`t`. Any `t` in `(0, 1)` that bounds these moduli is admissible, so when the largest of
them is positive, `t` may be taken equal to it and `ξ` is then the correlation length of `B`.

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
  obtain ⟨b₀, hb₀, herr⟩ := exists_approximationError_le_of_slope hζ hmpv hNB hLC hσ htr hfix
    ht0 ht1 hlam ha
  obtain ⟨L, hLpos, hL⟩ := hNB
  have hinj : ∀ n, L ≤ n → Kraus.IsInjective (blockTensor B n) := fun n hn =>
    (isNBlkInjective_iff_blockTensor_isInjective B n).1 (isNBlkInjective_of_le hLpos hL hn)
  refine ⟨b₀ + L + 3 * D + 1, by linarith, fun ε hε hε1 N q _ hqN hq => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog0 : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hbq : b₀ + L + 3 * D + 1 ≤ q := by
    have : 0 ≤ a * Real.log (N / ε) := by positivity
    linarith
  have hLq : L ≤ q := by exact_mod_cast (show (L : ℝ) ≤ q by linarith)
  have h3D : 3 * D ≤ q := by exact_mod_cast (show ((3 * D : ℕ) : ℝ) ≤ q by push_cast; linarith)
  have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  obtain ⟨M, hM⟩ := hqN
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hB : Kraus.IsInjective (blockTensor B q) := hinj q hLq
  refine ⟨approximatingMPVState B σ q M, norm_approximatingMPVState B hB hσ.posSemidef htr M,
    hC B σ hσ.posSemidef htr q h3D hB M, herr ε hε q M hq1 ?_⟩
  push_cast at hq
  have : (0 : ℝ) ≤ L + 3 * D + 1 := by positivity
  linarith

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

/-- **From `q ≤ 2 (a log(N/ε) + b)` to depth `O(log(N/ε))`.** For `N ≥ 2`, `0 < ε ≤ 1` and
`b ≥ 1`, a block length `q ≤ 2 (a log(N/ε) + b)` gives `C q ≤ C (2a + 2b/log 2) log(N/ε)`,
because `log(N/ε) ≥ log 2`. This is the last step from a depth `C q` to the depth
`O(log(N/ε))` of arXiv:2307.01696, eq. (1). -/
theorem natCast_mul_le_mul_log_of_le_two_mul {C N q : ℕ} {a b ε : ℝ} (hN : 2 ≤ N) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hb : 1 ≤ b) (hq : (q : ℝ) ≤ 2 * (a * Real.log (N / ε) + b)) :
    ((C * q : ℕ) : ℝ) ≤ C * (2 * a + 2 * b / Real.log 2) * Real.log (N / ε) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl : Real.log 2 ≤ Real.log (N / ε) := by
    refine Real.log_le_log two_pos ?_
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact this.trans (le_div_self (by positivity) hε hε1)
  have hbl : b ≤ b / Real.log 2 * Real.log (N / ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hl (zero_le_one.trans hb)
  push_cast
  calc (C : ℝ) * q ≤ C * (2 * (a * Real.log (N / ε) + b)) :=
        mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ ≤ C * ((2 * a + 2 * b / Real.log 2) * Real.log (N / ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have e : (2 * a + 2 * b / Real.log 2) * Real.log (N / ε) =
            2 * (a * Real.log (N / ε)) + 2 * (b / Real.log 2 * Real.log (N / ε)) := by ring
        rw [e]
        linarith
    _ = _ := by ring

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
  refine ⟨a, b, C * (2 * a + 2 * b / Real.log 2), ha, hb, fun ε hε hε1 N q _ hN hqN hq hq2 => ?_⟩
  obtain ⟨ψ, hψ, hprep, herr⟩ := h ε hε hε1 N q hqN hq
  exact ⟨ψ, C * q, hψ, natCast_mul_le_mul_log_of_le_two_mul hN hε hε1 hb hq2, hprep, herr⟩

end MPSPreparation
