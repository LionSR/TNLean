/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.DecayingCorrelationBound
import TNLean.MPS.Preparation.DepthLowerBoundCore

/-!
# No preparation of a normal matrix product state in depth `o(log N)`

For a normal tensor `A` in the gauge `eq:ldp_normal_gauge` with correlation length `ξ > 0`, a
unit vector `ψ` prepared from a product vector by a local circuit of depth `T` has overlap
`|⟨φ_N|ψ⟩| < 1/2` with the normalized periodic vector `φ_N` unless `N ≤ C (T+1) e^{b(T+1)}`
(`exists_depth_lower_bound`). Hence for depths `T_N = o(log N)` the error
`ε(φ_N, ψ_N) = 1 - |⟨φ_N|ψ_N⟩|` exceeds `1/2` for all large `N`
(`eventually_one_half_lt_infidelity_of_isLittleO_log`); this is arXiv:2307.01696, Theorem 1,
for a normal tensor in the gauge of its eq. (5).

The proof is the chapter's proof of `thm:ldp_depth_lower_bound`, not the source's. The source
(Supplemental Material, "Proof of Theorem 1") replaces `φ_N` by the blocked approximation of its
Lemma 1, bounds a fidelity of product states, and applies its Lemma 2 at the single separation
`s = 2T + 1` together with the exact vanishing of one-point functions; neither of the last two
holds in general (see `docs/paper-gaps/mswc24_decaying_correlations_windowed_connected.tex`).
The chapter instead takes the separation `s'` from the windowed correlation estimate
`exists_decayingCorrelations`, places the centred observables on `n ≈ N/Δ` windows spaced
`Δ = s' + L + 2T` apart, and compares the averages `Z₁ = (1/n) ∑ ±𝒪^{(k)}` and
`Z₂ = (1/n) ∑ 𝒪^{(k)} 𝒪'^{(k)}` in `φ_N` and `ψ` through the expectation-overlap inequality
`lem:ldp_expectation_overlap`. The variances are of order `1/n` in both states
(`exists_norm_sub_inner_smul_sq_le_mpv`,
`MPSPreparation.norm_sub_inner_smul_sq_le_of_isPreparedInDepth`), which gives
`c e^{-(s'-1)/ξ} ≤ |G_N(𝒪, 𝒪'; s')| ≤ 6S/√n` (eq. `eq:ldp_depth_contradiction`).

**Scope restriction (gauge):** the tensor is assumed to be in the gauge
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1` of arXiv:2307.01696, eq. (5), with a
blocking length `L` at which `A` is injective and a subleading eigenvalue `λ₂` of `E_A`. The
source's Theorem 1 is stated for every normal tensor; its proof, and the chapter's, first pass
to this gauge. That reduction is not formalized here, so the chapter entry
`thm:ldp_depth_lower_bound` is tagged against the separate gauge-form entry
`thm:ldp_depth_lower_bound_gauge`.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator ComplexOrder
open Filter Asymptotics

namespace MPSTensor

variable {d D : ℕ}

/-! ### The quantitative bound -/

private theorem lt_one_of_correlationLength_pos {lam₂ : ℂ} (hξ : 0 < correlationLength lam₂) :
    0 < ‖lam₂‖ ∧ ‖lam₂‖ < 1 := by
  have hlog : Real.log ‖lam₂‖ < 0 := by
    by_contra h
    push Not at h
    have : correlationLength lam₂ ≤ 0 := by
      unfold correlationLength
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, h⟩)
    linarith
  have hpos : 0 < ‖lam₂‖ := by
    rcases (norm_nonneg lam₂).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hlog
      exact absurd hlog (lt_irrefl 0)
  exact ⟨hpos, (Real.log_neg_iff hpos).mp hlog⟩

/-- **Depth lower bound, quantitative form.** Let `A` be normal in the gauge
`eq:ldp_normal_gauge` (arXiv:2307.01696, eq. (5)), with the products of `L` matrices spanning
the matrix algebra, and let `λ₂` be an eigenvalue of `E_A` of largest modulus among those
different from `1`, with correlation length `ξ = -1/log|λ₂| > 0`. There are constants `B`,
`C`, `b > 0` such that for every depth `T` and every `N ≥ B (T + 1)`: if a unit vector `ψ`
prepared in depth `T` satisfies `|⟨φ_N|ψ⟩| ≥ 1/2`, then `N ≤ C (T + 1) e^{b (T + 1)}`.

This is the quantitative content of the chapter's proof of `thm:ldp_depth_lower_bound`,
eq. `eq:ldp_depth_contradiction` (the chapter's version of arXiv:2307.01696, Supplemental
Material, "Proof of Theorem 1"). -/
theorem exists_depth_lower_bound {A : MPSTensor d D} {L : ℕ} (hL1 : 1 ≤ L)
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ 1)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) :
    ∃ B : ℕ, ∃ C b : ℝ, 0 < C ∧ 0 < b ∧ ∀ (T N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      MPSPreparation.IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 → B * (T + 1) ≤ N →
        1 / 2 ≤ ‖⟪normalizedMPVState A N, (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ →
          (N : ℝ) ≤ C * (T + 1) * Real.exp (b * (T + 1)) := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp [Matrix.trace] at hρtr⟩
  obtain ⟨hpos, hlt1⟩ := lt_one_of_correlationLength_pos hξ
  set ξ := correlationLength lam₂ with hξ_def
  obtain ⟨O, O', hOh, hO'h, hOn, hO'n, c, hc, K, hK1, hK2, -, s₀, hs₀, hdec⟩ :=
    exists_decayingCorrelations hL1 hL hA hρ hρfix hρtr hlam₂ hlam₂1 hmax hξ
  obtain ⟨S, hS0, hS⟩ := exists_norm_sub_inner_smul_add_le_div_sqrt hL1 hL hA hρ hρfix hρtr
    hmax hlt1
  set Bn : ℕ := s₀ + 2 * L + 4 with hBn_def
  set β : ℕ := s₀ + L + 2 with hβ_def
  refine ⟨3 * Bn, 72 * S ^ 2 * Bn / c ^ 2 + 1, 2 * β / ξ + 1, by positivity, by positivity, ?_⟩
  intro T N _ ψ hψ hψ1 hN hover
  /- If `φ_N(A) = 0` the overlap vanishes. -/
  by_cases hne : mpvState A N = 0
  · exfalso
    have : normalizedMPVState A N = 0 := by rw [normalizedMPVState, hne, smul_zero]
    rw [this, inner_zero_left, norm_zero] at hover
    norm_num at hover
  have hφeq : normalizedMPVState A N = ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N := rfl
  rw [hφeq] at hover
  /- The separation `s'` and the spacing `Δ`. -/
  obtain ⟨s', hss', hs'K, hdecN⟩ := hdec (max s₀ (2 * T + L + 1)) (le_max_left _ _)
  have hs'1 : 2 * T + L + 1 ≤ s' := (le_max_right _ _).trans hss'
  have hs'2 : s' ≤ s₀ + 2 * T + L + 2 := by
    have := max_le_iff.mpr ⟨Nat.le_add_right s₀ (2 * T + L + 1),
      (by omega : 2 * T + L + 1 ≤ s₀ + (2 * T + L + 1))⟩
    omega
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = s' + L + 2 * T := ⟨_, rfl⟩
  have hΔB : Δ ≤ Bn * (T + 1) := by
    have h4 : (s₀ + 2 * L + 4) * (T + 1) = (s₀ + 2 * L) * (T + 1) + 4 * T + 4 := by ring
    have h5 : s₀ + 2 * L ≤ (s₀ + 2 * L) * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [hBn_def]
    omega
  have hs'β : s' ≤ β * (T + 1) := by
    have h4 : (s₀ + L + 2) * (T + 1) = (s₀ + L) * (T + 1) + 2 * T + 2 := by ring
    have h5 : s₀ + L ≤ (s₀ + L) * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [hβ_def]
    omega
  have hN3 : 3 * Δ ≤ N := by
    have := Nat.mul_le_mul_left 3 hΔB
    rw [← Nat.mul_assoc] at this
    omega
  have hΔpos : 0 < Δ := by omega
  obtain ⟨n, hn_def⟩ : ∃ n, n = N / Δ := ⟨_, rfl⟩
  have hnΔ : n * Δ ≤ N := hn_def ▸ Nat.div_mul_le_self N Δ
  have hn3 : 3 ≤ n := hn_def ▸ (Nat.le_div_iff_mul_le hΔpos).mpr (by omega)
  have hNlt : N < n * Δ + Δ := hn_def ▸ Nat.lt_div_mul_add hΔpos
  have hN2 : N ≤ 2 * (n * Δ) := by
    have : Δ ≤ n * Δ := Nat.le_mul_of_pos_left Δ (by omega)
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  /- The two bounds on the correlator. -/
  have hG := norm_mpvConnectedCorrelator_le_of_overlap hS hψ hψ1 hne hOh hO'h hOn hO'n
    (by omega) hs'1 (by omega) hover
  rw [← hΔ, ← hn_def] at hG
  have hlow := hdecN N (by omega)
  set E : ℝ := Real.exp (-((s' : ℝ) - 1) / ξ) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have hcE : c * E ≤ 6 * (S / Real.sqrt n) := hlow.trans hG
  have hsq : (c * E) ^ 2 ≤ 36 * S ^ 2 / n := by
    have h := pow_le_pow_left₀ (by positivity) hcE 2
    calc (c * E) ^ 2 ≤ (6 * (S / Real.sqrt n)) ^ 2 := h
      _ = 36 * S ^ 2 / n := by rw [mul_pow, div_pow, Real.sq_sqrt hn0.le]; ring
  have hN2' : (N : ℝ) ≤ 2 * n * Δ := by exact_mod_cast (by linarith [hN2] : N ≤ 2 * n * Δ)
  have hkey : (N : ℝ) * (c * E) ^ 2 ≤ 72 * S ^ 2 * Δ := by
    calc (N : ℝ) * (c * E) ^ 2 ≤ (2 * n * Δ) * (36 * S ^ 2 / n) :=
          mul_le_mul hN2' hsq (by positivity) (by positivity)
      _ = 72 * S ^ 2 * Δ := by field_simp; ring
  have hΔB' : (Δ : ℝ) ≤ Bn * (T + 1) := by exact_mod_cast hΔB
  have hs'β' : (s' : ℝ) ≤ β * (T + 1) := by exact_mod_cast hs'β
  have hEinv : (E ^ 2)⁻¹ ≤ Real.exp ((2 * β / ξ + 1) * (T + 1)) := by
    rw [hE_def, ← Real.exp_nat_mul, ← Real.exp_neg]
    refine Real.exp_le_exp.mpr ?_
    have hT0 : (0 : ℝ) ≤ T + 1 := by positivity
    have h1 : -((2 : ℕ) * (-((s' : ℝ) - 1) / ξ)) = 2 / ξ * ((s' : ℝ) - 1) := by
      push_cast; ring
    rw [h1]
    calc 2 / ξ * ((s' : ℝ) - 1) ≤ 2 / ξ * (β * (T + 1)) := by
          gcongr
          linarith
      _ = 2 * β / ξ * (T + 1) := by ring
      _ ≤ (2 * β / ξ + 1) * (T + 1) := by nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  calc (N : ℝ) = N * (c * E) ^ 2 * (E ^ 2)⁻¹ / c ^ 2 := by
        field_simp
    _ ≤ 72 * S ^ 2 * Δ * (E ^ 2)⁻¹ / c ^ 2 := by gcongr
    _ ≤ 72 * S ^ 2 * (Bn * (T + 1)) * Real.exp ((2 * β / ξ + 1) * (T + 1)) / c ^ 2 := by
        gcongr
    _ = 72 * S ^ 2 * Bn / c ^ 2 * (T + 1) * Real.exp ((2 * β / ξ + 1) * (T + 1)) := by ring
    _ ≤ (72 * S ^ 2 * Bn / c ^ 2 + 1) * (T + 1) * Real.exp ((2 * β / ξ + 1) * (T + 1)) := by
        gcongr
        linarith

/-! ### Depths `o(log N)` -/

/-- **No preparation in depth `o(log N)`, gauge form.** Let `A` be normal in the gauge
`eq:ldp_normal_gauge` (arXiv:2307.01696, eq. (5)), with the products of `L` matrices spanning
the matrix algebra, and let `λ₂` be an eigenvalue of `E_A` of largest modulus among those
different from `1`, with correlation length `ξ = -1/log|λ₂| > 0`. Let `ψ_N` be unit vectors
prepared in depth `T_N` with `T_N = o(log N)`. Then `ε(φ_N, ψ_N) = 1 - |⟨φ_N|ψ_N⟩| > 1/2`
for all sufficiently large `N`.

This is arXiv:2307.01696, Theorem 1 (label `th:1`: "If `T=o(log N)` there is some `N_0` such
that for all `N>N_0` we have `ε > 1/2`"), in the setting stated before it: `φ_N` generated
"by a normal tensor `A`, with finite correlation length `ξ>0`", and `ψ_N` "obtained from
depth-`T` local quantum circuits applied to product states". The tensor is taken in the gauge
of the source's eq. (5); see the module docstring for this scope restriction. The hypothesis `T_N = o(log N)` is `Asymptotics.IsLittleO` along `atTop`. -/
theorem eventually_one_half_lt_infidelity_of_isLittleO_log {A : MPSTensor d D} {L : ℕ}
    (hL1 : 1 ≤ L) (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ 1)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) {T : ℕ → ℕ}
    (hT : (fun N ↦ (T N : ℝ)) =o[atTop] fun N ↦ Real.log N) (ψ : ∀ N, Cfg d N → ℂ)
    (hψ : ∀ (N : ℕ) [NeZero N], MPSPreparation.IsPreparedInDepth (T N) (ψ N))
    (hψ1 : ∀ N, star (ψ N) ⬝ᵥ ψ N = 1) :
    ∀ᶠ N in atTop, 1 / 2 <
      1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 (ψ N) : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ := by
  obtain ⟨B, C, b, hC, hb, hcore⟩ :=
    exists_depth_lower_bound hL1 hL hA hρ hρfix hρtr hlam₂ hlam₂1 hmax hξ
  set Kc : ℝ := (max C B + 1) * Real.exp (b + 1) with hKc_def
  have hKc : 0 < Kc := by positivity
  have hε : (0 : ℝ) < 1 / (2 * (b + 1)) := by positivity
  have hTb := hT.bound hε
  have hbig : ∀ᶠ N : ℕ in atTop, Kc ^ 2 < N := by
    obtain ⟨m, hm⟩ := exists_nat_gt (Kc ^ 2)
    filter_upwards [eventually_ge_atTop m] with N hN
    exact hm.trans_le (by exact_mod_cast hN)
  filter_upwards [hTb, hbig, eventually_ge_atTop 1] with N hTN hN hN1
  haveI : NeZero N := ⟨by omega⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  rw [Real.norm_natCast, Real.norm_of_nonneg hlog] at hTN
  -- `(b + 1)(T + 1) ≤ (b + 1) + log N / 2`
  have hexp : (b + 1) * ((T N : ℝ) + 1) ≤ (b + 1) + Real.log N / 2 := by
    have : (b + 1) * (T N : ℝ) ≤ Real.log N / 2 := by
      have h := mul_le_mul_of_nonneg_left hTN (by positivity : (0 : ℝ) ≤ b + 1)
      calc (b + 1) * (T N : ℝ) ≤ (b + 1) * (1 / (2 * (b + 1)) * Real.log N) := h
        _ = Real.log N / 2 := by field_simp
    linarith
  have hsqrt : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
    ring_nf
  have hKsqrt : Kc < Real.sqrt N := by
    rw [Real.lt_sqrt hKc.le]
    exact hN
  -- `x ≤ e^{b x}` bound for `x = T + 1`
  have hT1 : ((T N : ℝ) + 1) * Real.exp (b * ((T N : ℝ) + 1)) ≤
      Real.exp ((b + 1) * ((T N : ℝ) + 1)) := by
    have h := Real.add_one_le_exp ((T N : ℝ) + 1)
    have e : Real.exp ((b + 1) * ((T N : ℝ) + 1)) =
        Real.exp ((T N : ℝ) + 1) * Real.exp (b * ((T N : ℝ) + 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hE : Real.exp ((b + 1) * ((T N : ℝ) + 1)) ≤ Real.exp (b + 1) * Real.sqrt N := by
    rw [← hsqrt, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  by_contra hcon
  push Not at hcon
  have hover : 1 / 2 ≤
      ‖⟪normalizedMPVState A N, (WithLp.toLp 2 (ψ N) : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ := by
    linarith
  have hBN : B * (T N + 1) ≤ N := by
    have h1 : (B : ℝ) * ((T N : ℝ) + 1) ≤ B * Real.exp ((b + 1) * ((T N : ℝ) + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := Real.add_one_le_exp ((b + 1) * ((T N : ℝ) + 1))
      nlinarith
    have h2 : (B : ℝ) * Real.exp ((b + 1) * ((T N : ℝ) + 1)) ≤ Kc * Real.sqrt N := by
      rw [hKc_def]
      calc (B : ℝ) * Real.exp ((b + 1) * ((T N : ℝ) + 1))
          ≤ (max C B + 1) * (Real.exp (b + 1) * Real.sqrt N) := by
            gcongr
            linarith [le_max_right C (B : ℝ)]
        _ = _ := by ring
    have h3 : Kc * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hKsqrt.le (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hNpos.le] at h3
    exact_mod_cast h1.trans (h2.trans h3)
  have hle := hcore (T N) N (ψ N) (hψ N) (hψ1 N) hBN hover
  have h2 : C * ((T N : ℝ) + 1) * Real.exp (b * ((T N : ℝ) + 1)) < N := by
    calc C * ((T N : ℝ) + 1) * Real.exp (b * ((T N : ℝ) + 1))
        = C * (((T N : ℝ) + 1) * Real.exp (b * ((T N : ℝ) + 1))) := by ring
      _ ≤ C * (Real.exp (b + 1) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (hT1.trans hE) hC.le
      _ ≤ Kc * Real.sqrt N := by
          rw [hKc_def]
          have : C ≤ max C B + 1 := by linarith [le_max_left C (B : ℝ)]
          calc C * (Real.exp (b + 1) * Real.sqrt N)
              ≤ (max C B + 1) * (Real.exp (b + 1) * Real.sqrt N) := by gcongr
            _ = _ := by ring
      _ < Real.sqrt N * Real.sqrt N :=
          mul_lt_mul_of_pos_right hKsqrt (Real.sqrt_pos.mpr hNpos)
      _ = N := Real.mul_self_sqrt hNpos.le
  push_cast at hle
  linarith

end MPSTensor
