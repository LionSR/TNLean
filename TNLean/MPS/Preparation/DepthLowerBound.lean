/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExpectationOverlap
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.BlockVariance
import TNLean.MPS.Preparation.DecayingCorrelationBound

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

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator
open Filter Asymptotics

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

/-- The normalized expectation of the identity is `1` when `φ_N(A) ≠ 0`. -/
theorem mpvExpectation_one (A : MPSTensor d D) {N : ℕ} (h : mpvState A N ≠ 0) :
    mpvExpectation A N 1 = 1 := by
  have hχ := norm_inv_smul_mpvState h
  simp only [mpvExpectation, Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  rw [inner_self_eq_norm_sq_to_K, hχ]
  norm_num

/-- For a symmetric operator `S`, the expectation `⟪χ, S χ⟫` is real. -/
theorem _root_.LinearMap.IsSymmetric.star_inner_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {S : E →ₗ[ℂ] E} (hS : S.IsSymmetric) (χ : E) :
    star ⟪χ, S χ⟫_ℂ = ⟪χ, S χ⟫_ℂ := by
  change starRingEnd ℂ _ = _
  rw [← hS χ χ]
  exact hS.conj_inner_sym χ χ

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
  set r : ℝ := (‖lam₂‖ + 1) / 2 with hr_def
  have hr : ‖lam₂‖ < r := by rw [hr_def]; linarith
  have hr1 : r < 1 := by rw [hr_def]; linarith
  obtain ⟨C', hC'0, hvarφ⟩ := exists_norm_sub_inner_smul_sq_le_mpv hL1 hL hA hρ hρfix hρtr hmax
    hr hr1 (M := 4) (by norm_num)
  set S : ℝ := Real.sqrt (3 * C') + Real.sqrt 96 with hS_def
  have hS0 : 0 ≤ S := by positivity
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
  set φ : MPVSpace d N := ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N with hφ_def
  have hφ : ‖φ‖ = 1 := norm_inv_smul_mpvState hne
  set χ : EuclideanSpace ℂ (Cfg d N) := WithLp.toLp 2 ψ with hχ_def
  have hχ : ‖χ‖ = 1 := by
    have h : ⟪χ, χ⟫_ℂ = 1 := by
      have := MPSPreparation.inner_toLp_toEuclideanLin ψ 1
      rw [MPSPreparation.expect_one, hψ1] at this
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_one] using this
    rw [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖χ‖ ^ 2 = 1 := by exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  /- The separation `s'` and the spacing `Δ`. -/
  obtain ⟨s', hss', hs'K, hdecN⟩ := hdec (max s₀ (2 * T + L + 1)) (le_max_left _ _)
  have hs'1 : 2 * T + L + 1 ≤ s' := (le_max_right _ _).trans hss'
  have hs'2 : s' ≤ s₀ + 2 * T + L + 2 := by
    have := max_le_iff.mpr ⟨Nat.le_add_right s₀ (2 * T + L + 1),
      (by omega : 2 * T + L + 1 ≤ s₀ + (2 * T + L + 1))⟩
    omega
  set Δ : ℕ := s' + L + 2 * T with hΔ_def
  have hΔB : Δ ≤ Bn * (T + 1) := by
    have : s₀ + 2 * L + 4 ≤ (s₀ + 2 * L + 4) * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
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
  set n : ℕ := N / Δ with hn_def
  have hΔpos : 0 < Δ := by omega
  have hnΔ : n * Δ ≤ N := Nat.div_mul_le_self N Δ
  have hn3 : 3 ≤ n := (Nat.le_div_iff_mul_le hΔpos).mpr (by omega)
  have hNlt : N < n * Δ + Δ := Nat.lt_div_mul_add hΔpos
  have hN2 : N ≤ 2 * (n * Δ) := by
    have : Δ ≤ n * Δ := Nat.le_mul_of_pos_left Δ (by omega)
    omega
  have hL0 : 0 < L := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  /- The centred observables. -/
  set e : ℂ := mpvExpectation A N (chainWindowOperator N 0 O) with he_def
  set e' : ℂ := mpvExpectation A N (chainWindowOperator N (s' - 1) O') with he'_def
  have hsym : ∀ {Q : Matrix (Cfg d N) (Cfg d N) ℂ}, Q.IsHermitian →
      star (mpvExpectation A N Q) = mpvExpectation A N Q := fun hQ ↦
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ).star_inner_self _
  have he : star e = e := hsym (chainWindowOperator_isHermitian (by omega) (by omega) hOh)
  have he' : star e' = e' := hsym (chainWindowOperator_isHermitian (by omega) (by omega) hO'h)
  have heN : ‖e‖ ≤ 1 := (norm_mpvExpectation_le A N _).trans
    ((norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) O).trans hOn.le)
  have he'N : ‖e'‖ ≤ 1 := (norm_mpvExpectation_le A N _).trans
    ((norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) O').trans hO'n.le)
  set X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ := O - e • 1 with hX_def
  set Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ := O' - e' • 1 with hY_def
  have hX : X.IsHermitian := hOh.sub_smul_one he
  have hY : Y.IsHermitian := hO'h.sub_smul_one he'
  have hXn : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) X‖ ≤ 2 :=
    (Matrix.norm_toEuclideanCLM_sub_smul_one_le O e).trans (by rw [hOn]; linarith)
  have hYn : ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Y‖ ≤ 2 :=
    (Matrix.norm_toEuclideanCLM_sub_smul_one_le O' e').trans (by rw [hO'n]; linarith)
  /- The pair operator on `w = s' - 1 + L` sites. -/
  set w : ℕ := s' - 1 + L with hw_def
  set W : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ :=
    chainWindowOperator w 0 X * chainWindowOperator w (s' - 1) Y with hW_def
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
  have hPQ : ∀ k : Fin n, chainWindowOperator N (k.val * Δ) W =
      chainWindowOperator N (k.val * Δ) X * chainWindowOperator N (k.val * Δ + (s' - 1)) Y := by
    intro k
    rw [hW_def, chainWindowOperator_mul (hwinW k).1 (hwinW k).2,
      chainWindowOperator_chainWindowOperator (hwinW k).1 (hwinW k).2 (by omega) (by omega),
      chainWindowOperator_chainWindowOperator (hwinW k).1 (hwinW k).2 (by omega) (by omega),
      add_zero]
  have hQwin : ∀ k : Fin n, k.val * Δ + (s' - 1) < N ∧ k.val * Δ + (s' - 1) + L ≤ N := by
    intro k
    have := hwinW k
    omega
  /- One-window expectations in `φ` are translation invariant. -/
  have hPφ : ∀ k : Fin n, mpvExpectation A N (chainWindowOperator N (k.val * Δ) O) = e :=
    fun k ↦ mpvExpectation_chainWindowOperator_eq A hL0 (hwinL k).2 O
  have hQφ : ∀ k : Fin n,
      mpvExpectation A N (chainWindowOperator N (k.val * Δ + (s' - 1)) O') = e' := by
    intro k
    rw [he'_def, mpvExpectation_chainWindowOperator_eq A hL0 (hQwin k).2 O',
      mpvExpectation_chainWindowOperator_eq A hL0 (a := s' - 1) (by omega) O']
  /- The expectations in `ψ`. -/
  set x : Fin n → ℂ := fun k ↦
    ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) χ⟫_ℂ with hx_def
  have hxim : ∀ k, (x k).im = 0 := fun k ↦
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwinL k).1 (hwinL k).2 hX)).im_inner_self_apply χ
  set ε : Fin n → ℝ := fun k ↦ if 0 ≤ (x k).re then 1 else -1 with hε_def
  have hεx : ∀ k, (ε k : ℂ) * x k = (‖x k‖ : ℂ) := by
    intro k
    have hx : x k = ((x k).re : ℂ) := Complex.ext (by simp) (by simp [hxim k])
    have hn : ‖x k‖ = |(x k).re| := by rw [hx, Complex.norm_real, Real.norm_eq_abs]; simp
    rw [hn]
    simp only [hε_def]
    split_ifs with h
    · rw [abs_of_nonneg h, hx]; simp
    · rw [abs_of_neg (not_le.mp h)]
      conv_lhs => rw [hx]
      push_cast
      ring
  set c1 : Fin n → ℝ := fun k ↦ ε k / n with hc1_def
  have hc1 : ∀ k, |c1 k| ≤ 1 / n := by
    intro k
    simp only [hc1_def, hε_def, abs_div, Nat.abs_cast]
    split_ifs <;> simp
  set u : ℝ := 1 / Real.sqrt n with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hσ : ∀ {v a : ℝ}, 0 ≤ v → 0 ≤ a → v ^ 2 ≤ (1 / n) ^ 2 * (3 * n * a) →
      v ≤ Real.sqrt (3 * a) * u := by
    intro v a hv ha h
    have e1 : (1 / (n : ℝ)) ^ 2 * (3 * n * a) = (Real.sqrt (3 * a) * u) ^ 2 := by
      rw [hu_def, mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le]
      field_simp
    rw [e1] at h
    exact (pow_le_pow_iff_left₀ hv (by positivity) two_ne_zero).mp h
  /- The first average. -/
  set Z₁ := ∑ k : Fin n, (c1 k : ℂ) •
    Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) with hZ₁_def
  have hZ₁sym : Z₁.IsSymmetric := LinearMap.isSymmetric_sum _ fun k _ ↦
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwinL k).1 (hwinL k).2 hX)).smul (Complex.conj_ofReal _)
  have hZ₁φ : ⟪φ, Z₁ φ⟫_ℂ = 0 := by
    simp only [hZ₁_def, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, inner_sum,
      inner_smul_right]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have h0 : ⟪φ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X) φ⟫_ℂ =
        mpvExpectation A N (chainWindowOperator N (k.val * Δ) X) := rfl
    rw [h0, hX_def, chainWindowOperator_sub_smul_one (hwinL k).1 (hwinL k).2, mpvExpectation_sub,
      mpvExpectation_smul, mpvExpectation_one A hne, hPφ k, mul_one, sub_self, mul_zero]
  have hZ₁χ : ⟪χ, Z₁ χ⟫_ℂ = (((∑ k, ‖x k‖) / n : ℝ) : ℂ) := by
    simp only [hZ₁_def, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, inner_sum,
      inner_smul_right]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hc1_def]
    push_cast
    rw [div_mul_eq_mul_div, hεx]
  have hvφ1 := hvarφ L Δ n N hL0 (by omega) hnΔ hne X hX (hXn.trans (by norm_num)) c1 (1 / n) hc1
  have hvχ1 := MPSPreparation.norm_sub_inner_smul_sq_le_of_isPreparedInDepth hL0 (by omega) hnΔ
    hψ hψ1 hX (hXn.trans (by norm_num : (2 : ℝ) ≤ 4)) c1 hc1
  rw [← hφ_def, ← hZ₁_def] at hvφ1
  rw [← hχ_def, ← hZ₁_def] at hvχ1
  have hσφ1 := hσ (norm_nonneg _) hC'0 hvφ1
  have hσχ1 := hσ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 4 ^ 2) hvχ1
  have hov1 := hZ₁sym.norm_inner_mul_norm_sub_le hφ hχ
  rw [hZ₁φ, hZ₁χ, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hov1
  set a : ℝ := (∑ k, ‖x k‖) / n with ha_def
  have ha0 : 0 ≤ a := by positivity
  have h96 : Real.sqrt (3 * (2 * 4 ^ 2)) = Real.sqrt 96 := by norm_num
  rw [h96] at hσχ1
  have hSu : Real.sqrt (3 * C') * u + Real.sqrt 96 * u = S * u := by rw [hS_def]; ring
  have ha : a ≤ 2 * (S * u) := by
    have h1 : 1 / 2 * a ≤ ‖⟪φ, χ⟫_ℂ‖ * a := mul_le_mul_of_nonneg_right hover ha0
    linarith
  /- The second average. -/
  set Z₂ := ∑ k : Fin n, (((1 : ℝ) / n : ℝ) : ℂ) •
    Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) with hZ₂_def
  have hZ₂sym : Z₂.IsSymmetric := LinearMap.isSymmetric_sum _ fun k _ ↦
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwinW k).1 (hwinW k).2 hW)).smul (Complex.conj_ofReal _)
  set G : ℂ := mpvConnectedCorrelator A N 0 (s' - 1) O O' with hG_def
  have hpair : ∀ k : Fin n, mpvExpectation A N (chainWindowOperator N (k.val * Δ) W) = G := by
    intro k
    have hmul := mpvExpectation_chainWindowOperator_mul_eq A hL0 (a := k.val * Δ)
      (m := s' - 1 - L) (by have := hQwin k; omega) O O'
    rw [show L + (s' - 1 - L) = s' - 1 by omega] at hmul
    have hexp : (chainWindowOperator N (k.val * Δ) O - e • 1) *
        (chainWindowOperator N (k.val * Δ + (s' - 1)) O' - e' • 1) =
        chainWindowOperator N (k.val * Δ) O * chainWindowOperator N (k.val * Δ + (s' - 1)) O' -
          e' • chainWindowOperator N (k.val * Δ) O -
          e • chainWindowOperator N (k.val * Δ + (s' - 1)) O' + (e * e') • 1 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
      rw [mul_comm e' e]
      abel
    rw [hPQ k, hX_def, hY_def, chainWindowOperator_sub_smul_one (hwinL k).1 (hwinL k).2,
      chainWindowOperator_sub_smul_one (hQwin k).1 (hQwin k).2, hexp, mpvExpectation_add,
      mpvExpectation_sub, mpvExpectation_sub, mpvExpectation_smul, mpvExpectation_smul,
      mpvExpectation_smul, mpvExpectation_one A hne, hmul, hPφ k, hQφ k, hG_def,
      mpvConnectedCorrelator]
    ring
  have hZ₂φ : ⟪φ, Z₂ φ⟫_ℂ = G := by
    simp only [hZ₂_def, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, inner_sum,
      inner_smul_right]
    have h0 : ∀ k : Fin n, ⟪φ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) φ⟫_ℂ =
        G := fun k ↦ hpair k
    simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hZ₂χ : ‖⟪χ, Z₂ χ⟫_ℂ‖ ≤ 2 * a := by
    simp only [hZ₂_def, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, inner_sum,
      inner_smul_right]
    have hfac : ∀ k : Fin n,
        ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) χ⟫_ℂ =
          x k * ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ + (s' - 1)) Y) χ⟫_ℂ := by
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
        MPSPreparation.inner_toLp_toEuclideanLin, h, hx_def]
      simp only [MPSPreparation.inner_toLp_toEuclideanLin]
    have hy : ∀ k : Fin n,
        ‖⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ + (s' - 1)) Y) χ⟫_ℂ‖ ≤ 2 :=
      fun k ↦ (MPSPreparation.norm_inner_apply_le _ hχ).trans
        ((norm_toEuclideanCLM_chainWindowOperator_le (hQwin k).1 (hQwin k).2 Y).trans hYn)
    calc ‖∑ k : Fin n, ((((1 : ℝ) / n : ℝ) : ℂ)) *
          ⟪χ, Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) W) χ⟫_ℂ‖
        ≤ ∑ k : Fin n, 1 / n * (‖x k‖ * 2) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          rw [norm_mul, hfac k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
          gcongr
          exact hy k
      _ = 2 * a := by
          rw [ha_def, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hvφ2 := hvarφ w Δ n N (by omega) (by omega) hnΔ hne W hW hWn (fun _ ↦ 1 / n) (1 / n)
    (fun _ ↦ le_of_eq (abs_of_nonneg (by positivity)))
  have hvχ2 := MPSPreparation.norm_sub_inner_smul_sq_le_of_isPreparedInDepth (w := w)
    (by omega) (by omega) hnΔ hψ hψ1 hW hWn (fun _ ↦ 1 / n)
    (fun _ ↦ le_of_eq (abs_of_nonneg (by positivity)))
  rw [← hφ_def, ← hZ₂_def] at hvφ2
  rw [← hχ_def, ← hZ₂_def] at hvχ2
  have hσφ2 := hσ (norm_nonneg _) hC'0 hvφ2
  have hσχ2 := hσ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 4 ^ 2) hvχ2
  rw [h96] at hσχ2
  have hov2 := hZ₂sym.norm_inner_mul_norm_sub_le hφ hχ
  rw [hZ₂φ] at hov2
  have hG : ‖G‖ ≤ 6 * (S * u) := by
    have h1 : 1 / 2 * ‖G - ⟪χ, Z₂ χ⟫_ℂ‖ ≤ ‖⟪φ, χ⟫_ℂ‖ * ‖G - ⟪χ, Z₂ χ⟫_ℂ‖ :=
      mul_le_mul_of_nonneg_right hover (norm_nonneg _)
    have h2 : ‖G‖ ≤ ‖G - ⟪χ, Z₂ χ⟫_ℂ‖ + ‖⟪χ, Z₂ χ⟫_ℂ‖ := norm_le_norm_sub_add _ _
    linarith
  /- The lower bound on the correlator. -/
  have hlow := hdecN N (by omega)
  rw [← hG_def] at hlow
  set E : ℝ := Real.exp (-((s' : ℝ) - 1) / ξ) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have hcE : c * E ≤ 6 * (S * u) := hlow.trans hG
  have hsq : (c * E) ^ 2 ≤ 36 * S ^ 2 / n := by
    have h := pow_le_pow_left₀ (by positivity) hcE 2
    have hu2 : u ^ 2 = 1 / n := by
      rw [hu_def, div_pow, Real.sq_sqrt hn0.le, one_pow]
    calc (c * E) ^ 2 ≤ (6 * (S * u)) ^ 2 := h
      _ = 36 * S ^ 2 * u ^ 2 := by ring
      _ = 36 * S ^ 2 / n := by rw [hu2]; ring
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
    rw [add_mul, one_mul, Real.exp_add, mul_comm (Real.exp _)]
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
      _ ≤ C * (Real.exp (b + 1) * Real.sqrt N) := by gcongr; exact hT1.trans hE
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
