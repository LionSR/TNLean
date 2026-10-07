/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLowerBoundNormal
import TNLean.MPS.Preparation.LogDepthPreparation

/-!
# The depth lower bound with the constant `ξ/4`, and depth `Θ(log N)`

arXiv:2307.01696, Theorem 1, states that a local circuit of depth `T = o(log N)` cannot prepare
a normal translation-invariant matrix product state `|φ_N⟩` with error
`ε(φ_N, ψ) = 1 - |⟨φ_N|ψ⟩| ≤ 1/2`. The source's proof (Supplemental Material, "Proof of
Theorem 1") is quantitative: its final chain of inequalities compares `N/log N` with a multiple
of `e^{4T/ξ}`, so error at most `1/2` forces `T ≥ (ξ/4) log N` up to a correction of order
`log log N` and a constant. This file states that bound explicitly, with the correction written
as `(ξ/4) log(T + 1)`, and combines it with the upper bound of the source's eq. (1).

* `MPSTensor.exists_log_le_of_infidelity_le_one_half`: in the gauge of the source's eq. (5),
  `ε(φ_N, ψ) ≤ 1/2` for `ψ` prepared in depth `T` forces
  `(ξ/4) log N ≤ T + (ξ/4) log(T + 1) + C`, with `C` independent of `N` and `T`.
* `MPSTensor.exists_log_le_of_infidelity_le_one_half_of_isNormal`: the same for every tensor
  some blocking of which is injective, with `ξ = -1/log|λ₂/λ₁|`.
* `MPSTensor.exists_mul_log_le_of_infidelity_le_one_half_of_isNormal`: for every slope
  `a < ξ/4`, the depth is at least `a log N - C_a`.
* `MPSTensor.exists_depth_isTheta_log`: for a fixed error `0 < ε ≤ 1/2`, the optimal depth is
  `Θ(log N)`: depth `O(log N)` suffices (eq. (1)), and every circuit with error at most `ε` has
  depth at least `a log N - C`.

**Local fix (constants of the closing inequality):** the source's closing chain contains two
slips in its constants, neither of which affects the rate `4/ξ`: `(1 - δ)^{k/2} < 1/e` gives a
trace distance above `1 - 1/e - o(1)`, not above `√(3/4)`, and an undefined factor `γ`
appears in `N/(5q) > Nγ/(10 ξ log N)`. The bound proved here is derived from the chapter's averaging
argument (`MPSTensor.exists_depth_lower_bound`), not from the source's chain, and carries the
source's rate. Documented in `docs/paper-gaps/mswc24_depth_lower_bound_constant.tex`.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open QuantumCircuit

namespace MPSTensor

variable {d D : ℕ}

/-- **The depth lower bound with the constant `ξ/4`, gauge form.** Let `A` be normal in the
gauge of arXiv:2307.01696, eq. (5), with the products of `L` matrices spanning the matrix
algebra, and let `λ₂` be an eigenvalue of `E_A` of largest modulus among those different from
`1`, with correlation length `ξ = -1/log|λ₂| > 0`. There is `C`, independent of `N` and `T`,
such that a unit vector `ψ` prepared from a product vector in depth `T` with
`ε(φ_N, ψ) = 1 - |⟨φ_N|ψ⟩| ≤ 1/2` satisfies `(ξ/4) log N ≤ T + (ξ/4) log(T + 1) + C`.

This is the explicit form of arXiv:2307.01696, Theorem 1, as its proof gives it: the closing
inequality of the Supplemental Material, "Proof of Theorem 1", compares `N/log N` with
`(18/c₁²) e^{4T/ξ}`. Here the comparison is `N ≤ C' (T + 1) e^{4T/ξ}`
(`exists_depth_lower_bound`), and for `N < B (T + 1)` the bound holds trivially. -/
theorem exists_log_le_of_infidelity_le_one_half {A : MPSTensor d D} {L : ℕ} (hL1 : 1 ≤ L)
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ 1)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) :
    ∃ C : ℝ, ∀ (T N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 →
        1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ ≤
          1 / 2 →
          correlationLength lam₂ / 4 * Real.log N ≤
            T + correlationLength lam₂ / 4 * Real.log (T + 1) + C := by
  obtain ⟨B, C₀, hC₀, hcore⟩ :=
    exists_depth_lower_bound hL1 hL hA hρ hρfix hρtr hlam₂ hlam₂1 hmax hξ
  set ξ := correlationLength lam₂ with hξ_def
  set K : ℝ := |Real.log C₀| + Real.log (B + 1) with hK_def
  refine ⟨ξ / 4 * K, fun T N _ ψ hψ hψ1 herr => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hξ0 : ξ ≠ 0 := hξ.ne'
  have hlogB : 0 ≤ Real.log ((B : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg B))
  /- In both cases `log N ≤ K + log(T + 1) + 4T/ξ`. -/
  have hkey : Real.log N ≤ K + Real.log ((T : ℝ) + 1) + 4 * T / ξ := by
    have h4T : 0 ≤ 4 * (T : ℝ) / ξ := by positivity
    by_cases hBN : B * (T + 1) ≤ N
    · have hle := hcore T N ψ hψ hψ1 hBN (by linarith)
      have hlog := Real.log_le_log hNpos hle
      rw [Real.log_mul (mul_pos hC₀ hT1).ne' (Real.exp_pos _).ne', Real.log_mul hC₀.ne' hT1.ne',
        Real.log_exp] at hlog
      have := le_abs_self (Real.log C₀)
      rw [hK_def]
      linarith
    · push Not at hBN
      have hlt : (N : ℝ) < (B + 1) * (T + 1) := by
        have : N < (B + 1) * (T + 1) :=
          hBN.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ B))
        exact_mod_cast this
      have hlog := Real.log_le_log hNpos hlt.le
      rw [Real.log_mul (by positivity) hT1.ne'] at hlog
      have := abs_nonneg (Real.log C₀)
      rw [hK_def]
      linarith
  have h := mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ ξ / 4)
  have e : ξ / 4 * (K + Real.log ((T : ℝ) + 1) + 4 * T / ξ) =
      T + ξ / 4 * Real.log ((T : ℝ) + 1) + ξ / 4 * K := by
    field_simp
    ring
  linarith

/-- **The depth lower bound with the constant `ξ/4`**, arXiv:2307.01696, Theorem 1, in the
explicit form its proof gives. Let the products of some fixed number of matrices of `A` span the
matrix algebra (`Kraus.IsNormal`), let `λ₁` be an eigenvalue of `E_A` of largest modulus, and
let `λ₂` be an eigenvalue of largest modulus among those different from `λ₁`, with correlation
length `ξ = -1/log|λ₂/λ₁| > 0`. There is `C`, independent of `N` and `T`, such that a unit vector
`ψ` prepared from a product vector in depth `T` with `ε(φ_N, ψ) ≤ 1/2` satisfies
`(ξ/4) log N ≤ T + (ξ/4) log(T + 1) + C`.

The proof reduces to the gauge of the source's eq. (5) (`exists_normalGauge_of_isNormal`), which
changes `φ_N` by a nonzero factor and divides the eigenvalues of `E_A` by `λ₁`. -/
theorem exists_log_le_of_infidelity_le_one_half_of_isNormal {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {lam₁ lam₂ : ℂ}
    (hlam₁ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₁)
    (hlam₁max : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ ≤ ‖lam₁‖)
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ lam₁)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ lam₁ → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength (lam₂ / lam₁)) :
    ∃ C : ℝ, ∀ (T N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 →
        1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ ≤
          1 / 2 →
          correlationLength (lam₂ / lam₁) / 4 * Real.log N ≤
            T + correlationLength (lam₂ / lam₁) / 4 * Real.log (T + 1) + C := by
  obtain ⟨hl0, B, ζ, L, ρ, hζ, -, hL1, hL, hTP, hρ, hfix, htr, heig, hmpv⟩ :=
    exists_normalGauge_of_isNormal hA hlam₁ hlam₁max
  have hback : ∀ ν, Module.End.HasEigenvalue (Kraus.transferMap B) ν →
      Module.End.HasEigenvalue (Kraus.transferMap A) (ν * lam₁) := fun ν hν =>
    (heig _).2 (by rwa [mul_div_cancel_right₀ _ hl0])
  obtain ⟨C, hC⟩ := exists_log_le_of_infidelity_le_one_half hL1 hL hTP hρ hfix htr
    ((heig lam₂).1 hlam₂) (fun h1 => hlam₂1 ((div_eq_one_iff_eq hl0).1 h1))
    (fun ν hν hν1 => by
      have hle := hmax _ (hback ν hν) fun h1 =>
        hν1 (mul_right_cancel₀ hl0 (h1.trans (one_mul _).symm))
      rw [norm_div]
      rw [norm_mul] at hle
      exact (le_div_iff₀ (norm_pos_iff.mpr hl0)).2 hle)
    hξ
  refine ⟨C, fun T N _ ψ hψ hψ1 herr => hC T N ψ hψ hψ1 ?_⟩
  rwa [norm_inner_normalizedMPVState_smul (pow_ne_zero N hζ) (hmpv N)]

/-- **Every slope below `ξ/4`.** Under the hypotheses of
`exists_log_le_of_infidelity_le_one_half_of_isNormal`, for every `0 < a < ξ/4` there is `C`,
independent of `N` and `T`, such that a unit vector `ψ` prepared in depth `T` with
`ε(φ_N, ψ) ≤ 1/2` satisfies `a log N ≤ T + C`.

This absorbs the correction `(ξ/4) log(T + 1)` into the slope, using
`log x ≤ l x - 1 - log l` for `x, l > 0`. It is the bound "any circuit faithfully preparing
them requires a depth `T=\Omega(\log N)`" of the introduction of arXiv:2307.01696, with every
slope below the `ξ/4` of the proof of Theorem 1. -/
theorem exists_mul_log_le_of_infidelity_le_one_half_of_isNormal {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {lam₁ lam₂ : ℂ}
    (hlam₁ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₁)
    (hlam₁max : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ ≤ ‖lam₁‖)
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ lam₁)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ lam₁ → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength (lam₂ / lam₁)) {a : ℝ} (ha : 0 < a)
    (haξ : a < correlationLength (lam₂ / lam₁) / 4) :
    ∃ C : ℝ, ∀ (T N : ℕ) [NeZero N] (ψ : Cfg d N → ℂ),
      IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 →
        1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ ≤
          1 / 2 →
          a * Real.log N ≤ T + C := by
  obtain ⟨C₀, hC₀⟩ := exists_log_le_of_infidelity_le_one_half_of_isNormal hA hlam₁ hlam₁max
    hlam₂ hlam₂1 hmax hξ
  set ξ' := correlationLength (lam₂ / lam₁) / 4 with hξ'_def
  have hξ' : 0 < ξ' := div_pos hξ (by norm_num)
  set θ : ℝ := a / ξ' with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg ha.le hξ'.le
  have hθ1 : θ < 1 := (div_lt_one hξ').2 haξ
  have hθξ : θ * ξ' = a := div_mul_cancel₀ a hξ'.ne'
  set l : ℝ := (1 - θ) / a with hl_def
  have hl : 0 < l := div_pos (by linarith) ha
  have hal : a * l = 1 - θ := mul_div_cancel₀ (1 - θ) ha.ne'
  refine ⟨(1 - θ) - a * (1 + Real.log l) + θ * C₀, fun T N _ ψ hψ hψ1 herr => ?_⟩
  have h := hC₀ T N ψ hψ hψ1 herr
  have h1 : a * Real.log N ≤ θ * T + a * Real.log ((T : ℝ) + 1) + θ * C₀ := by
    have h' := mul_le_mul_of_nonneg_left h hθ0
    have e1 : θ * (ξ' * Real.log N) = a * Real.log N := by rw [← mul_assoc, hθξ]
    have e2 : θ * (T + ξ' * Real.log ((T : ℝ) + 1) + C₀) =
        θ * T + a * Real.log ((T : ℝ) + 1) + θ * C₀ := by rw [← hθξ]; ring
    rw [e1, e2] at h'
    exact h'
  have h2 : a * Real.log ((T : ℝ) + 1) ≤ (1 - θ) * (T + 1) - a * (1 + Real.log l) := by
    have hT1 : (0 : ℝ) < T + 1 := by positivity
    /- The tangent-line bound `log x = log (l x) - log l ≤ l x - 1 - log l`. -/
    have ht : Real.log ((T : ℝ) + 1) ≤ l * (T + 1) - 1 - Real.log l := by
      have h := Real.log_le_sub_one_of_pos (mul_pos hl hT1)
      rw [Real.log_mul hl.ne' hT1.ne'] at h
      linarith
    calc a * Real.log ((T : ℝ) + 1) ≤ a * (l * (T + 1) - 1 - Real.log l) :=
          mul_le_mul_of_nonneg_left ht ha.le
      _ = a * l * (T + 1) - a * (1 + Real.log l) := by ring
      _ = _ := by rw [hal]
  linear_combination h1 + h2

/-- **Depth `Θ(log N)` at fixed error** (arXiv:2307.01696, Theorem 1 with eq. (1); the
introduction: "requires a depth `T=\Omega(\log N)`" and "an algorithm that saturates this
bound"). Let `A` be as in `exists_log_le_of_infidelity_le_one_half_of_isNormal` and fix
`0 < ε ≤ 1/2`. There are `a > 0`, `c`, `C` and `N₀`, independent of `N`, such that for every
`N ≥ N₀`:

* some unit vector `ψ` with `ε(ψ, φ_N) ≤ ε` is prepared from a product vector in depth at most
  `c log N` (eq. (1), `T = O(log(N/ε))`, at fixed `ε`);
* every unit vector `ψ` prepared in depth `T` with `ε(φ_N, ψ) ≤ ε` has `T ≥ a log N - C`
  (Theorem 1 with the constant of its proof).

Any slope `a < ξ/4` is admissible (`exists_mul_log_le_of_infidelity_le_one_half_of_isNormal`);
this statement takes `a = ξ/8`. -/
theorem exists_depth_isTheta_log {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {lam₁ lam₂ : ℂ}
    (hlam₁ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₁)
    (hlam₁max : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ ≤ ‖lam₁‖)
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ lam₁)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ lam₁ → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength (lam₂ / lam₁)) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ a c C : ℝ, ∃ N₀ : ℕ, 0 < a ∧ ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      (∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log N ∧
          IsPreparedInDepth T (fun s => ψ s) ∧ 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε) ∧
      ∀ (T : ℕ) (ψ : Cfg d N → ℂ), IsPreparedInDepth T ψ → star ψ ⬝ᵥ ψ = 1 →
        1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ ≤ ε →
          a * Real.log N - C ≤ T := by
  have : NeZero D := ⟨by
    rintro rfl
    obtain ⟨Y, hY⟩ := hlam₁.exists_hasEigenvector
    exact hY.2 (Subsingleton.elim Y 0)⟩
  set ξ := correlationLength (lam₂ / lam₁) with hξ_def
  obtain ⟨C, hC⟩ := exists_mul_log_le_of_infidelity_le_one_half_of_isNormal hA hlam₁
    hlam₁max hlam₂ hlam₂1 hmax hξ (a := ξ / 8) (by linarith) (by linarith)
  obtain ⟨c₀, N₀, hc₀⟩ := MPSPreparation.exists_isPreparedInDepth_le_log A hA
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨ξ / 8, |c₀| * (1 + Real.log ε⁻¹ / Real.log 2), C, max N₀ 2, by linarith,
    fun N _ hN => ⟨?_, fun T ψ hψ hψ1 herr => ?_⟩⟩
  · obtain ⟨ψ, T, hψ, hT, hprep, herr⟩ :=
      hc₀ ε hε (by linarith) N (le_of_max_le_left hN)
    refine ⟨ψ, T, hψ, ?_, hprep, herr⟩
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
    have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log two_pos hN2
    have hlε : 0 ≤ Real.log ε⁻¹ :=
      Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hε, by linarith⟩)
    have hsplit : Real.log (N / ε) = Real.log N + Real.log ε⁻¹ := by
      rw [div_eq_mul_inv, Real.log_mul (ne_of_gt (by linarith)) (inv_pos.mpr hε).ne']
    have hεN : Real.log ε⁻¹ ≤ Real.log ε⁻¹ / Real.log 2 * Real.log N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogN hlε
    have hpos : 0 ≤ Real.log (N / ε) := by rw [hsplit]; linarith
    calc (T : ℝ) ≤ c₀ * Real.log (N / ε) := hT
      _ ≤ |c₀| * Real.log (N / ε) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ |c₀| * ((1 + Real.log ε⁻¹ / Real.log 2) * Real.log N) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [hsplit]
          linarith
      _ = _ := by ring
  · have := hC T N ψ hψ hψ1 (herr.trans hε2)
    linarith

end MPSTensor
