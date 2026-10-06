/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLowerBound
import TNLean.MPS.Preparation.NormalGauge

/-!
# No preparation of a normal matrix product state in depth `o(log N)`, for every normal tensor

arXiv:2307.01696, Theorem 1 (label `th:1`: "If `T=o(log N)` there is some `N_0` such that for all
`N>N_0` we have `ε > 1/2`"), for `φ_N` generated "by a normal tensor `A`, with finite correlation
length `ξ>0`" and `ψ_N` "obtained from depth-`T` local quantum circuits applied to product
states". The gauge-form theorem `eventually_one_half_lt_infidelity_of_isLittleO_log` assumes the
gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1` of the source's eq. (5); here that
gauge is reached from an arbitrary normal tensor (`NormalGauge.lean`), which leaves the
normalized vectors `φ_N/‖φ_N‖` and the correlation length unchanged.

* `eventually_one_half_lt_infidelity_of_isNormalTensor`: the theorem for a normal tensor in the
  source's sense (irreducible, `E_A` with the unique largest eigenvalue `λ₁ = 1`), with
  `ξ = -1/ln|λ₂|` for the subleading eigenvalue `λ₂` of `E_A`.
* `eventually_one_half_lt_infidelity_of_isNormal`: the theorem for a tensor some blocking of which
  is injective (the chapter's `def:normal`), with no normalization of the leading eigenvalue
  `λ₁`; the correlation length is `ξ = -1/ln|λ₂/λ₁|`.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter Asymptotics

namespace MPSTensor

variable {d D : ℕ}

/-- **No preparation in depth `o(log N)`** (arXiv:2307.01696, Theorem 1). Let `A` be normal in
the source's sense: irreducible, with `E_A` having "a unique largest eigenvalue `λ_1 = 1` and no
other of the same magnitude" (the definition after eq. (4); `IsNormalTensor`). Let `λ₂` be an
eigenvalue of `E_A` of largest modulus among those different from `1`, with correlation length
`ξ = -1/ln|λ₂| > 0`. If unit vectors `ψ_N` are prepared from product vectors by local circuits
of depth `T_N = o(log N)`, then `ε(φ_N, ψ_N) = 1 - |⟨φ_N|ψ_N⟩| > 1/2` for all sufficiently
large `N`.

The proof passes to the gauge of the source's eq. (5) ("After a gauge transformation"), which
leaves the normalized vectors `φ_N` and the eigenvalues of `E_A` unchanged, and applies the
gauge form `eventually_one_half_lt_infidelity_of_isLittleO_log`. -/
theorem eventually_one_half_lt_infidelity_of_isNormalTensor {A : MPSTensor d D}
    (hA : IsNormalTensor A) {lam₂ : ℂ}
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ 1)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) {T : ℕ → ℕ}
    (hT : (fun N ↦ (T N : ℝ)) =o[atTop] fun N ↦ Real.log N) (ψ : ∀ N, Cfg d N → ℂ)
    (hψ : ∀ (N : ℕ) [NeZero N], MPSPreparation.IsPreparedInDepth (T N) (ψ N))
    (hψ1 : ∀ N, star (ψ N) ⬝ᵥ ψ N = 1) :
    ∀ᶠ N in atTop, 1 / 2 <
      1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 (ψ N) : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ := by
  obtain ⟨B, L, ρ, hG, hL1, hL, hTP, hρ, hfix, htr⟩ := hA.exists_normalGauge
  have heig := hasEigenvalue_transferMap_iff_of_gaugeEquiv hG
  have h := eventually_one_half_lt_infidelity_of_isLittleO_log hL1 hL hTP hρ hfix htr
    ((heig lam₂).1 hlam₂) hlam₂1 (fun μ hμ hμ1 => hmax μ ((heig μ).2 hμ) hμ1) hξ hT ψ hψ hψ1
  simpa only [normalizedMPVState_eq_of_gaugeEquiv hG] using h

/-- **No preparation in depth `o(log N)`, for a tensor normal by block injectivity**
(arXiv:2307.01696, Theorem 1). Let the products of some fixed number of matrices of `A` span the
matrix algebra (`Kraus.IsNormal`, the chapter's `def:normal`), let `λ₁` be an eigenvalue of `E_A`
of largest modulus, and let `λ₂` be an eigenvalue of largest modulus among those different from
`λ₁`, with correlation length `ξ = -1/ln|λ₂/λ₁| > 0`. If unit vectors `ψ_N` are prepared from
product vectors by local circuits of depth `T_N = o(log N)`, then `ε(φ_N, ψ_N) > 1/2` for all
sufficiently large `N`.

The source normalizes "`λ_1 = 1`" in its definition of a normal tensor; here the normalization
is part of the proof. Rescaling `A` by `λ₁^{-1/2}` and gauging as before the source's eq. (5)
(`exists_normalGauge_of_isNormal`) multiplies `φ_N` by a nonzero constant and divides the
eigenvalues of `E_A` by `λ₁`. -/
theorem eventually_one_half_lt_infidelity_of_isNormal {A : MPSTensor d D} (hA : Kraus.IsNormal A)
    {lam₁ lam₂ : ℂ} (hlam₁ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₁)
    (hlam₁max : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ ≤ ‖lam₁‖)
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ lam₁)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ lam₁ → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength (lam₂ / lam₁)) {T : ℕ → ℕ}
    (hT : (fun N ↦ (T N : ℝ)) =o[atTop] fun N ↦ Real.log N) (ψ : ∀ N, Cfg d N → ℂ)
    (hψ : ∀ (N : ℕ) [NeZero N], MPSPreparation.IsPreparedInDepth (T N) (ψ N))
    (hψ1 : ∀ N, star (ψ N) ⬝ᵥ ψ N = 1) :
    ∀ᶠ N in atTop, 1 / 2 <
      1 - ‖⟪normalizedMPVState A N, (WithLp.toLp 2 (ψ N) : EuclideanSpace ℂ (Cfg d N))⟫_ℂ‖ := by
  obtain ⟨hl0, B, ζ, L, ρ, hζ, -, hL1, hL, hTP, hρ, hfix, htr, heig, hmpv⟩ :=
    exists_normalGauge_of_isNormal hA hlam₁ hlam₁max
  /- Every eigenvalue of `E_B` is `μ/λ₁` for an eigenvalue `μ` of `E_A`. -/
  have hback : ∀ ν, Module.End.HasEigenvalue (Kraus.transferMap B) ν →
      Module.End.HasEigenvalue (Kraus.transferMap A) (ν * lam₁) := fun ν hν =>
    (heig _).2 (by rwa [mul_div_cancel_right₀ _ hl0])
  have h := eventually_one_half_lt_infidelity_of_isLittleO_log hL1 hL hTP hρ hfix htr
    ((heig lam₂).1 hlam₂) (fun h1 => hlam₂1 ((div_eq_one_iff_eq hl0).1 h1))
    (fun ν hν hν1 => by
      have hle := hmax _ (hback ν hν) fun h1 =>
        hν1 (mul_right_cancel₀ hl0 (h1.trans (one_mul _).symm))
      rw [norm_div]
      rw [norm_mul] at hle
      exact (le_div_iff₀ (norm_pos_iff.mpr hl0)).2 hle)
    hξ hT ψ hψ hψ1
  filter_upwards [h] with N hN
  rwa [norm_inner_normalizedMPVState_smul (pow_ne_zero N hζ) (hmpv N)] at hN

end MPSTensor
