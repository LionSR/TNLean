/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWTransferEigenvalueRate
import TNLean.MPS.ParentHamiltonian.FNWGeometricDefect
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Prescribed prefactors after an overlap threshold

A decay rate strictly above all nonunit transfer eigenvalue moduli permits
any prescribed positive prefactor after a sufficiently large overlap.
An intermediate rate absorbs the original geometric constant.

**Scope restriction (rate-dependent onset):** the prefactor assertion following
Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`, lines
2401--2412, is proved here with an additional onset depending on the state,
rate, and prescribed prefactor. This is not a bound from the injectivity
threshold alone. The distinction is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.
-/

open Filter
open scoped Topology ComplexOrder ENNReal NNReal

namespace MPSTensor

variable {d D : ℕ}

/-- Any positive prefactor bounds the FNW mixing quantity eventually at a
prescribed rate above every nonunit transfer eigenvalue modulus. This is the
version of Nachtergaele's `boundAm` with the rate-dependent onset specified
in the module's scope-restriction statement. -/
theorem IsPrimitiveMPS.eventually_fnwMixingQuantity_le_of_pos_prefactor
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, fnwMixingQuantity ρ hρ A htr n ≤ c * (rate : ℝ) ^ n := by
  obtain ⟨μ, hμ, hμrate⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (hP.fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues hρ rate hrate hEigen)
  obtain ⟨C, hC, hbound⟩ :=
    hP.exists_fnwMixingQuantity_le_geometric hρ htr μ hμ
  have hsmall := (isLittleO_pow_pow_of_lt_left μ.coe_nonneg
    (show (μ : ℝ) < (rate : ℝ) by exact_mod_cast hμrate)).bound (div_pos hc hC)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn' : (μ : ℝ) ^ n ≤ c / C * (rate : ℝ) ^ n := by
    simpa only [Real.norm_of_nonneg (pow_nonneg μ.coe_nonneg n),
      Real.norm_of_nonneg (pow_nonneg rate.coe_nonneg n)] using hn
  calc
    fnwMixingQuantity ρ hρ A htr n ≤ C * (μ : ℝ) ^ n := hbound n hn1
    _ ≤ C * (c / C * (rate : ℝ) ^ n) := mul_le_mul_of_nonneg_left hn' hC.le
    _ = c * (rate : ℝ) ^ n := by field_simp

/-- The physical projector estimate with any prescribed positive prefactor
holds beyond a state- and rate-dependent overlap threshold. This is the
corrected eventual form of Nachtergaele, Section 6, equation `boundAm`.
The bound is uniform in the prefix and every positive suffix length. -/
theorem IsPrimitiveMPS.eventually_projector_defect_le_of_pos_prefactor
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (rate : ℝ≥0) (hrate : 0 < rate) (hrate1 : rate < 1)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, c * (rate : ℝ) ^ m < 1 ∧ ∀ r ℓ : ℕ, 0 < ℓ →
      ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
            (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
          (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
        c * (rate : ℝ) ^ m * (1 + c * (rate : ℝ) ^ m) /
          (1 - c * (rate : ℝ) ^ m) := by
  obtain ⟨L, hL, hInj⟩ := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  have hdecay : Tendsto (fun m : ℕ ↦ c * (rate : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one rate.coe_nonneg
        (show (rate : ℝ) < 1 by exact_mod_cast hrate1))
  filter_upwards [hP.eventually_fnwMixingQuantity_le_of_pos_prefactor
    hρ htr rate hrate hEigen hc, eventually_ge_atTop L,
    hdecay.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
    with m hmix hLm hsmall
  exact ⟨hsmall, fun r ℓ hℓ ↦
    wholeIncrement_groundProjection_defect_le_fnw_geometric ρ hρ htr A hP.norm
      hP.fixedPoint_is_fixed hInj hL hLm hmix hsmall r ℓ hℓ⟩

end MPSTensor
