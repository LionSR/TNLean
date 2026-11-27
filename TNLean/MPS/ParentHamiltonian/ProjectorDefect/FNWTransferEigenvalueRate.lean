/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.FNWTransferDecay
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.FNWGeometricDefect
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Transfer-eigenvalue rates for the FNW estimate

Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`,
lines 2401--2412, permits any positive decay rate strictly exceeding the
moduli of the nonunit transfer eigenvalues. Removing the stationary
projection preserves every nonzero remainder eigenvalue as a nonunit
transfer eigenvalue. Thus this prescription implies the weighted
spectral-radius hypothesis of the FNW geometric estimate.

**Scope restriction (FNW prefactor):** the prefactor remains existential and
may depend on the chosen rate. No identification with the constant \(c=k^2\) in
the source's projector bound is made. The physical counterexample to the
source's fixed-threshold projector bound with \(c=k^2\), and the valid eventual
estimate with a prescribed prefactor, are recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

## Prescribed prefactors after an overlap threshold

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

section

open scoped ComplexOrder ENNReal NNReal

namespace MPSTensor

end MPSTensor

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {d D : ℕ}

/-- Every nonzero FNW remainder eigenvalue is a transfer eigenvalue.
This is the algebraic step in the rate prescription following `boundAm`
in Nachtergaele, Section 6, lines 2407--2412. -/
theorem fnwTransfer_hasEigenvalue_of_remainder [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) {ν : ℂ} (hν0 : ν ≠ 0)
    (hν : Module.End.HasEigenvalue
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) ν) :
    Module.End.HasEigenvalue (fnwTransferMap A) ν := by
  obtain ⟨X, hX⟩ := hν.exists_hasEigenvector
  have hzero : fnwLimitMap ρ hP.trace_ne_zero *
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) = 0 := by
    rw [mul_sub, fnwLimitMap_mul_fnwTransferMap A ρ hP.trace_ne_zero
      hP.fixedPoint_is_fixed, fnwLimitMap_mul_self, sub_self]
  have hPX : fnwLimitMap ρ hP.trace_ne_zero X = 0 := by
    apply (smul_eq_zero.mp
      (show ν • fnwLimitMap ρ hP.trace_ne_zero X = 0 from ?_)).resolve_left hν0
    simpa only [Module.End.mul_apply, hX.apply_eq_smul, _root_.map_smul, LinearMap.zero_apply]
      using LinearMap.congr_fun hzero X
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      simpa only [LinearMap.sub_apply, hPX, sub_zero] using hX.apply_eq_smul), hX.2⟩

/-- The transfer-eigenvalue prescription following Nachtergaele's `boundAm`
(Section 6, lines 2407--2412) implies the weighted remainder spectral-radius
bound. Eigenvalues are compared by modulus, and the rate is positive. -/
theorem fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) (rate : ℝ≥0)
    (hrate : 0 < rate)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) :
    fnwWeightedRemainderSpectralRadius ρ hρ A hP.trace_ne_zero < (rate : ℝ≥0∞) := by
  weighted_matrix_norm_instances ρ hρ
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro ν hν
  have hEig : Module.End.HasEigenvalue
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) ν :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr
      (by simpa only [AlgEquiv.spectrum_eq] using hν)
  by_cases hν0 : ν = 0
  · simpa only [hν0, nnnorm_zero] using hrate
  · have hν1 : ν ≠ 1 := fun h ↦
      (ne_of_lt (hP.fnwRemainder_eigenvalue_norm_lt_one ν hEig)) (by simp [h])
    exact_mod_cast hEigen ν (hP.fnwTransfer_hasEigenvalue_of_remainder hν0 hEig) hν1

/-- The transfer-eigenvalue condition following Nachtergaele's `boundAm`
(Section 6, lines 2407--2412) gives the FNW mixing estimate at that prescribed
rate, with a positive rate-dependent prefactor. The dimension-only constant
in the source projector estimate is not asserted. -/
theorem exists_fnwMixingQuantity_le_geometric_of_transfer_eigenvalues
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      fnwMixingQuantity ρ hρ A htr n ≤ C * (rate : ℝ) ^ n :=
  hP.exists_fnwMixingQuantity_le_geometric hρ htr rate
    (hP.fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues hρ rate hrate hEigen)

end Kraus.HasComplementaryFixedPointGap

end

section

open Filter
open scoped Topology ComplexOrder ENNReal NNReal

namespace MPSTensor

variable {d D : ℕ}

/-- Any positive prefactor bounds the FNW mixing quantity eventually at a
prescribed rate above every nonunit transfer eigenvalue modulus. This is the
version of Nachtergaele's `boundAm` with the rate-dependent onset specified
in the module's scope-restriction statement. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.eventually_fnwMixingQuantity_le_of_pos_prefactor
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
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
theorem _root_.Kraus.HasComplementaryFixedPointGap.eventually_projector_defect_le_of_pos_prefactor
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (rate : ℝ≥0) (hrate : 0 < rate) (hrate1 : rate < 1)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, c * (rate : ℝ) ^ m < 1 ∧ ∀ r ℓ : ℕ, 0 < ℓ →
      ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
            (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
          ((groundSpace A (r + m + ℓ)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection‖ ≤
        c * (rate : ℝ) ^ m * (1 + c * (rate : ℝ) ^ m) /
          (1 - c * (rate : ℝ) ^ m) := by
  obtain ⟨L, hL, hInj⟩ := isNormal_of_hasComplementaryFixedPointGap_with_posDef hP hρ
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

end
