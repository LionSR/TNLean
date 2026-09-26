/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWTransferDecay

/-!
# Transfer-eigenvalue rates for the FNW estimate

Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`,
lines 2401--2412, permits any positive decay rate strictly exceeding the
moduli of the nonunit transfer eigenvalues. Removing the stationary
projection preserves every nonzero remainder eigenvalue as a nonunit
transfer eigenvalue. Thus this prescription implies the weighted
spectral-radius hypothesis of the FNW geometric estimate.

The prefactor remains existential and may depend on the chosen rate. No
identification with the constant \(c=k^2\) in the source's projector bound is made;
that separate question is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.
-/

open scoped ComplexOrder ENNReal NNReal

namespace MPSTensor

variable {d D : ℕ}

/-- Every nonzero FNW remainder eigenvalue is a transfer eigenvalue.
This is the algebraic step in the rate prescription following `boundAm`
in Nachtergaele, Section 6, lines 2407--2412. -/
theorem IsPrimitiveMPS.fnwTransfer_hasEigenvalue_of_remainder [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) {ν : ℂ} (hν0 : ν ≠ 0)
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
    simpa only [Module.End.mul_apply, hX.apply_eq_smul, map_smul, LinearMap.zero_apply]
      using LinearMap.congr_fun hzero X
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      simpa only [LinearMap.sub_apply, hPX, sub_zero] using hX.apply_eq_smul), hX.2⟩

/-- The transfer-eigenvalue prescription following Nachtergaele's `boundAm`
(Section 6, lines 2407--2412) implies the weighted remainder spectral-radius
bound. Eigenvalues are compared by modulus, and the rate is positive. -/
theorem IsPrimitiveMPS.fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) (rate : ℝ≥0) (hrate : 0 < rate)
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
theorem IsPrimitiveMPS.exists_fnwMixingQuantity_le_geometric_of_transfer_eigenvalues
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (hEigen : ∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν →
      ν ≠ 1 → ‖ν‖ < (rate : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      fnwMixingQuantity ρ hρ A htr n ≤ C * (rate : ℝ) ^ n :=
  hP.exists_fnwMixingQuantity_le_geometric hρ htr rate
    (hP.fnwWeightedRemainderSpectralRadius_lt_of_transfer_eigenvalues hρ rate hrate hEigen)

end MPSTensor
