/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Trace normalization of positive semidefinite matrices

This file gives a total trace normalization for a positive semidefinite matrix on a
nonempty finite-dimensional space.  When the trace vanishes, the normalized matrix is
chosen to be the maximally mixed state; the original matrix then vanishes.

## Main declarations

* `Matrix.normalizePosSemidef`: total trace normalization.
* `Matrix.normalizePosSemidef_posSemidef`: the normalized matrix is positive semidefinite.
* `Matrix.normalizePosSemidef_trace`: the normalized matrix has trace one.
* `Matrix.trace_re_smul_normalizePosSemidef`: multiplying by the original trace recovers
  the matrix.
* `Matrix.kronecker_eq_trace_re_mul_normalized`: normalization of two Kronecker factors.

This total normalization makes explicit the normalization implicit in HJPW,
arXiv:quant-ph/0304007v2, Appendix A, lines 857--858; the zero-trace branch is a local
total choice. CPSV, arXiv:1606.00608, Appendix C.2, lines 1614--1617, absorbs
nonzero scalar weights but does not specify TNLean's total zero-trace convention.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

/-- Normalize a positive semidefinite matrix by its trace, using the maximally mixed
state when the trace vanishes. -/
noncomputable def normalizePosSemidef
    {n : Type*} [Fintype n] (_x₀ : n) (M : Matrix n n ℂ) :
    Matrix n n ℂ := by
  classical
  exact if M.trace.re = 0 then
      ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ)
    else
      (((M.trace.re)⁻¹ : ℝ) : ℂ) • M

/-- Trace normalization preserves positive semidefiniteness. -/
theorem normalizePosSemidef_posSemidef
    {n : Type*} [Fintype n] (x₀ : n)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (normalizePosSemidef x₀ M).PosSemidef := by
  classical
  letI : Nonempty n := ⟨x₀⟩
  rw [normalizePosSemidef]
  split_ifs with htr
  · apply Matrix.PosSemidef.one.smul
      (a := ((Fintype.card n : ℂ)⁻¹))
    exact inv_nonneg_of_nonneg (by positivity : (0 : ℂ) ≤ Fintype.card n)
  · apply hM.smul
    exact_mod_cast inv_nonneg.mpr (Complex.nonneg_iff.mp hM.trace_nonneg).1

/-- The total normalization has trace one. -/
theorem normalizePosSemidef_trace
    {n : Type*} [Fintype n] (x₀ : n)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (normalizePosSemidef x₀ M).trace = 1 := by
  classical
  letI : Nonempty n := ⟨x₀⟩
  have htrace : M.trace = (M.trace.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm
  rw [normalizePosSemidef]
  split_ifs with htr
  · rw [Matrix.trace_smul, Matrix.trace_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · rw [Matrix.trace_smul, htrace]
    change ((M.trace.re⁻¹ : ℝ) : ℂ) * (M.trace.re : ℂ) = 1
    exact_mod_cast inv_mul_cancel₀ htr

/-- Multiplying the normalized matrix by the real part of the original trace recovers
the positive semidefinite matrix. -/
theorem trace_re_smul_normalizePosSemidef
    {n : Type*} [Fintype n] (x₀ : n)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (M.trace.re : ℂ) • normalizePosSemidef x₀ M = M := by
  classical
  letI : Nonempty n := ⟨x₀⟩
  have htrace : M.trace = (M.trace.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm
  rw [normalizePosSemidef]
  split_ifs with htr
  · have htrace0 : M.trace = 0 := by
      rw [htrace, htr]
      exact Complex.ofReal_zero
    have hM0 : M = 0 := hM.trace_eq_zero_iff.mp htrace0
    rw [hM0]
    simp
  · rw [smul_smul]
    rw [← Complex.ofReal_mul]
    rw [mul_inv_cancel₀ htr]
    simp

/-- A Kronecker product of positive semidefinite matrices separates into the product
of their traces and their normalized factors. -/
theorem kronecker_eq_trace_re_mul_normalized
    {m n : Type*} [Fintype m] [Fintype n] (x₀ : m) (y₀ : n)
    {L : Matrix m m ℂ} {R : Matrix n n ℂ}
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    L ⊗ₖ R =
      ((L.trace.re * R.trace.re : ℝ) : ℂ) •
        (normalizePosSemidef x₀ L ⊗ₖ normalizePosSemidef y₀ R) := by
  ext ⟨xL, xR⟩ ⟨yL, yR⟩
  have hLe := congrFun (congrFun
    (trace_re_smul_normalizePosSemidef x₀ hL) xL) yL
  have hRe := congrFun (congrFun
    (trace_re_smul_normalizePosSemidef y₀ hR) xR) yR
  simp only [smul_apply] at hLe hRe
  simp only [Matrix.kroneckerMap_apply, smul_apply]
  rw [← hLe, ← hRe]
  push_cast
  ring

end Matrix
