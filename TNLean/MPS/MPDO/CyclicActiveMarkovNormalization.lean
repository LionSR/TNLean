/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveFourthRegion

/-!
# Positive normalization for cyclic-active Markov blocks

This file collects the finite Kronecker-positivity and trace-normalization
lemmas used to turn the left and right cut factors into density matrices.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

/-- Normalize a positive semidefinite matrix by its trace, using the maximally
mixed state when the trace vanishes.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This total normalization is applied
to the positive path factors of the restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def normalizePosSemidef
    {n : Type*} [Fintype n] (_x₀ : n) (M : Matrix n n ℂ) :
    Matrix n n ℂ := by
  classical
  exact if M.trace.re = 0 then
      ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ)
    else
      (((M.trace.re)⁻¹ : ℝ) : ℂ) • M

/-- Trace normalization preserves positive semidefiniteness.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This positivity statement is used
for the normalized path factors of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
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

/-- The total normalization has trace one.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This trace identity is used for the
normalized path factors of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
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

/-- Multiplying the normalized matrix by the real part of the original trace
recovers a positive semidefinite matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This identity recovers the
unnormalized path factors of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
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

/-- A Kronecker product of positive semidefinite matrices separates into the
product of their traces and their normalized factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This identity normalizes the two
positive path factors obtained from the restricted coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
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
