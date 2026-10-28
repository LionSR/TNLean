/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.RelativeEntropyResolventIntegral
import QICLean.Channel.Schwarz.RelativeEntropyDataProcessing

/-!
# Lieb's trace-log-exponential concavity

For a fixed Hermitian matrix `H`, the map `A ↦ Re tr exp(H + log A)` is concave
on the positive-definite cone. The proof uses the joint convexity of the quantum
relative entropy already established in QICLean.

The library writes `D₀(X, Y) = Re tr (X (log X - log Y))`. The unnormalized
nonnegative divergence in the reference is `D₀(X, Y) - Re tr X + Re tr Y`.
The affine trace correction preserves joint convexity. Unnormalized Klein then
gives the variational formula for the trace, whose maximizing matrix is explicit.
Applying joint convexity at those maximizers proves the concavity theorem.

## References

* J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity
  theorem of Lieb* (2011), Fact 3, Lemma 6 and Theorem 1:
  https://tropp.caltech.edu/papers/Tro12-Joint-Convexity.pdf.

This is an analytic inequality. Matrix probability estimates and the sampled
operator construction in LVV are separate results.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace Matrix

/-- Unnormalized Klein inequality for positive-definite matrices. In the library's
trace-log convention, relative entropy is at least the difference of the traces.
This is Fact 3 of Tropp, *From joint convexity of quantum relative entropy to a
concavity theorem of Lieb* (2011), after separating the affine trace correction. -/
theorem trace_sub_le_quantumRelativeEntropy {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    A.trace.re - B.trace.re ≤ quantumRelativeEntropy A B := by
  classical
  let U := star hA.isHermitian.eigenvectorUnitary * hB.isHermitian.eigenvectorUnitary
  let P (i j : n) : ℝ := Complex.normSq ((U : Matrix n n ℂ) i j)
  have hrow (i : n) : ∑ j, P i j = 1 :=
    TNLean.Klein.row_sum_normSq_eq_one (Unitary.coe_mul_star_self U) i
  have hcol (j : n) : ∑ i, P i j = 1 :=
    TNLean.Klein.col_sum_normSq_eq_one (Unitary.coe_star_mul_self U) j
  have hscalar (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      a - b ≤ a * (Real.log a - Real.log b) := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos ha hb)) ha.le
    simpa only [Real.log_div ha.ne' hb.ne', inv_div, mul_sub, mul_one,
      mul_div_cancel₀ _ ha.ne'] using hh
  have htrace : A.trace.re - B.trace.re =
      ∑ i, ∑ j, (hA.isHermitian.eigenvalues i - hB.isHermitian.eigenvalues j) * P i j := by
    have hleft : (∑ i, ∑ j, hA.isHermitian.eigenvalues i * P i j) =
        ∑ i, hA.isHermitian.eigenvalues i := by simp_rw [← Finset.mul_sum, hrow, mul_one]
    have hright : (∑ i, ∑ j, hB.isHermitian.eigenvalues j * P i j) =
        ∑ j, hB.isHermitian.eigenvalues j := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hcol, mul_one]
    simp only [sub_mul, Finset.sum_sub_distrib, hleft, hright,
      hA.isHermitian.trace_eq_sum_eigenvalues, hB.isHermitian.trace_eq_sum_eigenvalues,
      Complex.re_sum]
    simp
  rw [htrace, quantumRelativeEntropy_posDef_spectral hA hB]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right (hscalar _ _ (hA.eigenvalues_pos i) (hB.eigenvalues_pos j))
      (Complex.normSq_nonneg _)

end Matrix

namespace Matrix

/-- The trace is the attained maximum of the positive-definite trace-log functional.
This is Tropp (2011), Lemma 6, *Variational Formula for Trace*. The maximum is attained
at the matrix whose trace is represented. -/
theorem isGreatest_trace_variational {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Matrix n n ℂ} (hY : Y.PosDef) :
    IsGreatest ((fun X : Matrix n n ℂ ↦
      (X * CFC.log Y).trace.re - (X * CFC.log X).trace.re + X.trace.re) ''
      {X | X.PosDef}) Y.trace.re := by
  constructor
  · exact ⟨Y, hY, by ring⟩
  · rintro r ⟨X, hX, rfl⟩
    have h := trace_sub_le_quantumRelativeEntropy hX hY
    rw [quantumRelativeEntropy_eq_trace_mul_log_sub] at h
    linarith

private theorem posDef_normedSpace_exp {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℂ} (hK : K.IsHermitian) : (NormedSpace.exp K).PosDef := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let hpsd : (NormedSpace.exp K).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hK.isSelfAdjoint.exp_nonneg
  exact hpsd.posDef_iff_isUnit.mpr (NormedSpace.isUnit_exp K)

private theorem trace_exp_variational_upper {n : Type*} [Fintype n] [DecidableEq n]
    {K X : Matrix n n ℂ} (hK : K.IsHermitian) (hX : X.PosDef) :
    (X * K).trace.re - (X * CFC.log X).trace.re + X.trace.re ≤
      (NormedSpace.exp K).trace.re := by
  have h := (isGreatest_trace_variational (posDef_normedSpace_exp hK)).2 ⟨X, hX, rfl⟩
  simpa only [CFC.log_exp K hK.isSelfAdjoint] using h

private theorem trace_exp_log_variational_upper {n : Type*} [Fintype n] [DecidableEq n]
    {H A X : Matrix n n ℂ} (hH : H.IsHermitian) (hX : X.PosDef) :
    (X * H).trace.re - quantumRelativeEntropy X A + X.trace.re ≤
      (NormedSpace.exp (H + CFC.log A)).trace.re := by
  have h := trace_exp_variational_upper (K := H + CFC.log A)
    (hH.add IsSelfAdjoint.log.isHermitian) hX
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub]
  linarith

private theorem quantumRelativeEntropy_exp_add_log {n : Type*} [Fintype n] [DecidableEq n]
    {H A : Matrix n n ℂ} (hH : H.IsHermitian) :
    quantumRelativeEntropy (NormedSpace.exp (H + CFC.log A)) A =
      (NormedSpace.exp (H + CFC.log A) * H).trace.re := by
  rw [quantumRelativeEntropy,
    CFC.log_exp _ (hH.add IsSelfAdjoint.log.isHermitian).isSelfAdjoint, add_sub_cancel_right]

end Matrix

namespace Matrix

/-- Lieb's trace-log-exponential concavity, with exactly the positive-definite domain.
For Hermitian `H`, the map `A ↦ Re tr exp(H + log A)` is concave. The proof follows
Tropp (2011), Theorem 1: apply joint convexity of the quantum relative entropy to the
attaining positive-definite matrices in the trace variational formula. -/
theorem concaveOn_trace_exp_add_log {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A ↦ (NormedSpace.exp (H + CFC.log A)).trace.re) := by
  constructor
  · intro A hA B hB a b ha hb hab
    exact PosDef.convex_comb ha hb hab hA hB
  · intro A₁ hA₁ A₂ hA₂ a b ha hb hab
    let X₁ := NormedSpace.exp (H + CFC.log A₁)
    let X₂ := NormedSpace.exp (H + CFC.log A₂)
    have hX₁ : X₁.PosDef := posDef_normedSpace_exp
      (hH.add (show (CFC.log A₁).IsHermitian from IsSelfAdjoint.log.isHermitian))
    have hX₂ : X₂.PosDef := posDef_normedSpace_exp
      (hH.add (show (CFC.log A₂).IsHermitian from IsSelfAdjoint.log.isHermitian))
    have hXm : (a • X₁ + b • X₂).PosDef := PosDef.convex_comb ha hb hab hX₁ hX₂
    have hcv := (TNLean.RelativeEntropyConvexity.convexOn_quantumRelativeEntropy_index
      (N := n)).2
      (show (X₁, A₁) ∈ _ from ⟨hX₁, hA₁⟩)
      (show (X₂, A₂) ∈ _ from ⟨hX₂, hA₂⟩) ha hb hab
    change quantumRelativeEntropy (a • X₁ + b • X₂) (a • A₁ + b • A₂) ≤
      a * quantumRelativeEntropy X₁ A₁ + b * quantumRelativeEntropy X₂ A₂ at hcv
    rw [quantumRelativeEntropy_exp_add_log hH, quantumRelativeEntropy_exp_add_log hH] at hcv
    have htrH : ((a • X₁ + b • X₂) * H).trace.re =
        a * (X₁ * H).trace.re + b * (X₂ * H).trace.re := by
      simp [Matrix.add_mul, Matrix.trace_smul]
    have htr : (a • X₁ + b • X₂).trace.re = a * X₁.trace.re + b * X₂.trace.re := by
      simp [Matrix.trace_smul]
    have hv := trace_exp_log_variational_upper (H := H) (A := a • A₁ + b • A₂) hH hXm
    rw [htrH, htr] at hv
    change a * X₁.trace.re + b * X₂.trace.re ≤ _
    linarith

end Matrix
