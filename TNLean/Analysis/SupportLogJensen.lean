/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import TNLean.Algebra.PosSemidefSupport
import TNLean.Analysis.SpectralQuadraticForm

/-!
# Support-aware vector-state Jensen inequality for the matrix logarithm

For a positive semidefinite matrix $A$ and a unit vector $v$ in the support of $A$,
the scalar logarithm of the expectation of $A$ dominates the expectation of the
continuous-functional-calculus logarithm:

$$
  \operatorname{Re}\langle v, (\log A)v\rangle
    \le \log\bigl(\operatorname{Re}\langle v, Av\rangle\bigr).
$$

The support condition is essential. The continuous functional calculus uses the
totalized convention $\log 0=0$, whereas scalar concavity of the logarithm is used
only on $(0,\infty)$. In an eigenbasis of $A$, the support condition makes every
weight at a zero eigenvalue vanish. Jensen's inequality is therefore applied only
to the strictly positive eigenvalues.

## Main result

* `Matrix.PosSemidef.re_dotProduct_cfc_log_mulVec_le_log`: support-aware vector-state
  Jensen inequality for `CFC.log`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter V (vector-state Jensen inequalities).
-/

open scoped Matrix ComplexOrder BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace Matrix.PosSemidef

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Support-aware vector-state Jensen inequality for the logarithm.**

If $A$ is positive semidefinite, $v$ is a unit vector, and the support projection
of $A$ fixes $v$, then
$\operatorname{Re}\langle v,(\log A)v\rangle \le
\log(\operatorname{Re}\langle v,Av\rangle)$.

The support hypothesis removes the zero eigenspace before applying concavity of
`Real.log` on $(0,\infty)$; it cannot be omitted under the convention `Real.log 0 = 0`.
This is the finite-dimensional vector-state form of Jensen's inequality; see Bhatia,
*Matrix Analysis*, Chapter V. -/
theorem re_dotProduct_cfc_log_mulVec_le_log
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {v : n → ℂ}
    (hv : star v ⬝ᵥ v = (1 : ℂ))
    (hsupport : hA.supportProj *ᵥ v = v) :
    (star v ⬝ᵥ (CFC.log A *ᵥ v)).re ≤ Real.log (star v ⬝ᵥ (A *ᵥ v)).re := by
  classical
  let hH : A.IsHermitian := hA.isHermitian
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let μ : n → ℝ := hH.eigenvalues
  let w : n → ℂ := Uᴴ *ᵥ v
  let p : n → ℝ := hH.spectralWeight v
  let S : Finset n := Finset.univ.filter fun i => μ i ≠ 0
  have hUstarU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hsupportDiag :
      Matrix.diagonal (fun i => if μ i ≠ 0 then (1 : ℂ) else 0) *ᵥ w = w := by
    have hs := congrArg (fun x => Uᴴ *ᵥ x) hsupport
    change Uᴴ *ᵥ
        ((U * Matrix.diagonal (fun i => if μ i ≠ 0 then (1 : ℂ) else 0) * Uᴴ) *ᵥ v) =
      Uᴴ *ᵥ v at hs
    rw [Matrix.mulVec_mulVec] at hs
    rw [← Matrix.mul_assoc Uᴴ
        (U * Matrix.diagonal (fun i => if μ i ≠ 0 then (1 : ℂ) else 0)) Uᴴ,
      ← Matrix.mul_assoc Uᴴ U, hUstarU, Matrix.one_mul] at hs
    simpa only [w, ← Matrix.mulVec_mulVec] using hs
  have hwZero : ∀ i, μ i = 0 → w i = 0 := by
    intro i hi
    have hi' := congrFun hsupportDiag i
    simpa [Matrix.mulVec_diagonal, hi] using hi'.symm
  have hpZero : ∀ i, μ i = 0 → p i = 0 := by
    intro i hi
    simp [p, Matrix.IsHermitian.spectralWeight, U, w, hwZero i hi]
  have hpSum : (∑ i ∈ S, p i) = 1 := by
    rw [← hH.sum_spectralWeight hv]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hiS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hiS
    exact hpZero i hiS
  have sum_eq_sum_support (f : ℝ → ℝ) :
      (∑ i, p i * f (μ i)) = ∑ i ∈ S, p i * f (μ i) := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    intro i _ hiS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hiS
    rw [hpZero i hiS, zero_mul]
  have hAv : (star v ⬝ᵥ (A *ᵥ v)).re = ∑ i ∈ S, p i * μ i := by
    calc
      (star v ⬝ᵥ (A *ᵥ v)).re = ∑ i, p i * μ i := by
        simpa only [p, μ] using hH.re_dotProduct_mulVec_eq_sum v
      _ = ∑ i ∈ S, p i * μ i := by
        simpa only [id_eq] using sum_eq_sum_support id
  have hlogAv : (star v ⬝ᵥ (CFC.log A *ᵥ v)).re =
      ∑ i ∈ S, p i * Real.log (μ i) := by
    calc
      (star v ⬝ᵥ (CFC.log A *ᵥ v)).re =
          (star v ⬝ᵥ (hH.cfc Real.log *ᵥ v)).re := by
        rw [CFC.log, hH.cfc_eq]
      _ = ∑ i, p i * Real.log (μ i) := by
        simpa only [p, μ] using hH.re_dotProduct_cfc_mulVec_eq_sum Real.log v
      _ = ∑ i ∈ S, p i * Real.log (μ i) := sum_eq_sum_support Real.log
  have hμPos : ∀ i ∈ S, 0 < μ i := by
    intro i hi
    have hne : μ i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hne)
  have hpNonneg : ∀ i ∈ S, 0 ≤ p i := fun i _ => hH.spectralWeight_nonneg v i
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := S) (w := p) (p := μ) hpNonneg hpSum (fun i hi => hμPos i hi)
  simp only [smul_eq_mul] at hjensen
  rw [hlogAv, hAv]
  exact hjensen

end Matrix.PosSemidef
