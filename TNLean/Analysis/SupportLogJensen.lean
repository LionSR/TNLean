/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import TNLean.Algebra.PosSemidefSupport
import TNLean.Analysis.TraceCFC

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

* `Matrix.PosSemidef.re_dotProduct_cfcLog_mulVec_le_log`: support-aware vector-state
  Jensen inequality for `CFC.log`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter V (vector-state Jensen inequalities).
-/

open scoped Matrix ComplexOrder BigOperators Matrix.Norms.L2Operator
open Finset Matrix

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
theorem re_dotProduct_cfcLog_mulVec_le_log
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {v : n → ℂ}
    (hv : star v ⬝ᵥ v = (1 : ℂ))
    (hsupport : hA.supportProj *ᵥ v = v) :
    (star v ⬝ᵥ (CFC.log A *ᵥ v)).re ≤ Real.log (star v ⬝ᵥ (A *ᵥ v)).re := by
  classical
  let hH : A.IsHermitian := hA.isHermitian
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let μ : n → ℝ := hH.eigenvalues
  let w : n → ℂ := Uᴴ *ᵥ v
  let p : n → ℝ := fun i => Complex.normSq (w i)
  let S : Finset n := Finset.univ.filter fun i => μ i ≠ 0
  have hUstarU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUUstar : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.prop
  have hQ : ∀ g : n → ℂ,
      star v ⬝ᵥ ((U * Matrix.diagonal g * Uᴴ) *ᵥ v) =
        ∑ i, g i * (star (w i) * w i) := by
    intro g
    have hvU : star v ᵥ* U = star w := by
      change star v ᵥ* U = star (Uᴴ *ᵥ v)
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    have hmul :
        (U * Matrix.diagonal g * Uᴴ) *ᵥ v =
          U *ᵥ (Matrix.diagonal g *ᵥ (Uᴴ *ᵥ v)) := by
      rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hmul, Matrix.dotProduct_mulVec, hvU]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnormSq : ∀ i, star (w i) * w i = ((p i : ℝ) : ℂ) := by
    intro i
    simpa [p, Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w i)).symm
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
    simp [p, hwZero i hi]
  have hpSum : (∑ i ∈ S, p i) = 1 := by
    have hstarw : star w = star v ᵥ* U := by
      change star (Uᴴ *ᵥ v) = star v ᵥ* U
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    have hww : star w ⬝ᵥ w = (1 : ℂ) := by
      rw [hstarw]
      calc
        (star v ᵥ* U) ⬝ᵥ w = star v ⬝ᵥ (U *ᵥ w) := by
          rw [← Matrix.dotProduct_mulVec]
        _ = star v ⬝ᵥ ((U * Uᴴ) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec]
        _ = star v ⬝ᵥ v := by rw [hUUstar, Matrix.one_mulVec]
        _ = 1 := hv
    have hall : ∑ i, p i = 1 := by
      have hc : (∑ i, ((p i : ℝ) : ℂ)) = (1 : ℂ) := by
        rw [← hww]
        simp only [dotProduct, Pi.star_apply]
        exact Finset.sum_congr rfl fun i _ => (hnormSq i).symm
      exact_mod_cast hc
    rw [← hall]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hiS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hiS
    exact hpZero i hiS
  have hASpec : A = U * Matrix.diagonal (fun i => ((μ i : ℂ))) * Uᴴ := by
    simpa [hH, U, μ, Matrix.star_eq_conjTranspose] using hH.spectral_form
  have hlogSpec : CFC.log A =
      U * Matrix.diagonal (fun i => ((Real.log (μ i) : ℂ))) * Uᴴ := by
    rw [CFC.log, hH.cfc_eq]
    simpa [hH, U, μ, Matrix.star_eq_conjTranspose] using hH.cfc_form Real.log
  have hAv : (star v ⬝ᵥ (A *ᵥ v)).re = ∑ i ∈ S, p i * μ i := by
    rw [hASpec, hQ, Complex.re_sum]
    simp only [hnormSq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hiS
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hiS
      simp [hiS]
  have hlogAv : (star v ⬝ᵥ (CFC.log A *ᵥ v)).re =
      ∑ i ∈ S, p i * Real.log (μ i) := by
    rw [hlogSpec, hQ, Complex.re_sum]
    simp only [hnormSq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hiS
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hiS
      simp [hiS]
  have hμPos : ∀ i ∈ S, 0 < μ i := by
    intro i hi
    have hne : μ i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hne)
  have hpNonneg : ∀ i ∈ S, 0 ≤ p i := fun i _ => Complex.normSq_nonneg _
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := S) (w := p) (p := μ) hpNonneg hpSum (fun i hi => hμPos i hi)
  simp only [smul_eq_mul] at hjensen
  rw [hlogAv, hAv]
  exact hjensen

end Matrix.PosSemidef
