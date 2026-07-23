/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.KleinInequality
import TNLean.Analysis.SuperoperatorResolvent
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Resolvent integral representations of relative entropy

This file proves the scalar logarithmic integral and the finite-dimensional
spectral identities needed for resolvent representations of quantum relative
entropy. It includes the homogeneous Hermitian trace-log identity and the
coordinate-free resolvent formula for positive-definite matrices.

## Main results

* `relativeEntropyScalar_integrableOn` and `integral_relativeEntropyScalar`
  give the coefficient-correct scalar improper integral.
* `sourceA_resolvent_quadratic_spectral` and
  `sourceB_resolvent_quadratic_spectral` identify the two resolvent quadratic
  forms in eigenvalue coordinates.
* `quantumRelativeEntropy_resolvent_integral` gives the positive-definite
  matrix integral representation.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §4 and Appendix.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

/-- The scalar integrand in the (p=1) Jenčová--Ruskai representation:
\[
 \frac{a^2/(a+tb)-b+t b^2/(a+tb)}{1+t}.
\]
The coefficient `t` in the last term is essential.

This is the scalar normalization `(intspec)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 406--413. -/
noncomputable def relativeEntropyScalar (a b t : ℝ) : ℝ :=
  (a ^ 2 / (a + t * b) - b + t * b ^ 2 / (a + t * b)) / (1 + t)

private theorem relativeEntropyScalar_integrable_and_integral
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (relativeEntropyScalar a b) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, relativeEntropyScalar a b t =
        a * (Real.log a - Real.log b) := by
  let f : ℝ → ℝ := relativeEntropyScalar a b
  let F : ℝ → ℝ := fun t =>
    a * (Real.log (1 + t) - Real.log (a + t * b))
  have hf_form (t : ℝ) (h₁ : 1 + t ≠ 0) (h₂ : a + t * b ≠ 0) :
      f t = a * (a - b) / ((a + t * b) * (1 + t)) := by
    simp only [f, relativeEntropyScalar]
    field_simp
    ring
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (f t) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have h1 : 1 + t ≠ 0 := by positivity
    have hab : a + t * b ≠ 0 := by positivity
    have hlog1 : HasDerivAt
        (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
      simpa [one_div] using ((hasDerivAt_id t).const_add 1).log h1
    have hlogab : HasDerivAt
        (fun x : ℝ => Real.log (a + x * b)) (b / (a + t * b)) t := by
      simpa [one_div, mul_comm] using
        ((hasDerivAt_id t).mul_const b |>.const_add a).log hab
    have h := (hlog1.sub hlogab).const_mul a
    have hvalue : a * (1 / (1 + t) - b / (a + t * b)) = f t := by
      rw [hf_form t h1 hab]
      field_simp
      ring
    rw [show F = fun y => a *
      ((fun x : ℝ => Real.log (1 + x)) y - Real.log (a + y * b)) from rfl]
    exact h.congr_deriv hvalue
  have hratio : Tendsto
      (fun t : ℝ => (1 + t) / (a + t * b)) atTop (𝓝 (1 / b)) := by
    have hzero : Tendsto (fun t : ℝ => (1 : ℝ) / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have ha0 : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hnum := hzero.add (tendsto_const_nhds (x := (1 : ℝ)))
    have hden := ha0.add (tendsto_const_nhds (x := b))
    have h : Tendsto (fun t : ℝ => (1 / t + 1) / (a / t + b)) atTop
        (𝓝 ((0 + 1) / (0 + b))) :=
      hnum.div hden (by simpa using hb.ne')
    have heq : (fun t : ℝ => (1 + t) / (a + t * b)) =ᶠ[atTop]
        fun t => (1 / t + 1) / (a / t + b) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      field_simp
    simpa only [zero_add] using h.congr' heq.symm
  have hF : Tendsto F atTop (𝓝 (-a * Real.log b)) := by
    have hinvb : (1 / b) ≠ 0 := one_div_ne_zero hb.ne'
    have hlog := (Real.continuousAt_log hinvb).tendsto.comp hratio
    have hmul := (tendsto_const_nhds (x := a)).mul hlog
    have heq : F =ᶠ[atTop]
        fun t => a * Real.log ((1 + t) / (a + t * b)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [F]
      rw [Real.log_div (by positivity) (by positivity)]
    have hmul' := hmul.congr' heq.symm
    rw [show -a * Real.log b = a * (-Real.log b) by ring]
    simpa only [Function.comp_apply, one_div, Real.log_inv] using hmul'
  have hfint : IntegrableOn f (Ioi 0) := by
    by_cases hab : b ≤ a
    · exact integrableOn_Ioi_deriv_of_nonneg' hderiv
        (fun t ht => by
          have ht0 : 0 ≤ t := ht.le
          have hden1 : 0 < 1 + t := by positivity
          have hdenab : 0 < a + t * b := by positivity
          rw [hf_form t hden1.ne' hdenab.ne']
          exact div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hab))
            (mul_nonneg hdenab.le hden1.le))
        hF
    · have hderivNeg : ∀ t ∈ Ici (0 : ℝ),
          HasDerivAt (fun x => -F x) (-f t) t :=
        fun t ht => (hderiv t ht).neg
      have hFneg : Tendsto (fun x => -F x) atTop
          (𝓝 (-(-a * Real.log b))) := hF.neg
      have hnegint : IntegrableOn (fun t => -f t) (Ioi 0) :=
        integrableOn_Ioi_deriv_of_nonneg' hderivNeg
          (fun t ht => by
            have ht0 : 0 ≤ t := ht.le
            have hden1 : 0 < 1 + t := by positivity
            have hdenab : 0 < a + t * b := by positivity
            rw [hf_form t hden1.ne' hdenab.ne', neg_nonneg]
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos ha.le
                (sub_nonpos.mpr (le_of_not_ge hab)))
              (mul_nonneg hdenab.le hden1.le))
          hFneg
      refine hnegint.neg.congr_fun ?_ measurableSet_Ioi
      intro t _
      change -(-f t) = f t
      ring
  refine ⟨hfint, ?_⟩
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hfint hF
  calc
    ∫ t : ℝ in Ioi 0, relativeEntropyScalar a b t =
        -a * Real.log b - a *
          (Real.log (1 + 0) - Real.log (a + 0 * b)) := by
      simpa only [F, f] using hint
    _ = a * (Real.log a - Real.log b) := by
      norm_num
      ring

/-- The scalar (p=1) relative-entropy resolvent integrand is integrable on
the positive half-line for positive `a` and `b`.

This is the integrability part of `(intspec)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 406--413. -/
theorem relativeEntropyScalar_integrableOn {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (relativeEntropyScalar a b) (Ioi 0) :=
  (relativeEntropyScalar_integrable_and_integral ha hb).1

/-- For positive `a` and `b`,
\[
 a(\log a-\log b)=\int_0^\infty
 \frac{a^2/(a+tb)-b+t b^2/(a+tb)}{1+t}\,dt.
\]

This is the scalar normalization `(intspec)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 406--413.
-/
theorem integral_relativeEntropyScalar {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ t : ℝ in Ioi 0, relativeEntropyScalar a b t =
      a * (Real.log a - Real.log b) :=
  (relativeEntropyScalar_integrable_and_integral ha hb).2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic resolvent form with source `A` for the positive left-right
operator `X ↦ A * X + t • (X * B)`. -/
noncomputable def sourceAResolventQuadratic (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  let S := A ⊗ₖ (1 : Matrix n n ℂ) +
    t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
  (star (vec Aᵀ) ⬝ᵥ (S⁻¹ *ᵥ vec Aᵀ)).re

/-- The quadratic resolvent form with source `B` for the positive left-right
operator `X ↦ A * X + t • (X * B)`. -/
noncomputable def sourceBResolventQuadratic (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  let S := A ⊗ₖ (1 : Matrix n n ℂ) +
    t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
  (star (vec Bᵀ) ⬝ᵥ (S⁻¹ *ᵥ vec Bᵀ)).re

/-- Under `X ↦ vec Xᵀ`, the Kronecker left-right matrix represents
`X ↦ A * X + t • (X * B)`. -/
theorem leftRight_mulVec_vec_transpose (A B X : Matrix n n ℂ) (t : ℝ) :
    (A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ =
      vec (A * X + t • (X * B))ᵀ := by
  rw [add_mulVec, smul_mulVec, kronecker_mulVec_vec,
    kronecker_mulVec_vec]
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one,
    ← vec_add, ← vec_smul, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.transpose_mul]

private lemma spectral_sourceA_solution {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      (α i / (α i + t * β j) : ℂ) * W i j
    let X := UA * Y * star UB
    A * X + t • (X * B) = A := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (α i / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  have hα (i : n) : 0 < α i := hA.eigenvalues_pos i
  have hβ (j : n) : 0 < β j := hB.eigenvalues_pos j
  have hcore : Dα * Y + t • (Y * Dβ) = Dα * W := by
    ext i j
    simp only [Dα, Dβ, Y, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    have hden : (α i : ℂ) + t * β j ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (add_pos (hα i) (mul_pos ht (hβ j))))
    field_simp
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUAstar : UA * star UA = 1 := by
    simpa only [UA] using
      Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.prop
  have hUBstar : UB * star UB = 1 := by
    simpa only [UB] using
      Unitary.mul_star_self_of_mem hB.isHermitian.eigenvectorUnitary.prop
  have hstarUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  calc
    A * X + t • (X * B) =
        (UA * Dα * star UA) * X +
          t • (X * (UB * Dβ * star UB)) := by rw [hAform, hBform]
    _ = UA * Dα * star UA := by
      simp only [X, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul,
        ← Matrix.mul_assoc (star UB) UB, hstarUB, Matrix.one_mul]
      rw [show UA * (Dα * (Y * star UB)) +
          t • (UA * (Y * (Dβ * star UB))) =
          UA * (Dα * Y + t • (Y * Dβ)) * star UB by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
          Matrix.mul_smul, Matrix.smul_mul], hcore]
      simp only [W, Matrix.mul_assoc]
      rw [hUBstar, Matrix.mul_one]
    _ = A := hAform.symm

private lemma spectral_sourceA_pairing {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (_ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      (α i / (α i + t * β j) : ℂ) * W i j
    let X := UA * Y * star UB
    (star (vec Aᵀ) ⬝ᵥ vec Xᵀ).re =
      ∑ i, ∑ j, α i ^ 2 / (α i + t * β j) *
        Complex.normSq (W i j) := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (α i / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hstarW : star W = star UB * UA := by
    simp only [W, star_mul, star_star]
  have hpair : star (vec Aᵀ) ⬝ᵥ vec Xᵀ = Matrix.trace (A * X) := by
    rw [Matrix.star_vec_dotProduct_vec]
    rw [hA.isHermitian.transpose.eq, ← Matrix.transpose_mul,
      Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [hpair]
  have htraceform : Matrix.trace (A * X) =
      Matrix.trace ((UA * Dα * star UA) * X) := by rw [hAform]
  rw [htraceform]
  simp only [X, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul]
  rw [Matrix.trace_mul_comm UA]
  simp only [Matrix.mul_assoc]
  rw [← hstarW]
  rw [← Matrix.mul_assoc Dα Y (star W)]
  have hDY : Dα * Y = fun i j => (α i : ℂ) * Y i j := by
    ext i j
    simp only [Dα, Matrix.diagonal_mul]
  rw [hDY]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Y,
    Matrix.star_apply, Complex.star_def,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ((α i : ℂ) * ((α i : ℂ) /
      ((α i : ℂ) + t * β j) * W i j) * star (W i j)).re =
    α i ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
  have hnorm : W i j * star (W i j) =
      (Complex.normSq (W i j) : ℂ) := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [show (α i : ℂ) * ((α i : ℂ) /
      ((α i : ℂ) + t * β j) * W i j) * star (W i j) =
      ((α i : ℂ) * ((α i : ℂ) /
        ((α i : ℂ) + t * β j))) * (W i j * star (W i j)) by ring,
    hnorm]
  rw [← Complex.ofReal_mul t (β j),
    ← Complex.ofReal_add (α i) (t * β j),
    ← Complex.ofReal_div (α i) (α i + t * β j),
    ← Complex.ofReal_mul (α i) (α i / (α i + t * β j)),
    ← Complex.ofReal_mul
      (α i * (α i / (α i + t * β j))) (Complex.normSq (W i j)),
    Complex.ofReal_re]
  ring

private lemma spectral_sourceB_solution {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      (β j / (α i + t * β j) : ℂ) * W i j
    let X := UA * Y * star UB
    A * X + t • (X * B) = B := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (β j / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  have hα (i : n) : 0 < α i := hA.eigenvalues_pos i
  have hβ (j : n) : 0 < β j := hB.eigenvalues_pos j
  have hcore : Dα * Y + t • (Y * Dβ) = W * Dβ := by
    ext i j
    simp only [Dα, Dβ, Y, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    have hden : (α i : ℂ) + t * β j ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (add_pos (hα i) (mul_pos ht (hβ j))))
    rw [div_eq_mul_inv]
    calc
      (α i : ℂ) * (((β j : ℂ) * ((α i : ℂ) + t * β j)⁻¹) * W i j) +
          t * ((((β j : ℂ) * ((α i : ℂ) + t * β j)⁻¹) * W i j) * β j) =
          W i j * β j *
            (((α i : ℂ) + t * β j) * ((α i : ℂ) + t * β j)⁻¹) := by ring
      _ = W i j * β j := by rw [mul_inv_cancel₀ hden, mul_one]
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUAstar : UA * star UA = 1 := by
    simpa only [UA] using
      Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.prop
  have hUBstar : UB * star UB = 1 := by
    simpa only [UB] using
      Unitary.mul_star_self_of_mem hB.isHermitian.eigenvectorUnitary.prop
  have hstarUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  calc
    A * X + t • (X * B) =
        (UA * Dα * star UA) * X +
          t • (X * (UB * Dβ * star UB)) := by rw [hAform, hBform]
    _ = UB * Dβ * star UB := by
      simp only [X, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul,
        ← Matrix.mul_assoc (star UB) UB, hstarUB, Matrix.one_mul]
      rw [show UA * (Dα * (Y * star UB)) +
          t • (UA * (Y * (Dβ * star UB))) =
          UA * (Dα * Y + t • (Y * Dβ)) * star UB by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
          Matrix.mul_smul, Matrix.smul_mul], hcore]
      simp only [W, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc UA (star UA) (UB * (Dβ * star UB)),
        hUAstar, Matrix.one_mul]
    _ = B := hBform.symm

private lemma spectral_sourceB_pairing {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (_ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      (β j / (α i + t * β j) : ℂ) * W i j
    let X := UA * Y * star UB
    (star (vec Bᵀ) ⬝ᵥ vec Xᵀ).re =
      ∑ i, ∑ j, β j ^ 2 / (α i + t * β j) *
        Complex.normSq (W i j) := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (β j / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  have hstarW : star W = star UB * UA := by
    simp only [W, star_mul, star_star]
  have hpair : star (vec Bᵀ) ⬝ᵥ vec Xᵀ = Matrix.trace (B * X) := by
    rw [Matrix.star_vec_dotProduct_vec]
    rw [hB.isHermitian.transpose.eq, ← Matrix.transpose_mul,
      Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [hpair]
  have htraceform : Matrix.trace (B * X) =
      Matrix.trace ((UB * Dβ * star UB) * X) := by rw [hBform]
  rw [htraceform]
  simp only [X, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm UB]
  simp only [Matrix.mul_assoc]
  rw [hUB, Matrix.mul_one]
  rw [← Matrix.mul_assoc (star UB) UA Y, ← hstarW]
  have hD : Dβ * (star W * Y) =
      fun i j => (β i : ℂ) * (star W * Y) i j := by
    ext i j
    simp only [Dβ, Matrix.diagonal_mul]
  rw [hD]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Y, W,
    Matrix.star_apply, Complex.star_def,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((β j : ℂ) * (star (W i j) *
      ((β j : ℂ) / ((α i : ℂ) + t * β j) * W i j))).re =
    β j ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
  have hnorm : star (W i j) * W i j =
      (Complex.normSq (W i j) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [show (β j : ℂ) * (star (W i j) *
      ((β j : ℂ) / ((α i : ℂ) + t * β j) * W i j)) =
      ((β j : ℂ) * ((β j : ℂ) /
        ((α i : ℂ) + t * β j))) * (star (W i j) * W i j) by ring,
    hnorm]
  rw [← Complex.ofReal_mul t (β j),
    ← Complex.ofReal_add (α i) (t * β j),
    ← Complex.ofReal_div (β j) (α i + t * β j),
    ← Complex.ofReal_mul (β j) (β j / (α i + t * β j)),
    ← Complex.ofReal_mul
      (β j * (β j / (α i + t * β j))) (Complex.normSq (W i j)),
    Complex.ofReal_re]
  ring

/-- The source-`A` left-right resolvent quadratic form has the spectral
expansion
\[
 \sum_{i,j}\frac{\alpha_i^2}{\alpha_i+t\beta_j}|W_{ij}|^2.
\]

This is the first resolvent term in the matrix lift `(intAB)` of
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 423--427. -/
theorem sourceA_resolvent_quadratic_spectral {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
    sourceAResolventQuadratic A B t =
      ∑ i, ∑ j,
        hA.isHermitian.eigenvalues i ^ 2 /
            (hA.isHermitian.eigenvalues i +
              t * hB.isHermitian.eigenvalues j) *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  classical
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (α i / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  let S : Matrix (n × n) (n × n) ℂ :=
    A ⊗ₖ (1 : Matrix n n ℂ) +
      t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
  have hsolution : A * X + t • (X * B) = A := by
    simpa only [UA, UB, α, β, W, Y, X] using
      spectral_sourceA_solution hA hB ht
  have hvec : S *ᵥ vec Xᵀ = vec Aᵀ := by
    change (A ⊗ₖ (1 : Matrix n n ℂ) +
      t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ = vec Aᵀ
    rw [leftRight_mulVec_vec_transpose, hsolution]
  have hS : S.PosDef := by
    simpa only [S] using superop_leftRight_posDef ht hA hB
  letI : Invertible S := hS.isUnit.invertible
  have hinv : S⁻¹ *ᵥ vec Aᵀ = vec Xᵀ := by
    rw [← hvec, mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
  simp only [sourceAResolventQuadratic]
  rw [hinv]
  simpa only [UA, UB, α, β, W, Y, X] using
    spectral_sourceA_pairing hA hB ht

/-- The source-`B` left-right resolvent quadratic form has the spectral
expansion
\[
 \sum_{i,j}\frac{\beta_j^2}{\alpha_i+t\beta_j}|W_{ij}|^2.
\]

This is the second resolvent term in the matrix lift `(intAB)` of
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 423--427. -/
theorem sourceB_resolvent_quadratic_spectral {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
    sourceBResolventQuadratic A B t =
      ∑ i, ∑ j,
        hB.isHermitian.eigenvalues j ^ 2 /
            (hA.isHermitian.eigenvalues i +
              t * hB.isHermitian.eigenvalues j) *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  classical
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    (β j / (α i + t * β j) : ℂ) * W i j
  let X : Matrix n n ℂ := UA * Y * star UB
  let S : Matrix (n × n) (n × n) ℂ :=
    A ⊗ₖ (1 : Matrix n n ℂ) +
      t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
  have hsolution : A * X + t • (X * B) = B := by
    simpa only [UA, UB, α, β, W, Y, X] using
      spectral_sourceB_solution hA hB ht
  have hvec : S *ᵥ vec Xᵀ = vec Bᵀ := by
    change (A ⊗ₖ (1 : Matrix n n ℂ) +
      t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ = vec Bᵀ
    rw [leftRight_mulVec_vec_transpose, hsolution]
  have hS : S.PosDef := by
    simpa only [S] using superop_leftRight_posDef ht hA hB
  letI : Invertible S := hS.isUnit.invertible
  have hinv : S⁻¹ *ᵥ vec Bᵀ = vec Xᵀ := by
    rw [← hvec, mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
  simp only [sourceBResolventQuadratic]
  rw [hinv]
  simpa only [UA, UB, α, β, W, Y, X] using
    spectral_sourceB_pairing hA hB ht

/-- The source-`A` resolvent quadratic form is continuous for positive
resolvent parameter. -/
theorem sourceAResolventQuadratic_continuousOn {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ContinuousOn (sourceAResolventQuadratic A B) (Ioi 0) := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hspectral : ContinuousOn
      (fun t : ℝ => ∑ i, ∑ j,
        α i ^ 2 / (α i + t * β j) * P i j) (Ioi 0) := by
    apply continuousOn_finsetSum Finset.univ
    intro i _
    apply continuousOn_finsetSum Finset.univ
    intro j _ t ht
    have ht0 : 0 < t := ht
    have hα : 0 < α i := hA.eigenvalues_pos i
    have hβ : 0 < β j := hB.eigenvalues_pos j
    have hden : α i + t * β j ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop
  refine hspectral.congr (fun t ht => ?_)
  simpa only [α, β, W, P] using
    sourceA_resolvent_quadratic_spectral hA hB ht

/-- The source-`B` resolvent quadratic form is continuous for positive
resolvent parameter. -/
theorem sourceBResolventQuadratic_continuousOn {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ContinuousOn (sourceBResolventQuadratic A B) (Ioi 0) := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hspectral : ContinuousOn
      (fun t : ℝ => ∑ i, ∑ j,
        β j ^ 2 / (α i + t * β j) * P i j) (Ioi 0) := by
    apply continuousOn_finsetSum Finset.univ
    intro i _
    apply continuousOn_finsetSum Finset.univ
    intro j _ t ht
    have ht0 : 0 < t := ht
    have hα : 0 < α i := hA.eigenvalues_pos i
    have hβ : 0 < β j := hB.eigenvalues_pos j
    have hden : α i + t * β j ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop
  refine hspectral.congr (fun t ht => ?_)
  simpa only [α, β, W, P] using
    sourceB_resolvent_quadratic_spectral hA hB ht

open scoped Matrix.Norms.L2Operator in
/-- For Hermitian matrices, the totalized trace-log relative entropy is the
spectral double sum
\[
 D(A\Vert B)=\sum_{i,j}\alpha_i
   (\log\alpha_i-\log\beta_j)|W_{ij}|^2.
\]

Here the logarithm is Mathlib's totalized `Real.log`: `Real.log 0 = 0`, and
for a negative eigenvalue `x` its value is `Real.log |x|`. Thus the theorem
is an algebraic totalized extension to arbitrary Hermitian matrices of the
strictly positive trace-log identity `(J1)` in Jenčová--Ruskai,
arXiv:0903.2895v4, lines 277--287. For positive-semidefinite matrices on the
physical support domain, it gives the usual finite-dimensional spectral
expression. -/
theorem quantumRelativeEntropy_spectral {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    quantumRelativeEntropy A B =
      ∑ i, ∑ j,
        hA.eigenvalues i *
          (Real.log (hA.eigenvalues i) -
            Real.log (hB.eigenvalues j)) *
          Complex.normSq
            ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  classical
  let α : n → ℝ := hA.eigenvalues
  let β : n → ℝ := hB.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hWrow : W * star W = 1 := by
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (hB.eigenvectorUnitary : Matrix n n ℂ)]
    rw [Unitary.mul_star_self_of_mem
      hB.eigenvectorUnitary.prop, Matrix.one_mul]
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hrow (i : n) : ∑ j, P i j = 1 := by
    exact TNLean.Klein.row_sum_normSq_eq_one hWrow i
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub]
  have hlogB : CFC.log B = hB.cfc Real.log := by
    rw [CFC.log]
    exact Matrix.IsHermitian.cfc_eq hB Real.log
  have hself : (Matrix.trace (A * CFC.log A)).re =
      ∑ i, ∑ j, α i * Real.log (α i) * P i j := by
    have h := vonNeumannEntropy_eq_neg_trace_mul_log hA
    rw [vonNeumannEntropy] at h
    have hre : (Matrix.trace (A * CFC.log A)).re =
        ∑ i, α i * Real.log (α i) := by
      rw [show (Matrix.trace (A * CFC.log A)).re =
          -(-(Matrix.trace (A * CFC.log A)).re) by ring,
        ← h, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Real.negMulLog]
        ring
    rw [hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← mul_one (α i * Real.log (α i)), ← hrow i]
    rw [Finset.mul_sum]
  have hcross : (Matrix.trace (A * CFC.log B)).re =
      ∑ i, ∑ j, α i * Real.log (β j) * P i j := by
    rw [hlogB, TNLean.Klein.re_trace_mul_cfc_eq_double_sum
      hA hB Real.log]
  rw [hself, hcross, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [α, β, W, P]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The positive-definite specialization of
`quantumRelativeEntropy_spectral`. -/
theorem quantumRelativeEntropy_posDef_spectral {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    quantumRelativeEntropy A B =
      ∑ i, ∑ j,
        hA.isHermitian.eigenvalues i *
          (Real.log (hA.isHermitian.eigenvalues i) -
            Real.log (hB.isHermitian.eigenvalues j)) *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) :=
  quantumRelativeEntropy_spectral hA.isHermitian hB.isHermitian

open scoped Matrix.Norms.L2Operator in
/-- Simultaneous multiplication of two positive-definite arguments by a
positive scalar multiplies their relative entropy by the same scalar.

This is the positive-definite homogeneity of finite-dimensional Umegaki
relative entropy. It follows from the trace-log formula and the identity
`log(c A) = (log c) 1 + log A` for `c > 0`. -/
theorem quantumRelativeEntropy_smul_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 0 < c) :
    quantumRelativeEntropy (c • A) (c • B) =
      c * quantumRelativeEntropy A B := by
  rw [quantumRelativeEntropy]
  rw [CFC.log_smul A (fun x hx hx0 =>
      spectrum.zero_notMem ℝ hA.isUnit (hx0 ▸ hx)) (ne_of_gt hc) hA.isHermitian,
    CFC.log_smul B (fun x hx hx0 =>
      spectrum.zero_notMem ℝ hB.isUnit (hx0 ▸ hx)) (ne_of_gt hc) hB.isHermitian]
  simp only [add_sub_add_left_eq_sub]
  rw [smul_mul]
  simp [Matrix.trace_smul, quantumRelativeEntropy]

/-- The two-source resolvent integrand for positive-definite relative entropy.
The source-`B` term carries the coefficient `t` required by the scalar
representation. This is the matrix lift `(intAB)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 423--427. -/
noncomputable def relativeEntropyResolventIntegrand
    (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (sourceAResolventQuadratic A B t - (Matrix.trace B).re +
      t * sourceBResolventQuadratic A B t) / (1 + t)

private lemma relativeEntropyResolventIntegrand_eq_spectral
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 < t) :
    relativeEntropyResolventIntegrand A B t =
      ∑ i, ∑ j,
        relativeEntropyScalar
            (hA.isHermitian.eigenvalues i)
            (hB.isHermitian.eigenvalues j) t *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hWcol : star W * W = 1 := by
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)]
    rw [Unitary.mul_star_self_of_mem
      hA.isHermitian.eigenvectorUnitary.prop, Matrix.one_mul]
    exact Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  have hcol (j : n) : ∑ i, P i j = 1 := by
    exact TNLean.Klein.col_sum_normSq_eq_one hWcol j
  have htrace : (Matrix.trace B).re = ∑ i, ∑ j, β j * P i j := by
    have htr : (Matrix.trace B).re = ∑ j, β j := by
      rw [hB.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => Complex.ofReal_re _
    rw [htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← mul_one (β j), ← hcol j]
    rw [Finset.mul_sum]
  rw [relativeEntropyResolventIntegrand,
    sourceA_resolvent_quadratic_spectral hA hB ht,
    sourceB_resolvent_quadratic_spectral hA hB ht]
  change ((∑ i, ∑ j, α i ^ 2 / (α i + t * β j) * P i j) -
      (Matrix.trace B).re +
      t * (∑ i, ∑ j, β j ^ 2 / (α i + t * β j) * P i j)) /
      (1 + t) = _
  rw [htrace, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [relativeEntropyScalar, α, β, W, P]
  ring

/-- The coefficient-correct positive-definite relative-entropy resolvent
integrand is integrable on `(0, ∞)`.

This is the integrability assertion accompanying `(intAB)` in
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 423--427. -/
theorem relativeEntropyResolventIntegrand_integrableOn
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    IntegrableOn (relativeEntropyResolventIntegrand A B) (Ioi 0) := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hspectral : IntegrableOn
      (fun t : ℝ => ∑ i, ∑ j,
        relativeEntropyScalar (α i) (β j) t * P i j) (Ioi 0) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    exact (relativeEntropyScalar_integrableOn
      (hA.eigenvalues_pos i) (hB.eigenvalues_pos j)).mul_const (P i j)
  refine hspectral.congr_fun (fun t ht => ?_) measurableSet_Ioi
  symm
  simpa only [α, β, W, P] using
    relativeEntropyResolventIntegrand_eq_spectral hA hB ht

/-- The coefficient-correct positive-definite relative-entropy resolvent
integrand is continuous on `(0, ∞)`.

This is the continuity input needed to pass from almost-everywhere vanishing
of the Jenčová--Ruskai integrand to pointwise vanishing. -/
theorem relativeEntropyResolventIntegrand_continuousOn
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    ContinuousOn (relativeEntropyResolventIntegrand A B) (Ioi 0) := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hspectral : ContinuousOn
      (fun t : ℝ => ∑ i, ∑ j,
        relativeEntropyScalar (α i) (β j) t * P i j) (Ioi 0) := by
    apply continuousOn_finsetSum Finset.univ
    intro i _
    apply continuousOn_finsetSum Finset.univ
    intro j _ t ht
    have ht0 : 0 < t := ht
    have hα : 0 < α i := hA.eigenvalues_pos i
    have hβ : 0 < β j := hB.eigenvalues_pos j
    have hden : α i + t * β j ≠ 0 := by positivity
    have h1 : 1 + t ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    unfold relativeEntropyScalar
    fun_prop
  refine hspectral.congr (fun t ht => ?_)
  simpa only [α, β, W, P] using
    relativeEntropyResolventIntegrand_eq_spectral hA hB ht

/-- **Positive-definite relative entropy as a two-source resolvent integral.**
For positive-definite `A` and `B`,
\[
 D(A\Vert B)=\int_0^\infty
 \frac{Q_A(t)-\operatorname{tr}B+tQ_B(t)}{1+t}\,dt.
\]
Both source families, and the coefficient `t` on the source-`B` family, are
part of the statement.

This is the finite-dimensional specialization of `(intAB)` in
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 423--427. -/
theorem quantumRelativeEntropy_resolvent_integral
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    quantumRelativeEntropy A B =
      ∫ t : ℝ in Ioi 0, relativeEntropyResolventIntegrand A B t := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hterm (i j : n) :
      IntegrableOn (fun t : ℝ =>
        relativeEntropyScalar (α i) (β j) t * P i j) (Ioi 0) :=
    (relativeEntropyScalar_integrableOn
      (hA.eigenvalues_pos i) (hB.eigenvalues_pos j)).mul_const (P i j)
  rw [quantumRelativeEntropy_posDef_spectral hA hB]
  change (∑ i, ∑ j,
      α i * (Real.log (α i) - Real.log (β j)) * P i j) = _
  calc
    (∑ i, ∑ j,
        α i * (Real.log (α i) - Real.log (β j)) * P i j) =
        ∑ i, ∑ j,
          (∫ t : ℝ in Ioi 0,
            relativeEntropyScalar (α i) (β j) t) * P i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_relativeEntropyScalar
        (hA.eigenvalues_pos i) (hB.eigenvalues_pos j)]
    _ = ∫ t : ℝ in Ioi 0,
        ∑ i, ∑ j,
          relativeEntropyScalar (α i) (β j) t * P i j := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro j _
          rw [integral_mul_const]
        · exact fun j _ => hterm i j
      · intro i _
        apply integrable_finsetSum Finset.univ
        exact fun j _ => hterm i j
    _ = ∫ t : ℝ in Ioi 0, relativeEntropyResolventIntegrand A B t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      symm
      simpa only [α, β, W, P] using
        relativeEntropyResolventIntegrand_eq_spectral hA hB ht

end Matrix
