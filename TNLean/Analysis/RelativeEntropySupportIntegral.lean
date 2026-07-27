/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PosSemidefSupport
import TNLean.Analysis.RelativeEntropyResolventIntegral

/-!
# Support-domain spectral integral of relative entropy

This file extends the scalar resolvent integral to positive-semidefinite
matrices under the support inclusion `ker B ⊆ ker A`. Zero reference
eigenvalues are removed only after multiplication by their spectral weights,
so no nonintegrable unweighted zero-reference term is introduced.

## Main results

* `quantumRelativeEntropy_smul_support` proves positive homogeneity on the
  finite-relative-entropy support domain.
* `supportRelativeEntropySpectralIntegrand` is the finite support-domain
  spectral integrand.
* `supportRelativeEntropySpectralIntegrand_integrableOn_and_integral_eq_quantumRelativeEntropy`
  identifies its integral with the totalized trace-log relative entropy.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §2.1 and lines 717--720.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

/-- If the first spectral value is zero and the reference spectral value and
resolvent parameter are positive, then the scalar relative-entropy resolvent
integrand vanishes.

This is the zero-source boundary of `(intspec)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 406--413, used with the support convention
in the positive-semidefinite extension at lines 717--720. -/
theorem relativeEntropyScalar_zero_left {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    relativeEntropyScalar 0 b t = 0 := by
  unfold relativeEntropyScalar
  have htb : t * b ≠ 0 := mul_ne_zero ht.ne' hb.ne'
  have h1 : 1 + t ≠ 0 := by positivity
  field_simp
  ring

/-- If the reference scalar is zero and the weighted source scalar vanishes,
then the complete weighted resolvent term vanishes for every parameter. -/
theorem relativeEntropyScalar_mul_eq_zero_of_right_eq_zero
    {a w t : ℝ} (haw : a * w = 0) :
    relativeEntropyScalar a 0 t * w = 0 := by
  rcases mul_eq_zero.mp haw with ha | hw
  · subst a
    simp [relativeEntropyScalar]
  · subst w
    simp

/-- A weighted scalar resolvent term is integrable, with its
expected logarithmic integral, provided a zero reference value annihilates
the weighted source value.

The logarithm is Mathlib's totalized logarithm, for which
`Real.log 0 = 0`. When `b = 0`, the unweighted scalar factor is generally
not integrable; the support hypothesis kills the complete weighted term
before integration. The positive scalar identity is `(intspec)` in
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 406--413, while the
zero-reference case implements the positive-semidefinite support extension
at lines 717--720. -/
theorem relativeEntropyScalar_mul_integrableOn_and_integral_of_nonneg
    {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupport : b = 0 → a * w = 0) :
    IntegrableOn (fun t : ℝ => relativeEntropyScalar a b t * w) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, relativeEntropyScalar a b t * w =
        a * (Real.log a - Real.log b) * w := by
  by_cases hb0 : b ≠ 0
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases ha0 : a ≠ 0
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      refine
        ⟨(relativeEntropyScalar_integrableOn hapos hbpos).mul_const w, ?_⟩
      rw [integral_mul_const, integral_relativeEntropyScalar hapos hbpos]
    · simp only [not_ne_iff] at ha0
      subst a
      have hzero :
          EqOn (fun t : ℝ => relativeEntropyScalar 0 b t * w) 0 (Ioi 0) := by
        intro t ht
        change relativeEntropyScalar 0 b t * w = 0
        rw [relativeEntropyScalar_zero_left hbpos ht, zero_mul]
      refine ⟨integrableOn_zero.congr_fun hzero.symm measurableSet_Ioi, ?_⟩
      rw [setIntegral_congr_fun measurableSet_Ioi hzero]
      simp
  · simp only [not_ne_iff] at hb0
    have haw : a * w = 0 := hsupport hb0
    have hzero (t : ℝ) : relativeEntropyScalar a b t * w = 0 := by
      rw [hb0]
      exact relativeEntropyScalar_mul_eq_zero_of_right_eq_zero haw
    refine ⟨integrableOn_zero.congr_fun ?_ measurableSet_Ioi, ?_⟩
    · intro t _
      change 0 = relativeEntropyScalar a b t * w
      exact (hzero t).symm
    · rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hzero t]
      rw [integral_zero]
      rw [hb0, Real.log_zero]
      rw [sub_zero, mul_right_comm a (Real.log a) w, haw, zero_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem log_smul_posSemidef {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 < c) :
    CFC.log (c • A) =
      (Real.log c) • hA.isHermitian.supportProj + CFC.log A := by
  let p : ℝ → ℝ := fun x ↦ if x ≠ 0 then 1 else 0
  have hp : ContinuousOn p (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn p
  have hlog : ContinuousOn Real.log (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn Real.log
  have hlogScaled :
      ContinuousOn Real.log ((c • ·) '' spectrum ℝ A) :=
    (A.finite_real_spectrum.image (c • ·)).continuousOn Real.log
  have hsupport : cfc p A = hA.isHermitian.supportProj := by
    rw [hA.isHermitian.cfc_eq, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply]
    simp only [Matrix.IsHermitian.supportProj, p, Function.comp_def]
    congr 2
    ext i j
    simp [Matrix.diagonal_apply]
  rw [CFC.log, CFC.log, ← cfc_comp_smul (p := IsSelfAdjoint) c Real.log A
    hlogScaled hA.isHermitian.isSelfAdjoint, ← hsupport,
    ← cfc_smul (p := IsSelfAdjoint) (Real.log c) p A hp,
    ← cfc_add (p := IsSelfAdjoint) (a := A)
      (fun x ↦ (Real.log c) • p x) Real.log
      (hf := A.finite_real_spectrum.continuousOn _)
      (hg := hlog)]
  apply cfc_congr
  intro x _
  simp only [p, smul_eq_mul]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_pos hx, Real.log_mul hc.ne' hx]
    ring

open scoped Matrix.Norms.L2Operator in
/-- Simultaneous multiplication of two positive-semidefinite arguments by a
positive scalar multiplies their relative entropy by the same scalar, provided
the kernel of the second argument is contained in the kernel of the first.

This auxiliary scaling identity is used to pass from the uniformly weighted
finite Weyl family to its unweighted form. It is a consequence of the
positive-semidefinite support convention used by Jenčová--Ruskai,
arXiv:0903.2895v4, lines 717--720.

The kernel condition is the finite-relative-entropy support condition. It makes
the two support-projection terms in `log (cA) = (log c) P_A + log A` cancel. -/
theorem quantumRelativeEntropy_smul_support {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    {c : ℝ} (hc : 0 < c) :
    quantumRelativeEntropy (c • A) (c • B) =
      c * quantumRelativeEntropy A B := by
  have hAPA : A * hA.isHermitian.supportProj = A :=
    hA.isHermitian.mul_supportProj_self
  have hAPB : A * hB.isHermitian.supportProj = A :=
    hB.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  unfold quantumRelativeEntropy
  rw [log_smul_posSemidef hA hc,
    log_smul_posSemidef hB hc, smul_mul]
  have hinside :
      A * ((Real.log c) • hA.isHermitian.supportProj + CFC.log A -
        ((Real.log c) • hB.isHermitian.supportProj + CFC.log B)) =
        A * (CFC.log A - CFC.log B) := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, hAPA, hAPB]
    rw [Matrix.mul_sub]
    abel
  rw [hinside]
  simp [Matrix.trace_smul]

open scoped Matrix.Norms.L2Operator in
/-- If the kernel of a positive-semidefinite reference matrix `B` is contained
in the kernel of `A`, then a zero eigenvector of `B` has zero overlap with
each positive spectral component of `A`.

This lemma implements the support convention in the positive-semidefinite
extension of Jenčová--Ruskai, arXiv:0903.2895v4, lines 717--720. It removes
the formally nonintegrable zero-reference-eigenvalue terms from the
support-domain relative-entropy resolvent integral. -/
theorem eigenvalue_mul_overlap_eq_zero_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    (i j : n) (hβ : hB.isHermitian.eigenvalues j = 0) :
    (hA.isHermitian.eigenvalues i : ℂ) *
        (star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j = 0 := by
  classical
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  have hBzero :
      B *ᵥ ⇑(hB.isHermitian.eigenvectorBasis j) = 0 := by
    rw [hB.isHermitian.mulVec_eigenvectorBasis, hβ, zero_smul]
  have hAzero : A *ᵥ ⇑(hB.isHermitian.eigenvectorBasis j) = 0 :=
    hker _ hBzero
  have hAUBzero : (A * UB) *ᵥ Pi.single j 1 = 0 := by
    rw [← Matrix.mulVec_mulVec]
    change A *ᵥ
      ((hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ Pi.single j 1) = 0
    rw [hB.isHermitian.eigenvectorUnitary_mulVec, hAzero]
  have hstarAUBzero :
      (star UA * (A * UB)) *ᵥ Pi.single j 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, hAUBzero, Matrix.mulVec_zero]
  have hentryzero := congrFun hstarAUBzero i
  simp only [Matrix.mulVec_single_one, Pi.zero_apply] at hentryzero
  change (star UA * (A * UB)) i j = 0 at hentryzero
  rw [hA.isHermitian.spectral_form] at hentryzero
  have hUA : star UA * UA = 1 := by
    simp [UA]
  change
    (star UA *
      ((UA * Matrix.diagonal
        (fun k => (hA.isHermitian.eigenvalues k : ℂ))) * star UA * UB)) i j = 0
    at hentryzero
  simp only [Matrix.mul_assoc] at hentryzero
  rw [← Matrix.mul_assoc, hUA, Matrix.one_mul] at hentryzero
  simp only [Matrix.diagonal_mul] at hentryzero
  simpa only [UA, UB] using hentryzero

open scoped Matrix.Norms.L2Operator in
/-- Under the support inclusion `ker B ⊆ ker A`, a zero reference eigenvalue
has zero weight in every spectral summand:
\[
  \alpha_i\lvert (U_A^\ast U_B)_{ij}\rvert^2=0.
\]

This is the nonnegative spectral-coefficient form used to implement the
support convention in the positive-semidefinite extension of
Jenčová--Ruskai, arXiv:0903.2895v4, lines 717--720. -/
theorem eigenvalue_mul_overlap_normSq_eq_zero_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    (i j : n) (hβ : hB.isHermitian.eigenvalues j = 0) :
    hA.isHermitian.eigenvalues i *
        Complex.normSq
          ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
            (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) = 0 := by
  classical
  have hcomp :=
    eigenvalue_mul_overlap_eq_zero_of_kernel_le hA hB hker i j hβ
  by_cases hα : hA.isHermitian.eigenvalues i ≠ 0
  · have hαc : (hA.isHermitian.eigenvalues i : ℂ) ≠ 0 := by
      exact_mod_cast hα
    have hWij :
        (star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j = 0 :=
      (mul_eq_zero.mp hcomp).resolve_left hαc
    simp [hWij]
  · simp only [not_ne_iff] at hα
    simp [hα]

open scoped Matrix.Norms.L2Operator in
/-- A zero eigenvalue of the reference matrix contributes identically zero to
the support-domain scalar resolvent sum when `ker B ⊆ ker A`.

The separate scalar factor need not be integrable when the reference
eigenvalue is zero. The support condition instead annihilates its spectral
weight before integration. This implements the support convention in the
positive-semidefinite extension of Jenčová--Ruskai, arXiv:0903.2895v4,
lines 717--720. -/
theorem relativeEntropyScalar_mul_overlap_normSq_eq_zero_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    (i j : n) (hβ : hB.isHermitian.eigenvalues j = 0) (t : ℝ) :
    relativeEntropyScalar
          (hA.isHermitian.eigenvalues i)
          (hB.isHermitian.eigenvalues j) t *
        Complex.normSq
          ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
            (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) = 0 := by
  classical
  have hweight :=
    eigenvalue_mul_overlap_normSq_eq_zero_of_kernel_le hA hB hker i j hβ
  by_cases hα : hA.isHermitian.eigenvalues i ≠ 0
  · have hnormSq :
        Complex.normSq
          ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
            (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) = 0 :=
      (mul_eq_zero.mp hweight).resolve_left hα
    simp [hnormSq]
  · simp only [not_ne_iff] at hα
    simp [relativeEntropyScalar, hα, hβ]

open scoped Matrix.Norms.L2Operator in
/-- For `t > 0`, the spectral integrand for relative entropy on the support
domain of positive-semidefinite `A` and `B` is the finite sum
\[
  \sum_{i,j} r(\alpha_i,\beta_j,t)
    \lvert (U_A^\ast U_B)_{ij}\rvert^2,
\]
where `r` is zero when `β_j = 0` and is `relativeEntropyScalar` when
`β_j > 0`. Thus no zero-over-zero quotient occurs in the definition.

Under `ker B ⊆ ker A`, this convention agrees with the totalized scalar
expression because the terms with `β_j = 0` vanish by
`relativeEntropyScalar_mul_overlap_normSq_eq_zero_of_kernel_le`. This
implements the support convention in the positive-semidefinite extension of
Jenčová--Ruskai, arXiv:0903.2895v4, lines 717--720.

The theorem `supportRelativeEntropyLeftRightIntegrand_eq_spectral` identifies
this expression with the support-projected left-right quadratic form of the
matrix lift `(intAB)`, lines 423--427. The passage to the shifted
relative-modular operator `t 1 + A ⊗ (B⁺)ᵀ` and the singular finite-family
equality-to-common-resolvent passage remain open. -/
noncomputable def supportRelativeEntropySpectralIntegrand
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : ℝ :=
  ∑ i, ∑ j,
    if 0 < hB.isHermitian.eigenvalues j then
      relativeEntropyScalar
          (hA.isHermitian.eigenvalues i)
          (hB.isHermitian.eigenvalues j) t *
        Complex.normSq
          ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
            (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)
    else 0

open scoped Matrix.Norms.L2Operator in
/-- Each weighted spectral term is integrable on the positive half-line and
has the expected logarithmic integral when `ker B ⊆ ker A`.

The zero-reference terms implement the support convention in the
positive-semidefinite extension of Jenčová--Ruskai, arXiv:0903.2895v4,
lines 717--720. The positive scalar terms use `(intspec)`, §2.1,
lines 406--413. -/
theorem
    relativeEntropyScalar_mul_overlap_normSq_integrableOn_and_integral_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    (i j : n) :
    IntegrableOn
      (fun t : ℝ =>
        relativeEntropyScalar
            (hA.isHermitian.eigenvalues i)
            (hB.isHermitian.eigenvalues j) t *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j))
      (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0,
        relativeEntropyScalar
              (hA.isHermitian.eigenvalues i)
              (hB.isHermitian.eigenvalues j) t *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) =
        hA.isHermitian.eigenvalues i *
          (Real.log (hA.isHermitian.eigenvalues i) -
            Real.log (hB.isHermitian.eigenvalues j)) *
          Complex.normSq
            ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
              (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  apply relativeEntropyScalar_mul_integrableOn_and_integral_of_nonneg
  · exact hA.eigenvalues_nonneg i
  · exact hB.eigenvalues_nonneg j
  · exact eigenvalue_mul_overlap_normSq_eq_zero_of_kernel_le hA hB hker i j

open scoped Matrix.Norms.L2Operator in
/-- The support-domain spectral integrand is integrable on the positive
half-line, and its integral is the spectral relative-entropy sum, when
`ker B ⊆ ker A`.

The zero-reference terms implement the support convention in the
positive-semidefinite extension of Jenčová--Ruskai, arXiv:0903.2895v4,
lines 717--720; the finite matrix lift is `(intAB)`, §2.1,
lines 423--427. -/
theorem
    supportRelativeEntropySpectralIntegrand_integrableOn_and_integral_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0) :
    IntegrableOn (supportRelativeEntropySpectralIntegrand hA hB) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, supportRelativeEntropySpectralIntegrand hA hB t =
        ∑ i, ∑ j,
          hA.isHermitian.eigenvalues i *
            (Real.log (hA.isHermitian.eigenvalues i) -
              Real.log (hB.isHermitian.eigenvalues j)) *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  classical
  have hterm (i j : n) :=
    relativeEntropyScalar_mul_overlap_normSq_integrableOn_and_integral_of_kernel_le
      hA hB hker i j
  have hpiece (i j : n) :
      IntegrableOn
        (fun t : ℝ =>
          if 0 < hB.isHermitian.eigenvalues j then
            relativeEntropyScalar
                (hA.isHermitian.eigenvalues i)
                (hB.isHermitian.eigenvalues j) t *
              Complex.normSq
                ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                  (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)
          else 0)
        (Ioi 0) ∧
        ∫ t : ℝ in Ioi 0,
          (if 0 < hB.isHermitian.eigenvalues j then
            relativeEntropyScalar
                (hA.isHermitian.eigenvalues i)
                (hB.isHermitian.eigenvalues j) t *
              Complex.normSq
                ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                  (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)
          else 0) =
          hA.isHermitian.eigenvalues i *
            (Real.log (hA.isHermitian.eigenvalues i) -
              Real.log (hB.isHermitian.eigenvalues j)) *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
    by_cases hβpos : 0 < hB.isHermitian.eigenvalues j
    · simpa only [hβpos, if_true] using hterm i j
    · have hβzero : hB.isHermitian.eigenvalues j = 0 :=
        le_antisymm (not_lt.mp hβpos) (hB.eigenvalues_nonneg j)
      have hweight :=
        eigenvalue_mul_overlap_normSq_eq_zero_of_kernel_le
          hA hB hker i j hβzero
      refine ⟨?_, ?_⟩
      · simp only [hβpos, if_false]
        exact integrableOn_zero
      · simp only [hβzero, lt_self_iff_false, if_false, integral_zero, Real.log_zero,
          sub_zero]
        rw [mul_right_comm, hweight, zero_mul]
  have hintegral :
      ∫ t : ℝ in Ioi 0, supportRelativeEntropySpectralIntegrand hA hB t =
        ∑ i, ∑ j,
          hA.isHermitian.eigenvalues i *
            (Real.log (hA.isHermitian.eigenvalues i) -
              Real.log (hB.isHermitian.eigenvalues j)) *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
    unfold supportRelativeEntropySpectralIntegrand
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro j _
        exact (hpiece i j).2
      · exact fun j _ => (hpiece i j).1
    · intro i _
      apply integrable_finsetSum Finset.univ
      exact fun j _ => (hpiece i j).1
  have hintegrable :
      IntegrableOn (supportRelativeEntropySpectralIntegrand hA hB) (Ioi 0) := by
    unfold supportRelativeEntropySpectralIntegrand
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    exact fun j _ => (hpiece i j).1
  exact ⟨hintegrable, hintegral⟩

open scoped Matrix.Norms.L2Operator in
/-- For positive-semidefinite `A` and `B` with `ker B ⊆ ker A`, the
support-domain spectral integrand is integrable on `(0, ∞)` and its integral
is the totalized trace-log relative entropy:
\[
  \int_0^\infty I_{A,B}(t)\,dt = D(A\Vert B).
\]

The spectral trace-log identity is `(J1)` in Jenčová--Ruskai,
arXiv:0903.2895v4, lines 277--287. The positive spectral terms use the scalar
normalization `(intspec)`, lines 406--413, and its finite spectral sum
`(intAB)`, lines 423--427. The kernel condition and zero-reference terms
implement the positive-semidefinite extension at lines 717--720. -/
theorem
    supportRelativeEntropySpectralIntegrand_integrableOn_and_integral_eq_quantumRelativeEntropy
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0) :
    IntegrableOn (supportRelativeEntropySpectralIntegrand hA hB) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, supportRelativeEntropySpectralIntegrand hA hB t =
        quantumRelativeEntropy A B := by
  have hfinite :=
    supportRelativeEntropySpectralIntegrand_integrableOn_and_integral_of_kernel_le
      hA hB hker
  refine ⟨hfinite.1, ?_⟩
  rw [hfinite.2]
  exact (quantumRelativeEntropy_spectral hA.isHermitian hB.isHermitian).symm

end Matrix
