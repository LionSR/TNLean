/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianCauchyTransform
import QICLean.Analysis.GaussianFilter.MatrixIntegral

/-!
# The actual regularized Gaussian negative-frequency observable

The Cauchy denominator multiplies the actual Heisenberg evolution of an
observable. Positive regularization bounds its norm uniformly in time, so
its Bochner integral against the Gaussian probability measure exists. Its
matrix elements between actual energy eigenvectors are the scalar
Gaussian--Cauchy transform at their energy difference. The scalar limit
therefore gives the Gaussian probability cutoff without an assumed spectral
multiplier or frequency-separation hypothesis.

The matrix norm is the Euclidean operator norm. The integrability statement
allows zero time variance; the nontrivial cutoff limit requires positive
variance. The finite regularizer bound retains its inverse regularizer and
is not a uniform estimate for taking that regularizer to zero.

Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.14), and the regularized observable used in Section 3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace NNReal Topology

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual regularized Cauchy factor times the Heisenberg evolution.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
def gaussianNegativeFrequencyIntegrand (H A : Matrix n n ℂ) (ε t : ℝ) : Matrix n n ℂ :=
  ((ε : ℂ) - Complex.I * t)⁻¹ •
    (hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t))

/-- The actual regularized frequency integral, normalized by the density
at zero of the inverse-variance Gaussian. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equations (3.7)–(3.8). -/
def gaussianNegativeFrequencyOperator (h : ℝ≥0) (ε : ℝ) (H A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (GaussianFilter.kernel h⁻¹ 0 : ℂ) •
    ∫ t : ℝ, gaussianNegativeFrequencyIntegrand H A ε t ∂gaussianReal 0 h

/-- Positive regularization makes the actual time integrand continuous.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
theorem continuous_gaussianNegativeFrequencyIntegrand
    (H A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gaussianNegativeFrequencyIntegrand H A ε) := by
  apply Continuous.smul
  · exact (by fun_prop : Continuous fun t : ℝ ↦ (ε : ℂ) - Complex.I * t).inv₀
      (cauchyDenominator_ne_zero hε)
  · exact SpectralFilter.continuous_hermitianUnitaryPath_conj H A

/-- Unitary conjugation bounds the actual integrand by the inverse positive
regularizer times the observable norm. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_gaussianNegativeFrequencyIntegrand_le
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖gaussianNegativeFrequencyIntegrand H A ε t‖ ≤ ε⁻¹ * ‖A‖ := by
  rw [gaussianNegativeFrequencyIntegrand, norm_smul,
    SpectralFilter.norm_hermitianUnitaryPath_conj hH A t]
  exact mul_le_mul_of_nonneg_right (norm_inv_cauchyDenominator_le hε t) (norm_nonneg A)

/-- The actual operator-valued integrand is Bochner integrable for every
Gaussian variance and every positive regularizer. In particular its norm
is integrable. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.8). -/
theorem integrable_gaussianNegativeFrequencyIntegrand
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianNegativeFrequencyIntegrand H A ε) (gaussianReal 0 h) := by
  apply (integrable_const (ε⁻¹ * ‖A‖)).mono'
    (continuous_gaussianNegativeFrequencyIntegrand H A hε).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_gaussianNegativeFrequencyIntegrand_le hH A hε)

/-- The actual regularized observable has a finite explicit norm bound.
The inverse regularizer is retained. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_gaussianNegativeFrequencyOperator_le
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖gaussianNegativeFrequencyOperator h ε H A‖ ≤
      GaussianFilter.kernel h⁻¹ 0 * (ε⁻¹ * ‖A‖) := by
  rw [gaussianNegativeFrequencyOperator, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (GaussianFilter.kernel_nonneg _ _)]
  apply mul_le_mul_of_nonneg_left ?_ (GaussianFilter.kernel_nonneg _ _)
  simpa using norm_integral_le_of_norm_le_const (μ := gaussianReal 0 h)
    (Filter.Eventually.of_forall (norm_gaussianNegativeFrequencyIntegrand_le hH A hε))

/-- Energy eigenvectors identify the actual operator integral with its
scalar Gaussian--Cauchy transform. No matrix-element or frequency witness
is assumed. Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.13). -/
theorem dotProduct_integral_gaussianNegativeFrequencyIntegrand_mulVec
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    star v ⬝ᵥ ((∫ t : ℝ, gaussianNegativeFrequencyIntegrand H A ε t
        ∂gaussianReal 0 h) *ᵥ w) =
      gaussianCauchyTransform h ε (E - E') * (star v ⬝ᵥ (A *ᵥ w)) := by
  let Lin : Matrix n n ℂ →ₗ[ℂ] ℂ :=
    (dotProductBilin ℂ ℂ (star v)).comp ((Matrix.mulVecBilin ℂ ℂ).flip w)
  let L : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Lin
  have hL : ∀ M, L M = star v ⬝ᵥ (M *ᵥ w) := fun M ↦ rfl
  rw [← hL, ← L.integral_comp_comm
    (integrable_gaussianNegativeFrequencyIntegrand h hH A hε)]
  simp_rw [gaussianNegativeFrequencyIntegrand, map_smul, hL,
    SpectralFilter.dotProduct_conj_mulVec hH A hv hw, smul_eq_mul]
  have hphase (t : ℝ) : (t : ℂ) * ((E : ℂ) - E') * Complex.I =
      ((E - E' : ℝ) : ℂ) * t * Complex.I := by
    push_cast
    ring
  simp_rw [hphase, ← mul_assoc]
  rw [integral_mul_const]
  rfl

/-- Exact eigenvector matrix elements of the actual normalized regularized
observable. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equations (3.7)–(3.13). -/
theorem dotProduct_gaussianNegativeFrequencyOperator_mulVec
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    star v ⬝ᵥ (gaussianNegativeFrequencyOperator h ε H A *ᵥ w) =
      (GaussianFilter.kernel h⁻¹ 0 : ℂ) * gaussianCauchyTransform h ε (E - E') *
        (star v ⬝ᵥ (A *ᵥ w)) := by
  rw [gaussianNegativeFrequencyOperator, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_integral_gaussianNegativeFrequencyIntegrand_mulVec h hH A hε hv hw,
    mul_assoc]

/-- The eigenvector matrix-element formula in the Euclidean Hilbert space.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
theorem inner_gaussianNegativeFrequencyOperator
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : EuclideanSpace ℂ n} {E E' : ℝ}
    (hv : H *ᵥ WithLp.ofLp v = (E : ℂ) • WithLp.ofLp v)
    (hw : H *ᵥ WithLp.ofLp w = (E' : ℂ) • WithLp.ofLp w) :
    ⟪v, Matrix.toEuclideanLin (gaussianNegativeFrequencyOperator h ε H A) w⟫_ℂ =
      (GaussianFilter.kernel h⁻¹ 0 : ℂ) * gaussianCauchyTransform h ε (E - E') *
        ⟪v, Matrix.toEuclideanLin A w⟫_ℂ := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, dotProduct_comm] using
    dotProduct_gaussianNegativeFrequencyOperator_mulVec h hH A hε hv hw

/-- The actual regularized observable converges entrywise between energy
eigenvectors to the Gaussian negative-frequency multiplier. This follows
from the actual scalar Cauchy limit, with no supplied multiplier premise.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem tendsto_dotProduct_gaussianNegativeFrequencyOperator
    (h : ℝ≥0) (hh : 0 < h) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : Matrix n n ℂ) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    Filter.Tendsto (fun ε : ℝ ↦
      star v ⬝ᵥ (gaussianNegativeFrequencyOperator h ε H A *ᵥ w))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((gaussianReal 0 h⁻¹).real (Set.Ici (E - E')) : ℂ) *
        (star v ⬝ᵥ (A *ᵥ w)))) := by
  apply ((tendsto_normalized_gaussianCauchyTransform h hh (E - E')).mul_const
    (star v ⬝ᵥ (A *ᵥ w))).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dotProduct_gaussianNegativeFrequencyOperator_mulVec h hH A hε hv hw).symm

end TNLean.Lattice
