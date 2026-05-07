/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order

/-!
# Frobenius norm squared and Euclidean-space embedding for matrices

Shared Frobenius-norm identities for the spectral-gap modules (`SpectralGap.lean`,
`SpectralGapRect.lean`).  Everything here works for *rectangular*
`Matrix (Fin m) (Fin n) ℂ`; the square case is obtained by setting `m = n`.

The Frobenius (Hilbert--Schmidt) norm is used throughout the spectral-gap
proofs in this repository (cf. PerezGarcia2007).  Wolf Chapter 6 proves the
same eigenvalue bound using the operator norm via Russo--Dye
(Proposition 6.1); both norms yield the same spectral-radius estimate
for finite-dimensional CP maps.

## Main definitions

* `MPSTensor.frobSq`: Frobenius norm squared, `∑ i j, ‖X i j‖²`.
* `MPSTensor.matToES`: Isometric embedding of a matrix into `EuclideanSpace ℂ (Fin m × Fin n)`.

## Main results

* `MPSTensor.frobSq_trace`: `frobSq X = (trace(X† X)).re`.
* `MPSTensor.frobSq_eq_zero_iff`, `frobSq_pos_of_ne_zero`, `frobSq_smul`.
* `MPSTensor.norm_matToES_sq`: `‖matToES X‖² = frobSq X`.
* `MPSTensor.norm_sq_sum_mul_le`: Cauchy–Schwarz estimate for norm-squared of
  an inner product.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {m n : ℕ}

/-! ### Frobenius norm squared -/

/-- Frobenius norm squared of a (possibly rectangular) matrix: `∑ i j, ‖X i j‖²`. -/
noncomputable def frobSq (X : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, ‖X i j‖ ^ 2

lemma frobSq_nonneg (X : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ frobSq X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

private lemma complex_mul_star_re (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [show star z = starRingEnd ℂ z from rfl, Complex.mul_conj', ← Complex.ofReal_pow]
  exact Complex.ofReal_re _

/-- The Frobenius norm squared equals `(trace(X† X)).re`. -/
lemma frobSq_trace (X : Matrix (Fin m) (Fin n) ℂ) :
    frobSq X = (Matrix.trace (Xᴴ * X)).re := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j
  rw [show star (X j i) * X j i = ↑(Complex.normSq (X j i)) from
    Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma frobSq_eq_zero_iff (X : Matrix (Fin m) (Fin n) ℂ) : frobSq X = 0 ↔ X = 0 := by
  constructor
  · intro h; ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by positivity).mp h i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp h1 j
      (Finset.mem_univ _)
    rwa [sq_eq_zero_iff, norm_eq_zero] at h2
  · rintro rfl; simp [frobSq]

lemma frobSq_pos_of_ne_zero (X : Matrix (Fin m) (Fin n) ℂ) (hX : X ≠ 0) :
    0 < frobSq X :=
  lt_of_le_of_ne (frobSq_nonneg X) (Ne.symm (mt (frobSq_eq_zero_iff X).mp hX))

lemma frobSq_smul (c : ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    frobSq (c • X) = ‖c‖ ^ 2 * frobSq X := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/-! ### Euclidean-space embedding -/

/-- Embed a matrix into the Euclidean space `ℂ^(m × n)` by flattening entries. -/
noncomputable def matToES (M : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin m × Fin n) :=
  (EuclideanSpace.equiv (Fin m × Fin n) ℂ).symm (fun p => M p.1 p.2)

@[simp] lemma matToES_apply (M : Matrix (Fin m) (Fin n) ℂ) (p : Fin m × Fin n) :
    matToES M p = M p.1 p.2 := by simp [matToES, EuclideanSpace.equiv]

lemma matToES_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin m) (Fin n) ℂ) :
    matToES (∑ i ∈ s, f i) = ∑ i ∈ s, matToES (f i) := by
  ext p; simp [Matrix.sum_apply, Finset.sum_apply]

lemma norm_matToES_sq (M : Matrix (Fin m) (Fin n) ℂ) :
    ‖matToES M‖ ^ 2 = frobSq M := by
  rw [sq, ← @inner_self_eq_norm_mul_norm ℂ]
  change RCLike.re (@inner ℂ _ _ (matToES M) (matToES M)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', matToES_apply, starRingEnd_apply]
  rw [show (∑ x : Fin m × Fin n, star (M x.1 x.2) * M x.1 x.2) =
    ∑ i, ∑ j, star (M i j) * M i j from Fintype.sum_prod_type _]
  simp only [frobSq, Complex.re_sum, RCLike.re_to_complex]
  congr 1; ext i; congr 1; ext j
  rw [mul_comm, show M i j * star (M i j) = (↑(‖M i j‖ ^ 2) : ℂ) from by
    rw [show star (M i j) = starRingEnd ℂ (M i j) from rfl, Complex.mul_conj',
      ← Complex.ofReal_pow]]
  exact Complex.ofReal_re _

/-! ### Cauchy–Schwarz estimate -/

/-- Cauchy–Schwarz for `‖∑ aₖ bₖ‖²`. -/
lemma norm_sq_sum_mul_le {D : ℕ} (a b : Fin D → ℂ) :
    ‖∑ k, a k * b k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_mul_le _ _)) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

end MPSTensor
