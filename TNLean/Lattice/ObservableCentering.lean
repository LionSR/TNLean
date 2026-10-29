/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SpectralFilter.PositiveReplacement
import Mathlib.Tactic.Abel

/-!
# Centering an observable at an unnormalized vector

Subtract the actual normalized expectation times the identity. For a nonzero
vector the resulting observable has vanishing expectation and norm at most
twice the original norm. The one-sided centered correlation is the ordinary
covariance. Every complex submodule containing the identity retains this
observable, so centering preserves any supported-operator space containing
the original observable. No vector normalization or Hermiticity is assumed.

The scalar-identity norm estimate reuses the existing finite-matrix bound,
which does not impose a nonempty coordinate type.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), applied to normalized expectations.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

/-- The actual expectation divided by the squared norm of its vector.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), with normalization made explicit. -/
def normalizedVectorExpectation (ψ : EuclideanSpace ℂ n) (A : Matrix n n ℂ) : ℂ :=
  ⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)

/-- Subtract the actual normalized expectation times the identity.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6). -/
def centeredObservable (ψ : EuclideanSpace ℂ n) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - normalizedVectorExpectation ψ A • 1

/-- The normalized expectation is bounded by the observable norm for every
nonzero vector. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6); this is Cauchy--Schwarz and the operator-norm bound. -/
theorem norm_normalizedVectorExpectation_le
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ‖normalizedVectorExpectation ψ A‖ ≤ ‖A‖ := by
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hA : ‖L A ψ‖ ≤ ‖A‖ * ‖ψ‖ := Matrix.l2_opNorm_mulVec A ψ
  rw [normalizedVectorExpectation, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (pow_pos hpos 2)).mpr
  calc
    _ ≤ ‖ψ‖ * ‖L A ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖A‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = _ := by ring

/-- The actual centered observable has zero expectation without assuming
that its nonzero reference vector is normalized. Source: Hastings–Koma,
arXiv:math-ph/0507008, Section 3, equations (3.1)–(3.6). -/
theorem inner_centeredObservable_eq_zero
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ⟪ψ, L (centeredObservable ψ A) ψ⟫_ℂ = 0 := by
  have hd : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))
  have hself : ⟪ψ, ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ).trans (Complex.ofReal_pow ‖ψ‖ 2).symm
  rw [centeredObservable, map_sub, map_smul, map_one]
  change ⟪ψ, L A ψ - normalizedVectorExpectation ψ A • ψ⟫_ℂ = 0
  rw [inner_sub_right, inner_smul_right, hself, normalizedVectorExpectation,
    div_mul_cancel₀ _ hd, sub_self]

/-- Actual centering increases the observable norm by at most a factor two.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), followed by the elementary triangle estimate. -/
theorem norm_centeredObservable_le
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ‖centeredObservable ψ A‖ ≤ 2 * ‖A‖ := by
  calc
    _ ≤ ‖A‖ + ‖normalizedVectorExpectation ψ A • (1 : Matrix n n ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ ‖A‖ + ‖normalizedVectorExpectation ψ A‖ :=
      add_le_add_left
        (SpectralFilter.norm_smul_one_le (n := n) (normalizedVectorExpectation ψ A)) ‖A‖
    _ ≤ ‖A‖ + ‖A‖ := add_le_add_left (norm_normalizedVectorExpectation_le hψ A) _
    _ = _ := by ring

/-- Centering only the first observable gives the actual covariance.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6). -/
theorem inner_centeredObservable_mul
    (ψ : EuclideanSpace ℂ n) (A B : Matrix n n ℂ) :
    ⟪ψ, L (centeredObservable ψ A * B) ψ⟫_ℂ =
      ⟪ψ, L (A * B) ψ⟫_ℂ - normalizedVectorExpectation ψ A * ⟪ψ, L B ψ⟫_ℂ := by
  rw [centeredObservable, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    map_sub, map_smul]
  change ⟪ψ, L (A * B) ψ - normalizedVectorExpectation ψ A • L B ψ⟫_ℂ = _
  rw [inner_sub_right, inner_smul_right]

/-- Centering preserves every complex submodule containing the identity
and the original observable, in particular a supported-operator space.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), where scalar subtraction preserves local support. -/
theorem centeredObservable_mem
    (ψ : EuclideanSpace ℂ n) {S : Submodule ℂ (Matrix n n ℂ)}
    (h1 : (1 : Matrix n n ℂ) ∈ S) {A : Matrix n n ℂ} (hA : A ∈ S) :
    centeredObservable ψ A ∈ S :=
  S.sub_mem hA (S.smul_mem _ h1)

/-- The scalar subtraction leaves the commutator with every observable
unchanged. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), used before applying the time-commutator bound. -/
theorem centeredObservable_commutator
    (ψ : EuclideanSpace ℂ n) (A B : Matrix n n ℂ) :
    centeredObservable ψ A * B - B * centeredObservable ψ A = A * B - B * A := by
  simp only [centeredObservable, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  abel

end TNLean.Lattice
