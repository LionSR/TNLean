/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.PositiveMapProperties

/-!
# Multiplicative domains of abstract Schwarz maps

This file proves Wolf's multiplicative-domain characterization for an arbitrary
complex-linear map satisfying the Schwarz inequality.  In particular, no Kraus
representation or complete-positivity hypothesis is imposed.

## Main definitions

* `IsSchwarzMap`: the one-variable inequality in
  Wolf, Equation (5.2).
* `SchwarzMap.rightMultiplicativeDomain` and
  `SchwarzMap.leftMultiplicativeDomain`: the domains in Wolf, Equations
  (5.11)--(5.12).

## Main results

* `SchwarzMap.mem_rightMultiplicativeDomain_iff`: Wolf, Equation (5.13).
* `SchwarzMap.mem_leftMultiplicativeDomain_iff`: Wolf, Equation (5.14).
* `SchwarzMap.eq_zero_of_forall_quadratic_posSemidef`: a matrix-valued
  quadratic in a real parameter, positive semidefinite for every value of
  the parameter and with zero constant term, has zero linear coefficient;
  the completing-the-square step reused by the Wolf Ch5 line-198 equality
  criterion for the two-variable operator Schwarz inequality.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Equations (5.2) and (5.11)--(5.14); local source
  `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 156--164 and
  383--410.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {n : Type*} [Fintype n]

local notation "Mat" => Matrix n n ℂ

/-- A complex-linear matrix map satisfies the Schwarz inequality when

\(E(A^\dagger A)-E(A^\dagger)E(A)\)

is positive semidefinite for every \(A\).

This is Wolf, Equation (5.2), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 156--164. -/
def IsSchwarzMap (E : Mat →ₗ[ℂ] Mat) : Prop :=
  ∀ A, (E (Aᴴ * A) - E Aᴴ * E A).PosSemidef

namespace SchwarzMap

/-- The right multiplicative domain of \(E\), following Wolf's convention:
it consists of those \(A\) for which right multiplication by \(A\) is preserved.

Source: Wolf, Equation (5.11), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 383--386. -/
def rightMultiplicativeDomain (E : Mat →ₗ[ℂ] Mat) : Set Mat :=
  {A | ∀ X, E (X * A) = E X * E A}

/-- The left multiplicative domain of \(E\), following Wolf's convention:
it consists of those \(A\) for which left multiplication by \(A\) is preserved.

Source: Wolf, Equation (5.12), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 387--389. -/
def leftMultiplicativeDomain (E : Mat →ₗ[ℂ] Mat) : Set Mat :=
  {A | ∀ X, E (A * X) = E A * E X}

/-- The multiplicative domain is the intersection of the right and left domains.

Source: Wolf, local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 391--392. -/
def multiplicativeDomain (E : Mat →ₗ[ℂ] Mat) : Set Mat :=
  rightMultiplicativeDomain E ∩ leftMultiplicativeDomain E

/-- If a real quadratic form `t ↦ t * b + t ^ 2 * d` is nonnegative for every
`t : ℝ`, then its linear coefficient `b` vanishes (evaluate at small positive
and negative `t`).

Source: Wolf, *Quantum Channels & Operations*, Chapter 5, the quadratic-form
step of the multiplicative-domain argument, local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 391--392. -/
theorem linear_eq_zero_of_quadratic_nonneg
    (b d : ℝ) (h : ∀ t : ℝ, 0 ≤ t * b + t ^ 2 * d) :
    b = 0 := by
  have hd : 0 ≤ d := by
    have hpos := h 1
    have hneg := h (-1)
    norm_num at hpos hneg
    linarith
  have hd1 : 0 < d + 1 := by linarith
  have hspecial := h (-b / (d + 1))
  field_simp [ne_of_gt hd1] at hspecial
  nlinarith [sq_nonneg b]

/-- A matrix-valued quadratic which is positive semidefinite for every real
parameter and has zero constant term must have zero linear coefficient. -/
theorem eq_zero_of_forall_quadratic_posSemidef
    {m : Type*} [Finite m] {B D : Matrix m m ℂ}
    (h : ∀ t : ℝ,
      (((t : ℂ) • B) + ((t ^ 2 : ℝ) : ℂ) • D).PosSemidef) :
    B = 0 := by
  classical
  letI := Fintype.ofFinite m
  apply Matrix.eq_zero_of_forall_star_dotProduct_mulVec_eq_zero
  intro x
  let b : ℂ := star x ⬝ᵥ B *ᵥ x
  let d : ℂ := star x ⬝ᵥ D *ᵥ x
  have hq (t : ℝ) : 0 ≤ (t : ℂ) * b + ((t ^ 2 : ℝ) : ℂ) * d := by
    have ht := (h t).dotProduct_mulVec_nonneg x
    simpa [b, d, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul] using ht
  have hbre : b.re = 0 := by
    apply linear_eq_zero_of_quadratic_nonneg b.re d.re
    intro t
    have ht := (Complex.nonneg_iff.mp (hq t)).1
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using ht
  have hbim : b.im = 0 := by
    have hplus := (Complex.nonneg_iff.mp (hq 1)).2
    have hminus := (Complex.nonneg_iff.mp (hq (-1))).2
    norm_num [Complex.mul_im] at hplus hminus
    linarith
  exact Complex.ext hbre hbim

private theorem schwarz_cross_terms
    (E : Mat →ₗ[ℂ] Mat) (hE : IsSchwarzMap E)
    (A : Mat)
    (hA : E (Aᴴ * A) = E Aᴴ * E A) (Y : Mat) :
    E (Aᴴ * Y) = E Aᴴ * E Y ∧
      E (Yᴴ * A) = E Yᴴ * E A := by
  let L : Mat := E (Aᴴ * Y) - E Aᴴ * E Y
  let R : Mat := E (Yᴴ * A) - E Yᴴ * E A
  let Q : Mat := E (Yᴴ * Y) - E Yᴴ * E Y
  have hreal (t : ℝ) :
      (((t : ℂ) • (L + R)) + ((t ^ 2 : ℝ) : ℂ) • Q).PosSemidef := by
    have hexpand :
        E ((A + (t : ℂ) • Y)ᴴ * (A + (t : ℂ) • Y)) -
            E (A + (t : ℂ) • Y)ᴴ * E (A + (t : ℂ) • Y) =
          ((t : ℂ) • (L + R)) + ((t ^ 2 : ℝ) : ℂ) • Q := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      rw [show star (t : ℂ) = (t : ℂ) by simp]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.smul_mul, map_add, map_smul]
      rw [hA]
      simp only [smul_add, Complex.coe_smul, Complex.ofReal_pow]
      module
    rw [← hexpand]
    exact hE (A + (t : ℂ) • Y)
  have hsum : L + R = 0 := eq_zero_of_forall_quadratic_posSemidef hreal
  have himag (t : ℝ) :
      (((t : ℂ) • ((Complex.I : ℂ) • L - (Complex.I : ℂ) • R)) +
        ((t ^ 2 : ℝ) : ℂ) • Q).PosSemidef := by
    have hexpand :
        E ((A + ((t : ℂ) * Complex.I) • Y)ᴴ *
              (A + ((t : ℂ) * Complex.I) • Y)) -
            E (A + ((t : ℂ) * Complex.I) • Y)ᴴ *
              E (A + ((t : ℂ) * Complex.I) • Y) =
          ((t : ℂ) • ((Complex.I : ℂ) • L - (Complex.I : ℂ) • R)) +
            ((t ^ 2 : ℝ) : ℂ) • Q := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      rw [show star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) by simp]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.smul_mul, map_add, map_smul]
      rw [hA]
      simp only [neg_smul, smul_add, smul_neg, Complex.coe_smul,
        Complex.ofReal_pow]
      have hz :
          -(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I)) =
            ((t ^ 2 : ℝ) : ℂ) := by
        calc
          -(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I)) =
              -((t : ℂ) ^ 2 * Complex.I ^ 2) := by ring
          _ = ((t ^ 2 : ℝ) : ℂ) := by rw [Complex.I_sq]; norm_num
      simp only [smul_smul]
      simp_rw [← neg_smul]
      rw [hz]
      module
    rw [← hexpand]
    exact hE (A + ((t : ℂ) * Complex.I) • Y)
  have hdiff : (Complex.I : ℂ) • L - (Complex.I : ℂ) • R = 0 :=
    eq_zero_of_forall_quadratic_posSemidef himag
  have hL : L = 0 := by
    have hR : R = -L := eq_neg_of_add_eq_zero_right hsum
    rw [hR, smul_neg, sub_neg_eq_add, ← add_smul] at hdiff
    exact (smul_eq_zero.mp hdiff).resolve_left (by norm_num)
  have hR : R = 0 := by
    rw [hL, zero_add] at hsum
    exact hsum
  exact ⟨sub_eq_zero.mp hL, sub_eq_zero.mp hR⟩

/-- Wolf's right multiplicative-domain characterization.

For an arbitrary complex-linear map satisfying the Schwarz inequality,
equality at \(A^\dagger A\) is equivalent to preservation of every product
\(XA\).

Source: Wolf, Equation (5.13), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 399--410. -/
theorem mem_rightMultiplicativeDomain_iff
    (E : Mat →ₗ[ℂ] Mat) (hE : IsSchwarzMap E) (A : Mat) :
    A ∈ rightMultiplicativeDomain E ↔
      E (Aᴴ * A) = E Aᴴ * E A := by
  constructor
  · intro hA
    exact hA Aᴴ
  · intro hA X
    simpa using (schwarz_cross_terms E hE A hA Xᴴ).2

/-- Wolf's left multiplicative-domain characterization.

For an arbitrary complex-linear map satisfying the Schwarz inequality,
equality at \(AA^\dagger\) is equivalent to preservation of every product
\(AX\).

Source: Wolf, Equation (5.14), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 399--410. -/
theorem mem_leftMultiplicativeDomain_iff
    (E : Mat →ₗ[ℂ] Mat) (hE : IsSchwarzMap E) (A : Mat) :
    A ∈ leftMultiplicativeDomain E ↔
      E (A * Aᴴ) = E A * E Aᴴ := by
  constructor
  · intro hA
    exact hA Aᴴ
  · intro hA X
    simpa using (schwarz_cross_terms E hE Aᴴ (by simpa) X).1

/-- The full multiplicative domain consists exactly of the matrices attaining
equality in both one-sided Schwarz inequalities.

Source: Wolf, Equations (5.13)--(5.14), local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 399--410. -/
theorem mem_multiplicativeDomain_iff
    (E : Mat →ₗ[ℂ] Mat) (hE : IsSchwarzMap E) (A : Mat) :
    A ∈ multiplicativeDomain E ↔
      E (Aᴴ * A) = E Aᴴ * E A ∧
        E (A * Aᴴ) = E A * E Aᴴ := by
  rw [multiplicativeDomain, Set.mem_inter_iff,
    mem_rightMultiplicativeDomain_iff E hE A,
    mem_leftMultiplicativeDomain_iff E hE A]

end SchwarzMap
