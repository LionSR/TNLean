/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import QICLean.Algebra.OperatorNormFrobenius
import TNLean.Algebra.MatrixEntryNorm

/-!
# An entrywise bound for a Sylvester equation with positive coefficients

Let `P` and `S` be positive semidefinite and let `X = P W₁ + W₂ S` solve the Sylvester equation
`P X + X S = R Z`, where `λ R Rᴴ ≤ P²` for some `λ > 0`. In eigenbases `P = ∑ₐ pₐ fₐ fₐᴴ` and
`S = ∑ᵢ sᵢ eᵢ eᵢᴴ` the equation reads `(pₐ + sᵢ) ⟨fₐ|X|eᵢ⟩ = ⟨Rᴴ fₐ|Z eᵢ⟩`, and
`‖Rᴴ fₐ‖ ≤ λ^{-1/2} pₐ`, so every entry `⟨fₐ|X|eᵢ⟩` has modulus at most `λ^{-1/2} ‖Z‖`: the factor
`pₐ / (pₐ + sᵢ)` is at most one. When `pₐ = sᵢ = 0` the entry vanishes because of the form of
`X`. Hence `‖X‖ ≤ n² λ^{-1/2} ‖Z‖` in dimension `n`, a bound that does not depend on how small
the eigenvalues of `P` and `S` are.

This is the step that makes the positive part of a blocked map with very different block weights
`cⱼ` close to its limit relative to each weight: with `P` the positive part, `S` its limit, and
`X = (P - S) C⁻¹` for `C = ∑ⱼ cⱼ L_j L_jᴴ`, the bound holds uniformly in the weights
(`TNLean.MPS.Preparation.RelativePositivePart`). The entrywise argument is the Schur-product
argument for the Sylvester equation, as in the relative perturbation bounds for the unitary
polar factor of R.-C. Li.

## Main declarations

* `Matrix.norm_le_of_mul_add_mul_eq_mul` — the bound `‖X‖ ≤ n² λ^{-1/2} ‖Z‖`.

## References

* [Li97] R.-C. Li, *Relative perturbation bounds for the unitary polar factor*,
  BIT Numerical Mathematics 37 (1997), 67–75.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz for an entry of a product: `|(A B)ₐᵢ|² ≤ (∑ₖ |Aₐₖ|²)(∑ₖ |Bₖᵢ|²)`. -/
private theorem norm_mul_apply_sq_le (A B : Matrix n n ℂ) (a i : n) :
    ‖(A * B) a i‖ ^ 2 ≤ (∑ k, ‖A a k‖ ^ 2) * ∑ k, ‖B k i‖ ^ 2 := by
  rw [mul_apply]
  calc ‖∑ k, A a k * B k i‖ ^ 2 ≤ (∑ k, ‖A a k‖ * ‖B k i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans_eq (by simp only [norm_mul])) 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq n] in
/-- The squared norm of the row `a` of `A` is the diagonal entry `(A Aᴴ)ₐₐ`. -/
private theorem ofReal_sum_norm_sq_row (A : Matrix n n ℂ) (a : n) :
    ((∑ k, ‖A a k‖ ^ 2 : ℝ) : ℂ) = (A * Aᴴ) a a := by
  simp only [mul_apply, conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.mul_conj']

open scoped Matrix.Norms.L2Operator in
/-- **Entrywise bound for a Sylvester equation.** Let `P, S` be positive semidefinite, `λ > 0`
with `λ R Rᴴ ≤ P²`, and let `X = P W₁ + W₂ S` satisfy `P X + X S = R Z`. Then
`‖X‖ ≤ n² λ^{-1/2} ‖Z‖`, where `n` is the dimension.

In the eigenbases `fₐ` of `P` and `eᵢ` of `S` the equation gives
`(pₐ + sᵢ) ⟨fₐ|X|eᵢ⟩ = ⟨Rᴴ fₐ|Z eᵢ⟩`, whose right side is at most `λ^{-1/2} pₐ ‖Z‖`; the entries
with `pₐ = sᵢ = 0` vanish by the form of `X` (compare R.-C. Li, BIT 37 (1997), the relative
perturbation bound for the unitary polar factor). -/
theorem norm_le_of_mul_add_mul_eq_mul {P S W₁ W₂ R Z : Matrix n n ℂ} (hP : P.PosSemidef)
    (hS : S.PosSemidef) {l : ℝ} (hl : 0 < l) (hR : (P * P - (l : ℂ) • (R * Rᴴ)).PosSemidef)
    (h : P * (P * W₁ + W₂ * S) + (P * W₁ + W₂ * S) * S = R * Z) :
    ‖P * W₁ + W₂ * S‖ ≤ (Fintype.card n : ℝ) ^ 2 * ((Real.sqrt l)⁻¹ * ‖Z‖) := by
  set X := P * W₁ + W₂ * S with hXdef
  set u := hP.1.eigenvectorUnitary
  set v := hS.1.eigenvectorUnitary
  set U : Matrix n n ℂ := (u : Matrix n n ℂ)
  set V : Matrix n n ℂ := (v : Matrix n n ℂ)
  set p := hP.1.eigenvalues
  set s := hS.1.eigenvalues
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self u
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self u
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self v
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self v
  have hPd : star U * P * U = diagonal (fun a => (p a : ℂ)) := by
    have h := hP.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    exact h
  have hSd : star V * S * V = diagonal (fun i => (s i : ℂ)) := by
    have h := hS.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    exact h
  -- Conjugating a product through the unitaries.
  have hconj : ∀ A B : Matrix n n ℂ, star U * (A * B) * V =
      (star U * A * U) * (star U * B * V) := fun A B => by
    calc star U * (A * B) * V = star U * A * (U * star U) * B * V := by
          rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hconj' : ∀ A B : Matrix n n ℂ, star U * (A * B) * V =
      (star U * A * V) * (star V * B * V) := fun A B => by
    calc star U * (A * B) * V = star U * A * (V * star V) * B * V := by
          rw [hVV', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  set X' := star U * X * V
  -- The Sylvester equation in the eigenbases.
  have hkey : ∀ a i, ((p a : ℂ) + s i) * X' a i = (star U * (R * Z) * V) a i := fun a i => by
    have he : star U * (R * Z) * V =
        diagonal (fun a => (p a : ℂ)) * X' + X' * diagonal (fun i => (s i : ℂ)) := by
      rw [← h, Matrix.mul_add, Matrix.add_mul, hconj, hconj', hPd, hSd]
    rw [he, add_apply, diagonal_mul, mul_diagonal]
    ring
  -- Entries with `pₐ = sᵢ = 0` vanish.
  have hzero : ∀ a i, p a = 0 → s i = 0 → X' a i = 0 := fun a i hp hs => by
    have he : X' = diagonal (fun a => (p a : ℂ)) * (star U * W₁ * V) +
        (star U * W₂ * V) * diagonal (fun i => (s i : ℂ)) := by
      simp only [X', hXdef, Matrix.mul_add, Matrix.add_mul]
      rw [hconj, hconj', hPd, hSd]
    rw [he, add_apply, diagonal_mul, mul_diagonal, hp, hs]
    simp
  -- The rows of `Uᴴ R` are controlled by the eigenvalues of `P`.
  have hrow : ∀ a, l * ∑ k, ‖(star U * R) a k‖ ^ 2 ≤ p a ^ 2 := fun a => by
    have hpsd := hR.conjTranspose_mul_mul_same U
    rw [← star_eq_conjTranspose] at hpsd
    have hd := hpsd.diag_nonneg (i := a)
    have hPP : star U * (P * P) * U =
        diagonal (fun a => (p a : ℂ)) * diagonal (fun a => (p a : ℂ)) := by
      rw [← hPd]
      calc star U * (P * P) * U = star U * P * (U * star U) * P * U := by
            rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hRR : star U * (R * Rᴴ) * U = (star U * R) * (star U * R)ᴴ := by
      rw [conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star]
      simp only [Matrix.mul_assoc]
    have he : star U * (P * P - (l : ℂ) • (R * Rᴴ)) * U =
        diagonal (fun a => (p a : ℂ)) * diagonal (fun a => (p a : ℂ)) -
          (l : ℂ) • ((star U * R) * (star U * R)ᴴ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPP, hRR]
    rw [he, sub_apply, smul_apply, diagonal_mul_diagonal, diagonal_apply_eq,
      ← ofReal_sum_norm_sq_row, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.zero_le_real] at hd
    nlinarith [hd]
  -- The columns of `Z V` are controlled by `‖Z‖`.
  have hcol : ∀ i, ∑ k, ‖(Z * V) k i‖ ^ 2 ≤ ‖Z‖ ^ 2 := fun i =>
    (sum_column_norm_sq_le_norm_sq (Z * V) i).trans_eq (by rw [CStarRing.norm_mul_coe_unitary])
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  -- Every entry of `X'` is at most `λ^{-1/2} ‖Z‖`.
  have hent : ∀ a i, ‖X' a i‖ ≤ (Real.sqrt l)⁻¹ * ‖Z‖ := fun a i => by
    have hp := hP.eigenvalues_nonneg a
    have hs := hS.eigenvalues_nonneg i
    rcases (add_nonneg hp hs).lt_or_eq with hpos | h0
    · have hrhs : ‖(star U * (R * Z) * V) a i‖ ≤ (Real.sqrt l)⁻¹ * p a * ‖Z‖ := by
        rw [show star U * (R * Z) * V = (star U * R) * (Z * V) by simp only [Matrix.mul_assoc]]
        have h1 := norm_mul_apply_sq_le (star U * R) (Z * V) a i
        have h2 : (∑ k, ‖(star U * R) a k‖ ^ 2) * ∑ k, ‖(Z * V) k i‖ ^ 2 ≤
            (p a ^ 2 / l) * ‖Z‖ ^ 2 := by
          gcongr
          · rw [le_div_iff₀ hl, mul_comm]; exact hrow a
          · exact hcol i
        have h3 : ((Real.sqrt l)⁻¹ * p a * ‖Z‖) ^ 2 = p a ^ 2 / l * ‖Z‖ ^ 2 := by
          rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hl.le]; ring
        exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.1
          (h1.trans (h2.trans h3.symm.le))
      have hnorm : ‖X' a i‖ * (p a + s i) = ‖(star U * (R * Z) * V) a i‖ := by
        rw [← hkey, norm_mul, mul_comm, ← Complex.ofReal_add, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hpos]
      have hle : ‖X' a i‖ * (p a + s i) ≤ (Real.sqrt l)⁻¹ * ‖Z‖ * (p a + s i) := by
        rw [hnorm]
        refine hrhs.trans ?_
        have : 0 ≤ (Real.sqrt l)⁻¹ * ‖Z‖ := by positivity
        nlinarith
      exact le_of_mul_le_mul_right hle hpos
    · have hp0 : p a = 0 := by linarith
      have hs0 : s i = 0 := by linarith
      rw [hzero a i hp0 hs0, norm_zero]
      positivity
  -- Back to `X`.
  have hX : X = U * X' * star V := by
    simp only [X', ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hVV', Matrix.mul_one]
  have hnormX : ‖X‖ = ‖X'‖ := by
    rw [hX, Matrix.mul_assoc]
    change ‖(u : Matrix n n ℂ) * (X' * star (v : Matrix n n ℂ))‖ = ‖X'‖
    rw [CStarRing.norm_coe_unitary_mul, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
  rw [hnormX]
  refine (l2_opNorm_le_sum_norm_entry X').trans ?_
  calc ∑ a, ∑ i, ‖X' a i‖ * ‖(single a i 1 : Matrix n n ℂ)‖
      ≤ ∑ _a : n, ∑ _i : n, (Real.sqrt l)⁻¹ * ‖Z‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => ?_
        rw [l2_opNorm_single_one, mul_one]
        exact hent a i
    _ = (Fintype.card n : ℝ) ^ 2 * ((Real.sqrt l)⁻¹ * ‖Z‖) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Matrix
