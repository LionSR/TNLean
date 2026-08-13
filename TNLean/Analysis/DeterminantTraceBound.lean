/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixTraceInequalities

/-!
# A determinant bound from the trace of `Aᴴ A`

For a square complex matrix `A` whose index type has cardinality `D`, with
singular values `s₁, …, s_D`,

  `D ^ D · |det A| ^ 2 ≤ tr[Aᴴ A] ^ D`,

because `|det A| ^ 2 = ∏ᵢ sᵢ ^ 2` and `tr[Aᴴ A] = ∑ᵢ sᵢ ^ 2`. The inequality is
the arithmetic–geometric mean estimate for the eigenvalues of the positive
semidefinite matrix `Aᴴ A`. It is the step behind Wolf's bound of the
determinant of a linear map on `M_d(ℂ)` by the purity of its
Choi–Jamiolkowski operator, `Wolf §6, lines 520–545`.

The arithmetic–geometric mean estimates of `TNLean.Analysis.MatrixTraceInequalities`
are indexed by `Fin D`; here they are transported to an arbitrary finite index
type, which is what a matrix whose rows are labelled by pairs requires.

## Main statements

* `pow_card_mul_prod_le_sum_pow'` — arithmetic–geometric mean inequality in
  product/sum form over an arbitrary finite index type.
* `Matrix.PosSemidef.pow_card_mul_det_re_le_trace_re_pow'` — the
  trace–determinant form `D ^ D · det M ≤ (tr M) ^ D` for a positive
  semidefinite `M` over an arbitrary finite index type.
* `Matrix.trace_conjTranspose_mul_self_re` — `tr[Aᴴ A]` is the sum of the
  squared moduli of the entries of `A`.
* `Matrix.pow_card_mul_norm_det_sq_le_trace_conjTranspose_mul_self_pow` — the
  determinant bound `D ^ D · |det A| ^ 2 ≤ tr[Aᴴ A] ^ D`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Finset

/-- **Arithmetic–geometric mean inequality in product/sum form** over an
arbitrary finite index type `n`: for a nonnegative family `f : n → ℝ`,
`D ^ D · ∏ f ≤ (∑ f) ^ D` with `D` the cardinality of `n`. -/
lemma pow_card_mul_prod_le_sum_pow' {n : Type*} [Fintype n] (f : n → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (Fintype.card n : ℝ) ^ Fintype.card n * ∏ i, f i ≤ (∑ i, f i) ^ Fintype.card n := by
  classical
  set e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm with he
  have hprod : ∏ i, f i = ∏ j : Fin (Fintype.card n), f (e j) := (e.prod_comp f).symm
  have hsum : ∑ i, f i = ∑ j : Fin (Fintype.card n), f (e j) := (e.sum_comp f).symm
  rw [hprod, hsum]
  exact pow_card_mul_prod_le_sum_pow (fun j => f (e j)) fun j => hf (e j)

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace–determinant arithmetic–geometric mean inequality** over an arbitrary
finite index type: for a positive semidefinite complex matrix `M` whose index
type has cardinality `D`, `D ^ D · det M ≤ (tr M) ^ D`, both determinant and
trace being real. -/
theorem PosSemidef.pow_card_mul_det_re_le_trace_re_pow' {M : Matrix n n ℂ}
    (hM : M.PosSemidef) :
    (Fintype.card n : ℝ) ^ Fintype.card n * M.det.re ≤ M.trace.re ^ Fintype.card n := by
  classical
  have hdet : M.det.re = ∏ i, hM.1.eigenvalues i := by
    simp only [hM.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  have htr : M.trace.re = ∑ i, hM.1.eigenvalues i := by
    simp only [hM.1.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [hdet, htr]
  exact pow_card_mul_prod_le_sum_pow' hM.1.eigenvalues fun i => hM.eigenvalues_nonneg i

/-- `tr[Aᴴ A] = ∑_{i,j} |A_{ij}| ^ 2`: the trace of `Aᴴ A` collects the squared
moduli of all entries of `A`. -/
theorem trace_conjTranspose_mul_self_re {m p : Type*} [Fintype m] [Fintype p]
    (A : Matrix m p ℂ) :
    (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hcomplex : (Aᴴ * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simpa using RCLike.conj_mul (K := ℂ) (A i j)
  rw [hcomplex, Complex.ofReal_re]

/-- **Determinant bound by the trace of `Aᴴ A`.** For a square complex matrix
`A` whose index type has cardinality `D`,

  `D ^ D · |det A| ^ 2 ≤ tr[Aᴴ A] ^ D`.

In singular values `s₁, …, s_D` of `A` this reads `D ^ D · ∏ᵢ sᵢ ^ 2 ≤
(∑ᵢ sᵢ ^ 2) ^ D`, the arithmetic–geometric mean inequality. -/
theorem pow_card_mul_norm_det_sq_le_trace_conjTranspose_mul_self_pow (A : Matrix n n ℂ) :
    (Fintype.card n : ℝ) ^ Fintype.card n * ‖A.det‖ ^ 2 ≤
      (Aᴴ * A).trace.re ^ Fintype.card n := by
  have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hdet : (Aᴴ * A).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose,
      show star A.det * A.det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) by
        simpa using RCLike.conj_mul (K := ℂ) A.det,
      Complex.ofReal_re]
  simpa only [hdet] using hpsd.pow_card_mul_det_re_le_trace_re_pow'

end Matrix
