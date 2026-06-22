/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.PerronFrobenius.RankOne

/-!
# Trace inequalities for positive semidefinite matrices

This module records finite-dimensional matrix trace inequalities used in
Wolf's discussion of Lorentz cones for positive maps. The first result is the
forward implication in Wolf, Chapter 3, Proposition 3.9: if `A ≥ 0`, then
`tr(A^2) ≤ tr(A)^2`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma ofReal_sq_re (r : ℝ) : Complex.re ((r : ℂ) ^ 2) = r ^ 2 := by
  have hpow : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow r 2).symm
  calc
    Complex.re ((r : ℂ) ^ 2) = Complex.re (((r ^ 2 : ℝ) : ℂ)) :=
      congrArg Complex.re hpow
    _ = r ^ 2 := Complex.ofReal_re _

/-- Wolf Chapter 3, Proposition 3.9, forward implication.

If `A` is positive semidefinite, then the real trace of `A ^ 2` is bounded by
the square of the real trace of `A`. In eigenvalues this is
`∑ᵢ λᵢ^2 ≤ (∑ᵢ λᵢ)^2`, with all `λᵢ ≥ 0`. -/
theorem PosSemidef.trace_sq_re_le_trace_re_sq
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Matrix.trace (A ^ 2)).re ≤ (Matrix.trace A).re ^ 2 := by
  let hH := hA.isHermitian
  set lam : n → ℝ := hH.eigenvalues with hlam
  have htrace : (Matrix.trace A).re = ∑ i, lam i := by
    have h := hH.trace_eq_sum_eigenvalues
    change Matrix.trace A = ∑ i, (lam i : ℂ) at h
    rw [h]
    simp
  have htrace2 : (Matrix.trace (A ^ 2)).re = ∑ i, lam i ^ 2 := by
    have h := hH.trace_sq_eq_sum_eigenvalues_sq
    change Matrix.trace (A ^ 2) = ∑ i, (lam i : ℂ) ^ 2 at h
    rw [h]
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => ofReal_sq_re (lam i))
  rw [htrace, htrace2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := lam)
    (fun i _ => by
      rw [hlam]
      exact hA.eigenvalues_nonneg i)

end Matrix
