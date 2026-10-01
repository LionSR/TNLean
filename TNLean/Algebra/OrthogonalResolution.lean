/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OrthogonalProjection

/-!
# Multiplication in an orthogonal resolution of the identity

The cyclic-sector calculations in arXiv:1708.00029, Lemma 6, use both the
equal-index and distinct-index cases of the projection multiplication rule.

The statement is generic matrix analysis and belongs beside
`orthogonalProjection_mul_eq_zero_of_sum_eq_one` in
`QICLean/Algebra/OrthogonalProjection.lean`; it is housed here until that library
is next released and the dependency is bumped.
-/

open scoped Matrix BigOperators

/-- Orthogonal projections summing to the identity have the Kronecker-delta
multiplication table. Source: arXiv:1708.00029, paragraph following `lem:unique-dec`. -/
theorem orthogonalProjection_mul_eq_ite_of_sum_eq_one {D m : ℕ}
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (u v : Fin m) : P u * P v = if u = v then P u else 0 := by
  split_ifs with huv
  · subst v
    exact (hproj u).2
  · exact orthogonalProjection_mul_eq_zero_of_sum_eq_one P hproj hsum huv
