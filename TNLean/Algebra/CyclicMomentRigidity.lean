/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Basic.Complex.Basic

/-!
# Multiplicativity from short reflected moments

An adjoint-preserving linear comparison that preserves two-point and three-point
contractions preserves products after projection onto its range. A reflected
four-point contraction forces the remaining product component to vanish.

The algebraic proof uses a linear functional faithful on adjoint squares; no
finite-dimensionality or traciality is needed for this implication.

The argument is self-contained: expanding `τA (star e * e)` for the defect
`e = V x * V y - V (x * y)` and rewriting each of the four terms by one of the
moment hypotheses shows that the expansion vanishes. This is a separate
finite-moment criterion, not a restatement of the fundamental theorem in
arXiv:2204.05940.
-/

namespace LinearMap

variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B]

/-- Two-point, three-point, and reflected four-point contractions determine
multiplicativity when the target functional is faithful on adjoint squares. -/
theorem map_mul_of_reflected_moments (V : B →ₗ[ℂ] A)
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
    (hstar : ∀ x, V (star x) = star (V x))
    (hfaithful : ∀ a, τA (star a * a) = 0 → a = 0)
    (h₂ : ∀ x y, τA (V x * V y) = τB (x * y))
    (h₃ : ∀ x y z, τA (V x * V y * V z) = τB (x * y * z))
    (h₄ : ∀ x y, τA ((star (V y) * star (V x)) * (V x * V y)) =
      τB ((star y * star x) * (x * y))) (x y : B) :
    V (x * y) = V x * V y := by
  symm
  apply sub_eq_zero.mp
  apply hfaithful
  rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub]
  rw [star_mul, h₄]
  rw [← hstar y, ← hstar x, ← hstar (x * y), h₃]
  rw [← mul_assoc (V (star (x * y))) (V x) (V y), h₃, h₂]
  simp only [mul_assoc, sub_self]

end LinearMap
