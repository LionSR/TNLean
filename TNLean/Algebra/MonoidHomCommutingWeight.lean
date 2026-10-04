/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Commute.Hom

/-!
# Combining commuting weights between representation factors

A power of a weight commuting with a representation can be moved past the
first representation factor. This is the elementary algebra used to combine
endpoint weights in SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
-/

namespace MonoidHom
variable {M N : Type*} [Monoid M] [Monoid N]

/-- A commuting weight leaves only the product of the two represented elements.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem mul_commuting_pow_mul (U : M →* N) (W : N) (hc : ∀ a, Commute W (U a))
    (n : ℕ) (a b : M) : U a * W ^ n * U b = W ^ n * U (a * b) := by
  rw [((hc a).pow_left n).eq.symm, mul_assoc, ← map_mul]

/-- Two adjacent endpoint weights combine to the square of the weight.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem mul_weight_mul_weight_mul (U : M →* N) (W : N)
    (hc : ∀ a, Commute W (U a)) (a b : M) :
    (U a * W) * (W * U b) = W ^ 2 * U (a * b) := by
  simpa only [pow_two, mul_assoc] using U.mul_commuting_pow_mul W hc 2 a b
end MonoidHom
