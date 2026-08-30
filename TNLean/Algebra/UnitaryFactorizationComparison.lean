/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Comparison of unitary factorizations

Given a family of unitary operators indexed by pairs, this file compares two
members by multiplying the first by the inverse of the second.  The orientation
is

`unitaryFactorizationComparison R a b c d = (R c d)⁻¹ * R a b`.

For unitary matrices, the inverse is the adjoint.  Thus this is precisely the
operator $\lambda_{a,b}^{c,d} = (\lambda^R_{c,d})^\dagger\lambda^R_{a,b}$ in
the corollary following FBC25, Proposition `prop:3`
(arXiv:2502.20257, lines 2782--2821).

The algebra does not use equalities between products of the indices.  Such
equalities only determine which factorizations are compared in applications.
-/

namespace Matrix

variable {ι n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜] [StarRing 𝕜]

/-- The comparison of the unitary operators indexed by `(a, b)` and `(c, d)`,
with the reference pair `(c, d)` on the left.

This is the orientation
$\lambda_{a,b}^{c,d} = (\lambda^R_{c,d})^\dagger\lambda^R_{a,b}$ from the
corollary following FBC25, Proposition `prop:3`
(arXiv:2502.20257, lines 2782--2821). -/
def unitaryFactorizationComparison
    (R : ι → ι → Matrix.unitaryGroup n 𝕜) (a b c d : ι) :
    Matrix.unitaryGroup n 𝕜 :=
  (R c d)⁻¹ * R a b

/-- The matrix underlying a unitary factorization comparison is the adjoint of
the reference operator multiplied by the source operator. -/
theorem unitaryFactorizationComparison_coe
    (R : ι → ι → Matrix.unitaryGroup n 𝕜) (a b c d : ι) :
    (unitaryFactorizationComparison R a b c d : Matrix n n 𝕜) =
      star (R c d : Matrix n n 𝕜) * (R a b : Matrix n n 𝕜) :=
  rfl

/-- Comparing a unitary factorization with itself gives the identity. -/
@[simp]
theorem unitaryFactorizationComparison_self
    (R : ι → ι → Matrix.unitaryGroup n 𝕜) (a b : ι) :
    unitaryFactorizationComparison R a b a b = 1 := by
  simp only [unitaryFactorizationComparison, inv_mul_cancel]

/-- Unitary factorization comparisons compose through an intermediate pair in
the source orientation.  This is the composition law in the corollary
following FBC25, Proposition `prop:3`
(arXiv:2502.20257, lines 2782--2821). -/
theorem unitaryFactorizationComparison_trans
    (R : ι → ι → Matrix.unitaryGroup n 𝕜) (a b c d f g : ι) :
    unitaryFactorizationComparison R a b f g =
      unitaryFactorizationComparison R c d f g *
        unitaryFactorizationComparison R a b c d := by
  simp only [unitaryFactorizationComparison, mul_assoc, mul_inv_cancel_left]

/-- If the reference operator is the identity, comparison against it recovers
the source operator. -/
theorem unitaryFactorizationComparison_of_reference_eq_one
    (R : ι → ι → Matrix.unitaryGroup n 𝕜) (a b c d : ι)
    (href : R c d = 1) :
    unitaryFactorizationComparison R a b c d = R a b := by
  simp only [unitaryFactorizationComparison, href, inv_one, one_mul]

/-- If the identity-prefixed operators are normalized to one, the right-fusion operator
indexed by `(g, h)` equals its comparison with `(1, g * h)`.

This is $\lambda^R_{g,h} = \lambda_{g,h}^{e,gh}$ in the corollary following
FBC25, Proposition `prop:3` (arXiv:2502.20257, lines 2782--2821). -/
theorem unitaryFactorizationComparison_right_reference
    {G : Type*} [Group G] (R : G → G → Matrix.unitaryGroup n 𝕜)
    (hR : ∀ x, R 1 x = 1) (g h : G) :
    R g h = unitaryFactorizationComparison R g h 1 (g * h) := by
  exact
    (unitaryFactorizationComparison_of_reference_eq_one R g h 1 (g * h) (hR (g * h))).symm

end Matrix
