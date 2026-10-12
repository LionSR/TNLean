/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.LinearMap

/-!
# The same-order involution on the dual of a star-compatible coalgebra

For a coalgebra whose comultiplication preserves the involution, the intrinsic
involution of its scalar-valued dual preserves the order of convolution:
`κ(f * g) = κ(f) * κ(g)`, where `κ(f)(x) = star (f (star x))`.
This is a multiplicative equivalence, not an anti-multiplicative star-ring
structure. Its preservation of the convolution unit follows from bijectivity,
so no separate compatibility condition on the counit is needed.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, lines 1236--1320.
* Molnár et al., arXiv:2204.05940v1, Definition 5.8 and Proposition 5.4.
-/

noncomputable section

open WithConv
open scoped TensorProduct

namespace Coalgebra

variable {R H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid H] [Module R H] [StarAddMonoid H] [StarModule R H]
  [Coalgebra R H]

/-- A star-preserving comultiplication induces a same-order multiplicative
involution of the scalar-valued convolution dual. The tensor factors are not
exchanged. -/
theorem dualStar_mul
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x))
    (f g : WithConv (H →ₗ[R] R)) : star (f * g) = star f * star g := by
  ext x
  simp only [LinearMap.intrinsicStar_apply, LinearMap.convMul_apply, hcomul]
  have ht (t : H ⊗[R] H) :
      star (LinearMap.mul' R R (_root_.TensorProduct.map f.ofConv g.ofConv (star t))) =
        LinearMap.mul' R R
          (_root_.TensorProduct.map (star f).ofConv (star g).ofConv t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add t u ht hu => simp only [star_add, map_add, ht, hu]
  exact ht (comul x)

/-- The involution of the convolution dual, regarded as a multiplicative
equivalence. Its unit law follows from the same-order product law and
involutivity. -/
def dualStarMulEquiv
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x)) :
    WithConv (H →ₗ[R] R) ≃* WithConv (H →ₗ[R] R) where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' := dualStar_mul hcomul

/-- Counit compatibility follows from the comultiplication compatibility:
the intrinsic involution fixes the convolution unit. -/
theorem dualStar_one
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x)) :
    star (1 : WithConv (H →ₗ[R] R)) = 1 :=
  (dualStarMulEquiv hcomul).map_one

end Coalgebra
