/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Products of finite indicator sums

Independent finite choices satisfying one condition each may be counted either
by multiplying the separate counts or by summing the simultaneous indicator.
The identity allows the choice type to depend on the index and holds in every
commutative semiring, including those of characteristic greater than zero.
-/

open scoped BigOperators

namespace Fintype

/-- A product of finite sums of indicators equals the sum of the simultaneous
indicator over dependent choice functions. -/
theorem prod_sum_boole {ι R : Type*} {κ : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [CommSemiring R]
    (P : (i : ι) → κ i → Prop) [∀ i, DecidablePred (P i)] :
    (∏ i, ∑ j : κ i, if P i j then (1 : R) else 0) =
      ∑ f : (i : ι) → κ i, if ∀ i, P i (f i) then (1 : R) else 0 := by
  simp only [prod_sum, prod_boole]

end Fintype
