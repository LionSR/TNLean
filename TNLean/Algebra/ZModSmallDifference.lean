/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic

/-!
# Integer equality below a cyclic modulus

A nonzero multiple of a modulus has absolute value at least that modulus.
Consequently, projecting two integers whose difference is smaller than the
modulus cannot identify them. No positivity or finiteness assumption on the
cyclic quotient is needed beyond the stated bound on their difference.
-/

namespace ZMod

/-- If the absolute integer difference is smaller than the modulus, equality
after projection to the cyclic quotient is equality of the original integers. -/
theorem intCast_eq_intCast_iff_of_natAbs_sub_lt {n : ℕ} (a b : ℤ)
    (hd : (b - a).natAbs < n) : (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · intro h
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hd)
    exact (sub_eq_zero.mp hz).symm
  · rintro rfl
    simp

end ZMod
