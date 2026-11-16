/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Fin.Basic

/-!
# The two summands of `Fin (m + n)` are disjoint

An index of `Fin (m + n)` coming from the first summand by `Fin.castAdd` is
never an index coming from the second summand by `Fin.natAdd`. This is the
disjointness of the two coordinate blocks of a direct sum of bond spaces.

## Main statements

* `Fin.castAdd_ne_natAdd`: a first-summand index differs from every
  second-summand index.
* `Fin.natAdd_ne_castAdd`: the same with the two sides exchanged.
-/

namespace Fin

/-- An index from the first summand of `Fin (m + n)` is not an index from the
second summand. -/
theorem castAdd_ne_natAdd {m n : ℕ} (a : Fin m) (b : Fin n) :
    Fin.castAdd n a ≠ Fin.natAdd m b := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- An index from the second summand of `Fin (m + n)` is not an index from the
first summand. -/
theorem natAdd_ne_castAdd {m n : ℕ} (b : Fin n) (a : Fin m) :
    Fin.natAdd m b ≠ Fin.castAdd n a :=
  (castAdd_ne_natAdd a b).symm

end Fin
