/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.End

/-!
# Spin flip and the cyclic controlled-Z exponent

The global spin flip and the nearest-neighbor phase exponent on a binary periodic chain.
These operations are independent of a choice of matrix product tensor.
-/

open scoped BigOperators

namespace CZXCompression

/-- The global spin flip `X^{⊗ N}` on periodic configurations of `N` qubits. -/
def spinFlip (N : ℕ) : Equiv.Perm (Fin N → Fin 2) :=
  Equiv.piCongrRight fun _ ↦ Fin.revPerm

theorem spinFlip_apply {N : ℕ} (t : Fin N → Fin 2) (n : Fin N) :
    spinFlip N t n = (t n).rev := rfl

/-- The global spin flip is an involution. -/
theorem spinFlip_mul_self {N : ℕ} : spinFlip N * spinFlip N = 1 := by
  ext t n
  simp [Equiv.Perm.mul_apply, spinFlip_apply]

variable {N : ℕ} [NeZero N]

/-- The controlled-`Z` exponent of a periodic configuration: the number of neighboring pairs
of ones, the site after the last being the first. -/
def czExponent (t : Fin N → Fin 2) : ℕ :=
  ∑ n, (t n).val * (t (n + 1)).val

end CZXCompression
