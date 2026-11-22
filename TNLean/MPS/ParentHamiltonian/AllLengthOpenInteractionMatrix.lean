/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator

/-!
# Open interaction Hamiltonians on chains shorter than the range

On a chain shorter than the interaction range there is no window, so the Hamiltonian of the
open-chain translates of a local matrix vanishes.

Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12).
-/

open scoped Matrix BigOperators
open ManyBody.Interaction (chainTranslates hamiltonian_chainTranslates_eq_sum_range)

namespace MPSTensor
variable {d R N : ℕ}

/-- The open matrix sum vanishes when the interval is shorter than its
interaction range. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12), the empty interaction sum. -/
theorem hamiltonian_chainTranslates_eq_zero_of_length_lt
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hN : N < R) :
    (chainTranslates R N h).hamiltonian = 0 := by
  have hEmpty : N + 1 - R = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp [hamiltonian_chainTranslates_eq_sum_range, hEmpty]

end MPSTensor

