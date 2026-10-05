/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ProductVector

/-!
# GHZ-type vectors

The weighted superposition of constant computational-basis vectors used in
unitary-circuit obstructions and measurement-assisted state preparation.
-/

open scoped BigOperators

namespace QuantumCircuit

/-! ### The GHZ-type state -/

section State

variable {b : ℕ}

/-- The GHZ-like state `|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` on `M` sites of dimension `b`
(arXiv:2307.01696, the paragraph after eq. (19)): its amplitude at `s` is `∑ⱼ αⱼ`
times the product of the coordinates `s k` of the basis vector `|j⟩`. -/
def ghzState {M : ℕ} (α : Fin b → ℂ) (s : Fin M → Fin b) : ℂ :=
  ∑ j, α j * ∏ k, (Pi.single j 1 : Fin b → ℂ) (s k)

/-- The amplitude of `|χ_M⟩` at `s` is `α (s 0)` if all the values `s k` are equal, and `0`
otherwise. -/
theorem ghzState_apply {M : ℕ} [NeZero M] (α : Fin b → ℂ) (s : Fin M → Fin b) :
    ghzState α s = if ∀ k, s k = s 0 then α (s 0) else 0 := by
  classical
  simp only [ghzState, Pi.single_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  rw [Finset.sum_eq_single (s 0)]
  · split_ifs <;> simp
  · intro j _ hj
    rw [ite_eq_right fun h => hj (h 0).symm, mul_zero]
  · simp

end State

end QuantumCircuit
