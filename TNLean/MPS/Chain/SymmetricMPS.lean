import TNLean.MPS.Defs

/-!
# Symmetry helpers for chain MPS tensors

This module defines the symmetry-twisted tensor construction `twistedTensor` and
proves the identity law `twistedTensor_one`.

TODO: add a direct proof of the composition law (`twistedTensor_mul`).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Twist an MPS tensor by an on-site matrix action on the physical index. -/
def twistedTensor (U : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j, U i j • A j

@[simp] lemma twistedTensor_one (A : MPSTensor d D) :
    twistedTensor (1 : Matrix (Fin d) (Fin d) ℂ) A = A := by
  funext i
  simp [twistedTensor, Matrix.one_apply]

end MPSTensor
