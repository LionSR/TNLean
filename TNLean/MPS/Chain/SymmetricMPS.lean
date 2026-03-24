import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Matrix.Basic
import TNLean.MPS.Defs

/-!
# Symmetry helpers for MPS tensors

This file introduces the tensor obtained by twisting a physical index with a
matrix representation and proves the identity law. The composition law is left
as a TODO.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {G : Type*} [Monoid G]
variable {d D : ℕ}

/-- Twist an MPS tensor `A` by a physical action `U(g)` on the local index:
`(twistedTensor U A g) i = ∑ j, U(g)ᵢⱼ • A j`. -/
def twistedTensor (U : G →* Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (g : G) :
    MPSTensor d D :=
  fun i => ∑ j, U g i j • A j

@[simp] lemma twistedTensor_one
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) :
    twistedTensor U A 1 = A := by
  ext i a b
  simp [twistedTensor, Matrix.one_apply]

-- TODO (#197 follow-up): add a non-vacuous proof of the composition law
-- `twistedTensor U A (g * h) = twistedTensor U (twistedTensor U A h) g`
-- directly from `Matrix.mul_apply`, avoiding circular assumptions.

end MPSTensor
