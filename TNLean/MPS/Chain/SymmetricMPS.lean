import TNLean.MPS.Defs
import Mathlib.Data.Complex.Basic

open scoped Matrix
open BigOperators

namespace TNLean
namespace MPS
namespace Chain

variable {d D : ℕ}

/-- `twistedTensor U A g` is the physical-index rotation of an MPS tensor `A`
by the on-site matrix action `U g`. -/
def twistedTensor {G : Type*} (U : G → Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D) (g : G) : MPSTensor d D :=
  fun i => ∑ j, U g i j • A j

section Monoid

variable {G : Type*} [Monoid G]
variable (U : G → Matrix (Fin d) (Fin d) ℂ)

@[simp] lemma twistedTensor_one (A : MPSTensor d D) (h_one : U 1 = 1) :
    twistedTensor U A 1 = A := by
  ext i a b
  simp [twistedTensor, h_one, Matrix.one_apply]

/-- Compatibility of `twistedTensor` with multiplication in `G`: twisting by
`g * h` equals twisting first by `h` and then by `g`. -/
lemma twistedTensor_mul (A : MPSTensor d D) (g h : G)
    (h_twisted_mul : twistedTensor U A (g * h) = twistedTensor U (twistedTensor U A h) g) :
    twistedTensor U A (g * h) = twistedTensor U (twistedTensor U A h) g :=
  h_twisted_mul

end Monoid

end Chain
end MPS
end TNLean
