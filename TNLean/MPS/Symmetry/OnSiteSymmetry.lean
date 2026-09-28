/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs

/-!
# Permutation twists of matrix product state tensors

A monoid acting on the physical index set, that is, a `MulAction G (Fin d)`, twists a tensor by
relabelling its physical index; when `G` is a group, each element acts by a permutation. The
twist by a product is the composite of the twists, and the twist by the identity is trivial.
-/

open scoped Matrix

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ} [MulAction G (Fin d)]

/-- Tensor twisted by the physical action at the element `g`.

This is the index twist `A^{σ_g}` defined by `(TwistedTensor A g) i = A (g • i)`. -/
def TwistedTensor (A : MPSTensor d D) (g : G) : MPSTensor d D :=
  fun i => A (g • i)

@[simp] lemma TwistedTensor_apply (A : MPSTensor d D) (g : G) (i : Fin d) :
    TwistedTensor A g i = A (g • i) := rfl

/-- Twisting by the identity is trivial. -/
@[simp] lemma TwistedTensor_one (A : MPSTensor d D) :
    TwistedTensor A (1 : G) = A := by
  funext i
  simp [TwistedTensor]

/-- Composition law for twists: twisting by `g * h` equals twisting by `g` then
by `h`. -/
lemma TwistedTensor_mul (A : MPSTensor d D) (g h : G) :
    TwistedTensor A (g * h) = TwistedTensor (TwistedTensor A g) h := by
  funext i
  simp [TwistedTensor, mul_smul]

end MPSTensor
