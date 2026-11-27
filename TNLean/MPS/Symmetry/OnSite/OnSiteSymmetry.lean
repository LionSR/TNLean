/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Tensor.Gauge.OnSiteSymmetry
import TNLean.MPS.Tensor.Defs

/-!
# On-site symmetry with a character

An on-site symmetry can multiply each tensor letter by the value of a character.
The periodic vector on a chain of length \(N\) then acquires the \(N\)-th power of that value.
The virtual gauge remains a conjugation on the bond space.

Source: Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127, §III.A,
`Papers/2011.12127/TN-Review-main.tex` lines 1147–1157.

## Permutation twists of matrix product state tensors

A monoid acting on the physical index set, that is, a `MulAction G (Fin d)`, twists a tensor by
relabelling its physical index; when `G` is a group, each element acts by a permutation. The
twist by a product is the composite of the twists, and the twist by the identity is trivial.
-/

open MPTensor

section

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ}

/-- On-site symmetry with character \(\varphi\): the tensor twisted by \(g\) is gauge
equivalent to \(\varphi(g) A\). Source: arXiv:2011.12127, §III.A, lines 1147–1157. -/
def IsOnSiteSymmetricUpToCharacter (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (φ : G →* ℂ) : Prop :=
  ∀ g, GaugeEquiv (φ g • A) (twistedTensor A U g)

/-- The periodic coefficient on \(N\) sites acquires the character factor
\(\varphi(g)^N\), including at \(N=0\). Source: arXiv:2011.12127, §III.A, lines 1147–1157. -/
theorem IsOnSiteSymmetricUpToCharacter.mpv_twistedTensor
    {A : MPSTensor d D} {U : G →* Matrix (Fin d) (Fin d) ℂ} {φ : G →* ℂ}
    (h : IsOnSiteSymmetricUpToCharacter A U φ) (g : G) {N : ℕ}
    (s : Fin N → Fin d) :
    mpv (twistedTensor A U g) s = φ g ^ N * mpv A s := by
  rw [← (h g).sameMPV N s]
  exact mpv_smul (φ g) A s

end MPSTensor

end

section

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

end
