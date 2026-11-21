/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# The tensor type

A translation-invariant matrix product tensor with physical basis `α` and bond basis `β` is
one matrix on the bond space for each physical basis element. As a family of matrices indexed
by `α` it is a finite Kraus family, so every statement about Kraus families applies to it
without a conversion.

## Main definitions

* `MPTensor α β` — the tensor with physical basis `α` and bond basis `β`.
* `MPSTensor d D` — the tensor of local dimension `d` and bond dimension `D`, the case
  `α = Fin d`, `β = Fin D`.

## Implementation notes

Both are abbreviations, not structures: the Kraus statements of QICLean, stated for families
`ι → Matrix n n ℂ`, apply to a tensor directly, and `MPSTensor d D` is by definition the
family `Fin d → Matrix (Fin D) (Fin D) ℂ`. The design is `docs/tensor_type_unification.md`.

## References

* [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) (Cirac, Pérez-García, Schuch,
  Verstraete), Section 2, the tensors of a translation-invariant matrix product state.
-/

universe u v

/-- A matrix product tensor with physical basis `α` and bond basis `β`: one matrix on the bond
space for each physical basis element. As a family of matrices indexed by `α` it is a finite
Kraus family, and every Kraus statement applies to it unchanged. -/
abbrev MPTensor (α : Type u) (β : Type v) : Type (max u v) := α → Matrix β β ℂ

/-- The tensor of local dimension `d` and bond dimension `D`. -/
abbrev MPSTensor (d D : ℕ) := MPTensor (Fin d) (Fin D)
