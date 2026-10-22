/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.PartyPartition

/-!
# Memory vectors under equality of register lists

The canonical identification of equal register lists preserves the underlying
memory vector. The same identification preserves elementary tensors when each
factor is transported separately.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 409–450.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.Lattice.PartyCircuit.Layout
variable {P : Type}

/-- Equality of register lists preserves the underlying memory vector. -/
theorem memCongr_apply_heq {a b : Layout P} (h : a = b) (x : Mem a) :
    HEq (memCongr h x) x := by
  cases h
  rfl

/-- Transporting two memory vectors along layout equalities preserves their tensor. -/
theorem memCongr_tmul_heq {a b c d : Layout P} (ha : a = b) (hc : c = d)
    (x : Mem a) (y : Mem c) :
    HEq (memCongr ha x ⊗ₜ[ℂ] memCongr hc y) (x ⊗ₜ[ℂ] y) := by
  cases ha
  cases hc
  rfl

/-- Prepending one register vector to memory vectors of equal register lists preserves
their equality. -/
theorem cons_tmul_heq (r : Reg P) {a b : Layout P} (h : a = b) (u : r.space)
    {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq (u ⊗ₜ[ℂ] x : Mem (r :: a)) (u ⊗ₜ[ℂ] y : Mem (r :: b)) := by
  cases h
  cases hxy
  rfl

end TNLean.Lattice.PartyCircuit.Layout
