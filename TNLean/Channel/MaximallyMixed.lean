/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Maximally mixed matrices

This file defines the normalized identity matrix on a finite-dimensional
complex matrix algebra and records its positivity and trace normalization.

## Main declarations

* `Matrix.maximallyMixedOn`: the normalized identity matrix on `Fin d`.
* `Matrix.maximallyMixedOn_posSemidef`: its positive semidefiniteness.
* `Matrix.maximallyMixedOn_posDef`: its positive definiteness when `d` is nonzero.
* `Matrix.maximallyMixedOn_trace`: its trace-one normalization when `d` is nonzero.
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

/-- The maximally mixed matrix on `Fin dA`. -/
noncomputable def maximallyMixedOn {dA : ℕ} : Matrix (Fin dA) (Fin dA) ℂ :=
  (dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)

/-- The maximally mixed matrix is positive semidefinite. -/
theorem maximallyMixedOn_posSemidef {dA : ℕ} :
    (maximallyMixedOn (dA := dA)).PosSemidef := by
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by positivity)

/-- The maximally mixed matrix is positive definite on a nonempty index. -/
theorem maximallyMixedOn_posDef {dA : ℕ} [NeZero dA] :
    (maximallyMixedOn (dA := dA)).PosDef := by
  apply Matrix.PosDef.smul Matrix.PosDef.one
  rw [inv_pos]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)

/-- The maximally mixed matrix has trace one on a nonempty index. -/
theorem maximallyMixedOn_trace {dA : ℕ} [NeZero dA] :
    (maximallyMixedOn (dA := dA)).trace = 1 := by
  simp [maximallyMixedOn, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    (Nat.cast_ne_zero.mpr (NeZero.ne dA) : (dA : ℂ) ≠ 0)]

end Matrix
