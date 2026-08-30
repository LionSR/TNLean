/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity

/-!
# Trace-normalized weights for paper-facing shift source factors

CPSV17 fixes the Canonical Form II right fixed point $\rho$ to be positive
and trace one in arXiv:1703.09188, `Erightleft` (lines 269--281). For the
corrected supplied cyclic-shift witnesses, this fixed point is
\[
W_d = d^{-1} I_d.
\]
This module packages that specialization and its elementary matrix properties.
It is independent of the identity-weight mixed kernels in
`ShiftSourceFactors` and does not identify those kernels with the paper gates
of `uuvv` (lines 532--543).

A tensor product of two shifts has product bond dimension $d^2$, so its fixed
weight is $W_{d^2} = (d^2)^{-1} I_{d^2}$.
-/

open scoped ComplexOrder

namespace MPOTensor

/-- The scalar identity weight on the shift bond space, normalized to trace
one when `d` is nonzero.

This is the scalar specialization of the CFII right fixed point in
arXiv:1703.09188, `Erightleft` (lines 269--280), as used by the source metric in
`Y1Y1X1X1` (lines 487--495). -/
noncomputable def shiftPaperWeight (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The trace-normalized identity weight is positive semidefinite in every
dimension, including dimension zero. -/
theorem shiftPaperWeight_posSemidef (d : ℕ) :
    (shiftPaperWeight d).PosSemidef := by
  exact Matrix.PosSemidef.one.smul (by positivity)

/-- In positive dimension, the trace-normalized identity weight is positive
definite. -/
theorem shiftPaperWeight_posDef (d : ℕ) [NeZero d] :
    (shiftPaperWeight d).PosDef := by
  have hd : (0 : ℂ) < (d : ℂ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  exact Matrix.PosDef.one.smul (inv_pos.mpr hd)

/-- In positive dimension, the trace-normalized identity weight has trace one. -/
@[simp] theorem shiftPaperWeight_trace (d : ℕ) [NeZero d] :
    Matrix.trace (shiftPaperWeight d) = 1 := by
  rw [shiftPaperWeight, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

/-- The scalar trace-one identity weight on the `d²`-dimensional product bond
space used by the tensor-product shift examples of arXiv:1703.09188,
`threeMPU` (lines 1988--1994), when `d` is nonzero. -/
noncomputable abbrev shiftPaperWeightSquared (d : ℕ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  shiftPaperWeight (d * d)

/-- The `d²` weight is the scalar identity `(d²)⁻¹ I`. -/
theorem shiftPaperWeightSquared_eq (d : ℕ) :
    shiftPaperWeightSquared d =
      (d * d : ℂ)⁻¹ • (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) := by
  rw [shiftPaperWeightSquared, shiftPaperWeight, Nat.cast_mul]

/-- The `d²` weight is positive semidefinite in every dimension. -/
theorem shiftPaperWeightSquared_posSemidef (d : ℕ) :
    (shiftPaperWeightSquared d).PosSemidef :=
  shiftPaperWeight_posSemidef (d * d)

/-- In positive dimension, the `d²` weight is positive definite. -/
theorem shiftPaperWeightSquared_posDef (d : ℕ) [NeZero d] :
    (shiftPaperWeightSquared d).PosDef :=
  shiftPaperWeight_posDef (d * d)

/-- In positive dimension, the `d²` weight has trace one. -/
@[simp] theorem shiftPaperWeightSquared_trace (d : ℕ) [NeZero d] :
    Matrix.trace (shiftPaperWeightSquared d) = 1 :=
  shiftPaperWeight_trace (d * d)

end MPOTensor
