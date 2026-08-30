/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactors

/-!
# Trace-normalized weights for paper-facing shift source factors

This module defines the scalar identity weight
\[
W_d = d^{-1} I_d
\]
used by the corrected paper-facing source-factor calculations for the cyclic
shift examples.  It is independent of the supplied identity-weight mixed
kernels in `ShiftSourceFactors` and does not identify those kernels with the
paper gates.

The squared-dimension abbreviation records the weight on the product bond
space of the tensor-product shift examples.
-/

open scoped ComplexOrder

namespace MPOTensor

/-- The trace-normalized scalar identity matrix on a `d`-dimensional space. -/
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

/-- The trace-normalized identity weight on the `d²`-dimensional product bond
space used by the tensor-product shift examples. -/
noncomputable abbrev shiftPaperWeightSquared (d : ℕ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  shiftPaperWeight (d * d)

/-- The `d²` weight is the scalar identity `(d²)⁻¹ I`. -/
theorem shiftPaperWeightSquared_eq (d : ℕ) :
    shiftPaperWeightSquared d =
      (d * d : ℂ)⁻¹ • (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) := by
  simp [shiftPaperWeightSquared, shiftPaperWeight, Nat.cast_mul]

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
