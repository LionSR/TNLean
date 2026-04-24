/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.OperatorConvexity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace convexity and concavity consequences

This file restates trace convexity/concavity consequences for matrix power
functions in the Schwarz chapter namespace.

## Main results

* `trace_rpow_concave` — `A ↦ Re Tr(A ^ p)` is concave on PSD
  matrices for `p ∈ [0, 1]`.
* `trace_rpow_convex` — `A ↦ Re Tr(A ^ p)` is convex on PSD
  matrices for `p ∈ [1, 2]`.
### Status

* `trace_rpow_concave`, `trace_rpow_convex` are proved in
  `TNLean.Analysis.OperatorConvexity` using the spectral theorem and the
  scalar Jensen inequality. This file restates them in the present file,
  for downstream use.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Ch. 5]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private local instance instAndoLiebNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instAndoLiebNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra
private local instance instAndoLiebCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instAndoLiebPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instAndoLiebStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instAndoLiebNonnegSpectrumClass : NonnegSpectrumClass ℝ Mat :=
  Matrix.instNonnegSpectrumClass
private local instance instAndoLiebCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

/-! ## Trace convexity and concavity of matrix powers -/

/-- **Trace concavity of `rpow`** for `p ∈ [0, 1]`.

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `t · Re Tr(A₁ ^ p) + (1 − t) · Re Tr(A₂ ^ p) ≤
     Re Tr((t • A₁ + (1 − t) • A₂) ^ p)`.

Proved in `TNLean.Analysis.OperatorConvexity` via the spectral theorem
and the scalar Jensen inequality. -/
theorem trace_rpow_concave
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * (trace (A₁ ^ p)).re + (1 - t) * (trace (A₂ ^ p)).re ≤
      (trace ((t • A₁ + (1 - t) • A₂) ^ p)).re :=
  TNLean.trace_rpow_concave hp hA₁ hA₂ ht

/-- **Trace convexity of `rpow`** for `p ∈ [1, 2]`.

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `Re Tr((t • A₁ + (1 − t) • A₂) ^ p) ≤
     t · Re Tr(A₁ ^ p) + (1 − t) · Re Tr(A₂ ^ p)`.

Proved in `TNLean.Analysis.OperatorConvexity` via the spectral theorem
and the scalar Jensen inequality. -/
theorem trace_rpow_convex
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (trace ((t • A₁ + (1 - t) • A₂) ^ p)).re ≤
      t * (trace (A₁ ^ p)).re + (1 - t) * (trace (A₂ ^ p)).re :=
  TNLean.trace_rpow_convex hp hA₁ hA₂ ht

end
