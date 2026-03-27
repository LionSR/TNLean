/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator Jensen inequality for positive subunital maps

This file states the **operator Jensen inequality** (also known as the
Choi--Davis--Jensen or Hansen--Pedersen inequality) specialized to the
functions `x ↦ x ^ p` and `log`, for positive subunital maps on matrices.

### Background

A function `f : ℝ → ℝ` is *operator convex* on `s ⊆ ℝ` when, for every
dimension `n`, all `n × n` Hermitian matrices `A`, `B` with spectra in `s`,
and every `t ∈ [0, 1]`:

  `f(t A + (1 − t) B) ≤ t f(A) + (1 − t) f(B)`

in the Loewner order, where `f` is applied via the continuous functional
calculus. *Operator concavity* reverses the inequality.

The **operator Jensen inequality** for a positive subunital map `T`
(`T(1) ≤ 1`) then says:

* **convex** `f`: `f(T(A)) ≤ T(f(A))`;
* **concave** `f`: `T(f(A)) ≤ f(T(A))`.

### Status

The three Jensen instances below are `sorry` placeholders. Their proofs
require:

1. Operator concavity of `x ↦ x ^ p` for `p ∈ [0, 1]` — listed as a
   Mathlib TODO in `CFC.Rpow.Order`.
2. Operator convexity of `x ↦ x ^ p` for `p ∈ [1, 2]` — likewise a TODO.
3. Operator concavity of `log` — listed as a TODO in `CFC.ExpLog.Order`.
4. The general Jensen inequality for positive maps — absent from Mathlib.

These are consumed by the Corollary 5.2 proofs in `OperatorMonotone.lean`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 5.1]
* [F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, 2003]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private local instance : NormedRing Mat := Matrix.instL2OpNormedRing
private local instance : NormedAlgebra ℂ Mat := Matrix.instL2OpNormedAlgebra
private local instance : CStarRing Mat := Matrix.instCStarRing
private local instance : PartialOrder Mat := Matrix.instPartialOrder
private local instance : StarOrderedRing Mat := Matrix.instStarOrderedRing
private local instance : NonnegSpectrumClass ℝ Mat :=
  Matrix.instNonnegSpectrumClass
private local instance : CStarAlgebra Mat := CStarAlgebra.mk

/-- **Operator Jensen for concave `rpow`** (Wolf Thm. 5.1 applied to
`x ↦ x ^ p` for `p ∈ [0, 1]`).

For a positive subunital map `T` and `p ∈ [0, 1]`:
  `T(A ^ p) ≤ (T A) ^ p`.

This follows from operator concavity of `x ↦ x ^ p` on `[0, ∞)` for
`p ∈ [0, 1]`, combined with the concave version of the operator Jensen
inequality for positive subunital maps.

**TODO**: prove operator concavity of `x ↦ x ^ p` for `p ∈ [0, 1]`
(see Mathlib `CFC.Rpow.Order` TODO) and the general operator Jensen
inequality for positive maps. -/
theorem IsPositiveMap.rpow_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : Mat} (hA : 0 ≤ A) :
    T (A ^ p) ≤ (T A) ^ p := by
  sorry

/-- **Operator Jensen for convex `rpow`** (Wolf Thm. 5.1 applied to
`x ↦ x ^ p` for `p ∈ [1, 2]`).

For a positive subunital map `T` and `p ∈ [1, 2]`:
  `(T A) ^ p ≤ T(A ^ p)`.

This follows from operator convexity of `x ↦ x ^ p` on `[0, ∞)` for
`p ∈ [1, 2]`, combined with the convex version of the operator Jensen
inequality for positive subunital maps.

**TODO**: prove operator convexity of `x ↦ x ^ p` for `p ∈ [1, 2]`
(see Mathlib `CFC.Rpow.Order` TODO) and the general operator Jensen
inequality for positive maps. -/
theorem IsPositiveMap.rpow_convex_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2) {A : Mat} (hA : 0 ≤ A) :
    (T A) ^ p ≤ T (A ^ p) := by
  sorry

/-- **Operator Jensen for concave `log`** (Wolf Thm. 5.1 applied to `log`).

For a positive subunital map `T` and positive-definite `A`:
  `T(log A) ≤ log(T A)`.

This follows from operator concavity of `log` on `(0, ∞)`, combined
with the concave version of the operator Jensen inequality for positive
subunital maps.

**TODO**: prove operator concavity of `log` (see Mathlib `CFC.ExpLog.Order`
TODO) and the general operator Jensen inequality for positive maps. -/
theorem IsPositiveMap.log_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {A : Mat} (hA : A.PosDef) :
    T (CFC.log A) ≤ CFC.log (T A) := by
  sorry

end
