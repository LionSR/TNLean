/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator-monotone corollaries for subunital positive maps

Mathlib already proves operator monotonicity of `x ↦ x^p` for `p ∈ [0,1]` and of
`log`. To derive Wolf Corollary 5.2 from these ingredients, one also needs the
positive-map Jensen inequality from Wolf Theorem 5.13. That intermediate result is
not yet formalized in TNLean, so this file does two things:

* it records the directly available matrix monotonicity lemmas for `rpow` and `log`;
* it registers the three matrix statements of Wolf Corollary 5.2 as
  statement-only placeholders, ready to be upgraded to proved theorems once the
  Jensen infrastructure is available.

### Note on `sorry` placeholders

The 3 `sorry` placeholders below were originally declared as `axiom`s,
which bypass Lean's proof-tracking system. They have been converted to
`theorem ... := by sorry` so that `#print axioms` honestly reports the gaps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 5.2 and
  Theorem 5.13][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private local instance instOperatorMonotoneNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instOperatorMonotoneNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra
private local instance instOperatorMonotoneCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instOperatorMonotonePartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instOperatorMonotoneStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instOperatorMonotoneNonnegSpectrumClass : NonnegSpectrumClass ℝ Mat :=
  Matrix.instNonnegSpectrumClass
private local instance instOperatorMonotoneCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

/-- Matrix-specialized operator monotonicity of `x ↦ x^p` for `p ∈ [0,1]`. -/
theorem matrix_rpow_le_rpow
    {A B : Mat} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hAB : A ≤ B) :
    A ^ p ≤ B ^ p := by
  simpa using (CFC.rpow_le_rpow (A := Mat) hp hAB)

/-- Matrix-specialized operator monotonicity of `log` on positive definite matrices. -/
theorem matrix_log_le_log
    {A B : Mat} (hAB : A ≤ B) (hA : A.PosDef) :
    CFC.log A ≤ CFC.log B := by
  exact CFC.log_le_log (A := Mat) hAB
    (ha := Matrix.isStrictlyPositive_iff_posDef.mpr hA)

/-- Wolf Cor. 5.2(1) in matrix form.

**TODO**: The proof needs the operator-monotone Jensen inequality for positive
subunital maps (Wolf Thm. 5.13), which is not yet in Mathlib.
Currently a `sorry` placeholder. -/
theorem IsPositiveMap.cor52_item1_rpow_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : 1 ≤ p) {A : Mat} (hA : 0 ≤ A) :
    T A ≤ (T (A ^ p)) ^ (1 / p) := by
  sorry

/-- Wolf Cor. 5.2(2) in matrix form.

**TODO**: The proof needs the operator-monotone Jensen inequality for positive
subunital maps (Wolf Thm. 5.13), which is not yet in Mathlib.
Currently a `sorry` placeholder. -/
theorem IsPositiveMap.cor52_item2_rpow_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) {A : Mat} (hA : A.PosDef) :
    (T (A ^ p)) ^ (1 / p) ≤ T A := by
  sorry

/-- Wolf Cor. 5.2(3) in matrix form.

**TODO**: The proof needs the operator-monotone Jensen inequality for positive
subunital maps (Wolf Thm. 5.13) applied to `log`, which is not yet in Mathlib.
Currently a `sorry` placeholder. -/
theorem IsPositiveMap.cor52_item3_log_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {A : Mat} (hA : A.PosDef) :
    T (CFC.log A) ≤ CFC.log (T A) := by
  sorry

end
