/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.OperatorConvexity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator-monotone corollaries for subunital positive maps

Mathlib already proves operator monotonicity of `x ↦ x^p` for `p ∈ [0,1]` and of
`log`. This file records those matrix-specialized lemmas and proves Wolf
Corollary 5.2 from the operator Jensen inequality
(`OperatorConvexity.lean`).

### Proof strategy for Corollary 5.2

Each item reduces to an instance of the operator Jensen inequality applied
to `A ^ p` with a suitable exponent:

* **Item 1** (`p ≥ 1`): Jensen for concave `x ↦ x^{1/p}` applied to `A^p`,
  using `(A^p)^{1/p} = A` (CFC power composition).
* **Item 2** (`p ∈ [1/2, 1]`): Jensen for convex `x ↦ x^{1/p}` applied
  to `A^p`, using the same power composition.
* **Item 3** (`log`): Direct from Jensen for concave `log`.

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

For a positive subunital map `T`, `p ≥ 1`, and `A ≥ 0`:
  `T(A) ≤ (T(A ^ p)) ^ (1/p)`.

Proof: apply the concave Jensen inequality (from `OperatorConvexity.lean`)
with exponent `1/p ∈ (0, 1]` to the matrix `A ^ p`, then simplify
`(A^p)^{1/p} = A` using the CFC power composition law. -/
theorem IsPositiveMap.cor52_item1_rpow_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : 1 ≤ p) {A : Mat} (hA : 0 ≤ A) :
    T A ≤ (T (A ^ p)) ^ (1 / p) := by
  have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have hp_nn : (0 : ℝ) ≤ p := hp_pos.le
  have h1p_nn : (0 : ℝ) ≤ 1 / p := div_nonneg zero_le_one hp_nn
  have h1p_le1 : 1 / p ≤ 1 := by rwa [div_le_one₀ hp_pos]
  -- (A ^ p) ^ (1 / p) = A via CFC power composition
  have hcomp : (A ^ p) ^ (1 / p) = A := by
    rw [CFC.rpow_rpow_of_exponent_nonneg A p (1 / p) hp_nn h1p_nn]
    rw [show p * (1 / p) = (1 : ℝ) from by field_simp [ne_of_gt hp_pos]]
    exact CFC.rpow_one A
  -- Concave Jensen for rpow with exponent 1/p ∈ [0, 1] applied to A ^ p
  have hJ : T ((A ^ p) ^ (1 / p)) ≤ (T (A ^ p)) ^ (1 / p) :=
    hT.rpow_concave_jensen hSub ⟨h1p_nn, h1p_le1⟩ CFC.rpow_nonneg
  rw [hcomp] at hJ
  exact hJ

/-- Wolf Cor. 5.2(2) in matrix form.

For a positive subunital map `T`, `p ∈ [1/2, 1]`, and positive-definite `A`:
  `(T(A ^ p)) ^ (1/p) ≤ T(A)`.

Proof: apply the convex Jensen inequality (from `OperatorConvexity.lean`)
with exponent `1/p ∈ [1, 2]` to the matrix `A ^ p`, then simplify
`(A^p)^{1/p} = A` using the CFC power composition law. -/
theorem IsPositiveMap.cor52_item2_rpow_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) {A : Mat} (hA : A.PosDef) :
    (T (A ^ p)) ^ (1 / p) ≤ T A := by
  have hp_pos : (0 : ℝ) < p := by linarith [hp.1]
  have hp_nn : (0 : ℝ) ≤ p := hp_pos.le
  have h1p_nn : (0 : ℝ) ≤ 1 / p := div_nonneg zero_le_one hp_nn
  have h1p_ge1 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp_pos]; linarith [hp.2]
  have h1p_le2 : 1 / p ≤ 2 := by rw [div_le_iff₀ hp_pos]; linarith [hp.1]
  have hA_nn : (0 : Mat) ≤ A := by
    rw [Matrix.le_iff]; simpa using hA.posSemidef
  -- (A ^ p) ^ (1 / p) = A via CFC power composition
  have hcomp : (A ^ p) ^ (1 / p) = A := by
    rw [CFC.rpow_rpow_of_exponent_nonneg A p (1 / p) hp_nn h1p_nn (ha₂ := hA_nn)]
    rw [show p * (1 / p) = (1 : ℝ) from by field_simp [ne_of_gt hp_pos]]
    exact CFC.rpow_one A (ha := hA_nn)
  -- Convex Jensen for rpow with exponent 1/p ∈ [1, 2] applied to A ^ p
  have hJ : (T (A ^ p)) ^ (1 / p) ≤ T ((A ^ p) ^ (1 / p)) :=
    hT.rpow_convex_jensen hSub ⟨h1p_ge1, h1p_le2⟩ CFC.rpow_nonneg
  rw [hcomp] at hJ
  exact hJ

/-- Wolf Cor. 5.2(3) in matrix form.

For a positive subunital map `T` and positive-definite `A`:
  `T(log A) ≤ log(T A)`.

This is a direct instance of the concave Jensen inequality for `log`
(from `OperatorConvexity.lean`). -/
theorem IsPositiveMap.cor52_item3_log_of_subunital
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {A : Mat} (hA : A.PosDef) :
    T (CFC.log A) ≤ CFC.log (T A) :=
  hT.log_concave_jensen hSub hA

end
