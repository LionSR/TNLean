/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Square roots in a C⋆-algebra are `1/2`-Hölder

For positive elements `a` and `b` of a C⋆-algebra, `‖√a - √b‖ ≤ √‖a - b‖`. This is the operator
inequality `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` for positive semidefinite matrices that arXiv:2103.13367,
Supplemental Material, eq. `intermediate`, quotes from Bhatia.

## Main declarations

* `IsSelfAdjoint.norm_le_of_le_algebraMap` — `-r ≤ a ≤ r` bounds `‖a‖` by `r`.
* `CFC.norm_sqrt_sub_sqrt_le` — `‖√a - √b‖ ≤ √‖a - b‖` for `a, b ≥ 0`.
-/

/-- A selfadjoint element with `-r ≤ a ≤ r` has norm at most `r`. -/
theorem IsSelfAdjoint.norm_le_of_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -algebraMap ℝ A r ≤ a) : ‖a‖ ≤ r := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim a 0, norm_zero]; exact hr
  have hup := (le_algebraMap_iff_spectrum_le (R := ℝ) ha).1 h₁
  have hlo := (algebraMap_le_iff_le_spectrum (R := ℝ) ha).1 (by rwa [map_neg])
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with h | h
  · exact hup _ h
  · linarith [hlo _ h]

/-- Upper half of `CFC.norm_sqrt_sub_sqrt_le`: `√a - √b ≤ √‖a - b‖`. -/
theorem CFC.sqrt_sub_sqrt_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A (Real.sqrt ‖a - b‖) := by
  set ε := ‖a - b‖
  set S := CFC.sqrt b
  set c := algebraMap ℝ A (Real.sqrt ε)
  have h₁ : a ≤ b + algebraMap ℝ A ε :=
    sub_le_iff_le_add'.1
      (IsSelfAdjoint.le_algebraMap_norm_self (a - b) (ha.isSelfAdjoint.sub hb.isSelfAdjoint))
  have hS : 0 ≤ S := CFC.sqrt_nonneg b
  have hcS : c * S = Real.sqrt ε • S := (Algebra.smul_def _ _).symm
  have hSc : S * c = Real.sqrt ε • S := by rw [← Algebra.commutes, hcS]
  have hcc : c * c = algebraMap ℝ A ε := by
    rw [← map_mul, Real.mul_self_sqrt (norm_nonneg _)]
  have hc : 0 ≤ c := by
    simp only [c, Algebra.algebraMap_eq_smul_one]
    exact smul_nonneg (Real.sqrt_nonneg _) zero_le_one
  have hsq : b + algebraMap ℝ A ε ≤ (S + c) ^ 2 := by
    have hexp : (S + c) ^ 2 = b + algebraMap ℝ A ε + (Real.sqrt ε • S + Real.sqrt ε • S) := by
      rw [sq, add_mul, mul_add, mul_add, CFC.sqrt_mul_sqrt_self b hb, hcS, hSc, hcc]
      abel
    rw [hexp]
    exact le_add_of_nonneg_right
      (add_nonneg (smul_nonneg (Real.sqrt_nonneg _) hS) (smul_nonneg (Real.sqrt_nonneg _) hS))
  have h₂ : CFC.sqrt a ≤ S + c :=
    calc CFC.sqrt a ≤ CFC.sqrt (b + algebraMap ℝ A ε) := CFC.sqrt_le_sqrt _ _ h₁
      _ ≤ CFC.sqrt ((S + c) ^ 2) := CFC.sqrt_le_sqrt _ _ hsq
      _ = S + c := CFC.sqrt_sq (S + c) (add_nonneg hS hc)
  exact sub_le_iff_le_add'.2 h₂

/-- **Square roots are `1/2`-Hölder**: for `a, b ≥ 0` in a C⋆-algebra,
`‖√a - √b‖ ≤ √‖a - b‖`.

arXiv:2103.13367, eq. `intermediate` (the bound `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` for `X, Y ≥ 0`,
quoted there from Bhatia). -/
theorem CFC.norm_sqrt_sub_sqrt_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ Real.sqrt ‖a - b‖ := by
  refine IsSelfAdjoint.norm_le_of_le_algebraMap
    ((CFC.sqrt_nonneg a).isSelfAdjoint.sub (CFC.sqrt_nonneg b).isSelfAdjoint)
    (Real.sqrt_nonneg _) (CFC.sqrt_sub_sqrt_le_algebraMap ha hb) ?_
  have h := CFC.sqrt_sub_sqrt_le_algebraMap hb ha
  rw [norm_sub_rev] at h
  rw [neg_le, neg_sub]
  exact h
