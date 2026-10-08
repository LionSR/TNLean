/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QICLean.Analysis.SqrtHolder

/-!
# Square roots in a C⋆-algebra are `1/2`-Hölder

For positive elements `a` and `b` of a C⋆-algebra, `‖√a - √b‖ ≤ √‖a - b‖`. This is the operator
inequality `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` for positive semidefinite matrices that arXiv:2103.13367,
Supplemental Material, eq. (26), quotes from Bhatia.

The upper half follows from a one-sided bound with a scalar floor. If `b ≥ c ≥ 0` and
`‖a - b‖ ≤ 2 s √c + s²` with `s ≥ 0`, then `a ≤ (√b + s)²`, so `√a - √b ≤ s` by operator
monotonicity of the square root. The Hölder bound is the case `c = 0`, `s = √‖a - b‖`; the
Lipschitz bound of `TNLean.Algebra.CStarSqrtLipschitz` uses a positive floor.

## Main declarations

* `IsSelfAdjoint.norm_le_of_le_algebraMap` — `-r ≤ a ≤ r` bounds `‖a‖` by `r`.
* `CFC.algebraMap_sqrt_le_sqrt` — `c ≤ b` gives `√c ≤ √b`.
* `CFC.sqrt_sub_sqrt_le_algebraMap_of_le` — `√a - √b ≤ s` from a scalar floor `c ≤ b`.
* The Hölder bound `CFC.norm_sqrt_sub_sqrt_le` itself is `QICLean.Analysis.SqrtHolder`.
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

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A scalar lower bound passes to square roots: `c ≤ b` gives `√c ≤ √b`. -/
theorem algebraMap_sqrt_le_sqrt {b : A} {c : ℝ} (hc : 0 ≤ c) (h : algebraMap ℝ A c ≤ b) :
    algebraMap ℝ A (Real.sqrt c) ≤ CFC.sqrt b := by
  have h0 : 0 ≤ algebraMap ℝ A (Real.sqrt c) := by
    simpa using algebraMap_mono A (Real.sqrt_nonneg c)
  calc algebraMap ℝ A (Real.sqrt c) = CFC.sqrt (algebraMap ℝ A (Real.sqrt c) ^ 2) :=
        (CFC.sqrt_sq _ h0).symm
    _ ≤ CFC.sqrt b := CFC.sqrt_le_sqrt _ _ (by rwa [← map_pow, Real.sq_sqrt hc])

/-- The square of `√b + s` for a real scalar `s`. -/
theorem sq_sqrt_add_algebraMap {b : A} (hb : 0 ≤ b) (s : ℝ) :
    (CFC.sqrt b + algebraMap ℝ A s) ^ 2 =
      b + (s • CFC.sqrt b + s • CFC.sqrt b) + algebraMap ℝ A (s * s) := by
  rw [sq, add_mul, mul_add, mul_add, CFC.sqrt_mul_sqrt_self b hb, ← Algebra.smul_def,
    ← Algebra.commutes, ← Algebra.smul_def, ← map_mul]
  abel

/-- Upper half of `norm_sqrt_sub_sqrt_le` and of `norm_sqrt_sub_sqrt_le_div`: if `b ≥ c ≥ 0` and
`s ≥ 0` satisfies `‖a - b‖ ≤ 2 s √c + s²`, then `√a - √b ≤ s`. -/
theorem sqrt_sub_sqrt_le_algebraMap_of_le {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {c s : ℝ}
    (hc : 0 ≤ c) (hcb : algebraMap ℝ A c ≤ b) (hs : 0 ≤ s)
    (hε : ‖a - b‖ ≤ 2 * s * Real.sqrt c + s * s) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A s := by
  have hS := algebraMap_sqrt_le_sqrt hc hcb
  have hC : 0 ≤ algebraMap ℝ A s := by simpa using algebraMap_mono A hs
  have hsS : algebraMap ℝ A (s * Real.sqrt c) ≤ s • CFC.sqrt b := by
    rw [map_mul, ← Algebra.smul_def]
    exact smul_le_smul_of_nonneg_left hS hs
  have h₁ : a ≤ b + algebraMap ℝ A ‖a - b‖ :=
    sub_le_iff_le_add'.1
      (IsSelfAdjoint.le_algebraMap_norm_self (a - b) (ha.isSelfAdjoint.sub hb.isSelfAdjoint))
  have h₂ : a ≤ (CFC.sqrt b + algebraMap ℝ A s) ^ 2 := by
    rw [sq_sqrt_add_algebraMap hb]
    refine h₁.trans ?_
    rw [add_assoc]
    refine add_le_add_right ?_ b
    calc algebraMap ℝ A ‖a - b‖
        ≤ algebraMap ℝ A (s * Real.sqrt c + s * Real.sqrt c + s * s) :=
          algebraMap_mono A (by linarith)
      _ = algebraMap ℝ A (s * Real.sqrt c) + algebraMap ℝ A (s * Real.sqrt c) +
          algebraMap ℝ A (s * s) := by rw [map_add, map_add]
      _ ≤ s • CFC.sqrt b + s • CFC.sqrt b + algebraMap ℝ A (s * s) := by gcongr
  have h₃ : CFC.sqrt a ≤ CFC.sqrt b + algebraMap ℝ A s :=
    calc CFC.sqrt a ≤ CFC.sqrt ((CFC.sqrt b + algebraMap ℝ A s) ^ 2) := CFC.sqrt_le_sqrt _ _ h₂
      _ = CFC.sqrt b + algebraMap ℝ A s := CFC.sqrt_sq _ (add_nonneg (CFC.sqrt_nonneg b) hC)
  exact sub_le_iff_le_add'.2 h₃

/-- Upper half of `CFC.norm_sqrt_sub_sqrt_le`: `√a - √b ≤ √‖a - b‖`. This is
`sqrt_sub_sqrt_le_algebraMap_of_le` at `c = 0`. -/
theorem sqrt_sub_sqrt_le_algebraMap {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A (Real.sqrt ‖a - b‖) :=
  sqrt_sub_sqrt_le_algebraMap_of_le ha hb le_rfl (by rwa [map_zero]) (Real.sqrt_nonneg _)
    (by rw [Real.sqrt_zero, mul_zero, zero_add, Real.mul_self_sqrt (norm_nonneg _)])

end CFC
