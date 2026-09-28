/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CStarSqrtHolder

/-!
# Square roots in a C⋆-algebra are Lipschitz away from zero

For positive elements `a` and `b` of a C⋆-algebra with `b ≥ c` for a real `c > 0`,
`‖√a - √b‖ ≤ ‖a - b‖ / √c`. Near a strictly positive element the square root is therefore
Lipschitz, which improves on the global `1/2`-Hölder bound `CFC.norm_sqrt_sub_sqrt_le`.

The proof is order-theoretic and uses only the operator monotonicity of the square root: with
`ε = ‖a - b‖` and `s = ε / √c ≤ √c`, the inequalities `a ≤ (√b + s)²` and `(√b - s)² ≤ a`
follow from `-ε ≤ a - b ≤ ε` and `√b ≥ √c`, and `√b - s ≥ 0`. When `ε > c` the Hölder bound
`√ε ≤ ε / √c` suffices. The upper half, `CFC.sqrt_sub_sqrt_le_algebraMap_of_le`, and the scalar
bound `CFC.algebraMap_sqrt_le_sqrt` live in `TNLean.Algebra.CStarSqrtHolder`, where the Hölder
bound is their case `c = 0`.

Mathlib has no Lipschitz bound for the square root; the results here are upstream candidates for
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`.

## Main declarations

* `CFC.norm_sqrt_sub_sqrt_le_div` — `‖√a - √b‖ ≤ ‖a - b‖ / √c` for `a ≥ 0` and `b ≥ c > 0`.
* `IsStrictlyPositive.exists_norm_sqrt_sub_sqrt_le` — a Lipschitz constant for the square root
  at a strictly positive element.
-/

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Lower half of `norm_sqrt_sub_sqrt_le_div`: if `b ≥ c ≥ 0` and `0 ≤ s ≤ √c` satisfies
`‖a - b‖ + s² ≤ 2 s √c`, then `√b - √a ≤ s`. -/
theorem sqrt_sub_sqrt_le_algebraMap_of_le' {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {c s : ℝ}
    (hc : 0 ≤ c) (hcb : algebraMap ℝ A c ≤ b) (hs : 0 ≤ s) (hsc : s ≤ Real.sqrt c)
    (hε : ‖a - b‖ + s * s ≤ 2 * s * Real.sqrt c) :
    CFC.sqrt b - CFC.sqrt a ≤ algebraMap ℝ A s := by
  have hS := algebraMap_sqrt_le_sqrt hc hcb
  have hT : 0 ≤ CFC.sqrt b + algebraMap ℝ A (-s) := by
    rw [map_neg, ← sub_eq_add_neg, sub_nonneg]
    exact (algebraMap_le_algebraMap_of_le hsc).trans hS
  have hsS : algebraMap ℝ A (s * Real.sqrt c) ≤ s • CFC.sqrt b := by
    rw [map_mul, ← Algebra.smul_def]
    exact smul_le_smul_of_nonneg_left hS hs
  have h₁ : b ≤ a + algebraMap ℝ A ‖a - b‖ := by
    rw [norm_sub_rev]
    exact sub_le_iff_le_add'.1
      (IsSelfAdjoint.le_algebraMap_norm_self (b - a) (hb.isSelfAdjoint.sub ha.isSelfAdjoint))
  have h₂ : (CFC.sqrt b + algebraMap ℝ A (-s)) ^ 2 ≤ a := by
    rw [sq_sqrt_add_algebraMap hb, neg_smul, neg_mul_neg]
    have hle : algebraMap ℝ A ‖a - b‖ + algebraMap ℝ A (s * s) ≤
        algebraMap ℝ A (s * Real.sqrt c) + algebraMap ℝ A (s * Real.sqrt c) := by
      rw [← map_add, ← map_add]
      exact algebraMap_le_algebraMap_of_le (by linarith)
    calc b + (-(s • CFC.sqrt b) + -(s • CFC.sqrt b)) + algebraMap ℝ A (s * s)
        ≤ a + algebraMap ℝ A ‖a - b‖ + (-(s • CFC.sqrt b) + -(s • CFC.sqrt b)) +
            algebraMap ℝ A (s * s) := by gcongr
      _ = a + (algebraMap ℝ A ‖a - b‖ + algebraMap ℝ A (s * s)) -
            (s • CFC.sqrt b + s • CFC.sqrt b) := by abel
      _ ≤ a + (algebraMap ℝ A (s * Real.sqrt c) + algebraMap ℝ A (s * Real.sqrt c)) -
            (algebraMap ℝ A (s * Real.sqrt c) + algebraMap ℝ A (s * Real.sqrt c)) := by
          gcongr
      _ = a := by abel
  have h₃ : CFC.sqrt b + algebraMap ℝ A (-s) ≤ CFC.sqrt a :=
    calc CFC.sqrt b + algebraMap ℝ A (-s) = CFC.sqrt ((CFC.sqrt b + algebraMap ℝ A (-s)) ^ 2) :=
          (CFC.sqrt_sq _ hT).symm
      _ ≤ CFC.sqrt a := CFC.sqrt_le_sqrt _ _ h₂
  rw [map_neg, ← sub_eq_add_neg] at h₃
  exact sub_le_comm.1 h₃

/-- **Square roots are Lipschitz away from zero**: for `a ≥ 0` and `b ≥ c` with a real `c > 0`
in a C⋆-algebra, `‖√a - √b‖ ≤ ‖a - b‖ / √c`.

Upstream candidate for Mathlib, beside `CFC.sqrt_le_sqrt`. -/
theorem norm_sqrt_sub_sqrt_le_div {a b : A} (ha : 0 ≤ a) {c : ℝ} (hc : 0 < c)
    (hcb : algebraMap ℝ A c ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ ‖a - b‖ / Real.sqrt c := by
  have hb : 0 ≤ b := by simpa using (algebraMap_le_algebraMap_of_le (A := A) hc.le).trans hcb
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set ε := ‖a - b‖ with hε_def
  have hε : 0 ≤ ε := norm_nonneg _
  rcases le_or_gt ε c with hεc | hεc
  · set s := ε / Real.sqrt c
    have hs : 0 ≤ s := by positivity
    have hss : s * Real.sqrt c = ε := div_mul_cancel₀ _ hsc.ne'
    have hsc' : s ≤ Real.sqrt c := by
      rw [div_le_iff₀ hsc, Real.mul_self_sqrt hc.le]; exact hεc
    have hs2 : s * s ≤ ε := by
      calc s * s ≤ s * Real.sqrt c := mul_le_mul_of_nonneg_left hsc' hs
        _ = ε := hss
    refine IsSelfAdjoint.norm_le_of_le_algebraMap
      ((CFC.sqrt_nonneg a).isSelfAdjoint.sub (CFC.sqrt_nonneg b).isSelfAdjoint) hs
      (sqrt_sub_sqrt_le_algebraMap_of_le ha hb hc.le hcb hs (by nlinarith)) ?_
    rw [neg_le, neg_sub]
    exact sqrt_sub_sqrt_le_algebraMap_of_le' ha hb hc.le hcb hs hsc' (by nlinarith)
  · refine (CFC.norm_sqrt_sub_sqrt_le ha hb).trans ?_
    rw [le_div_iff₀ hsc]
    calc Real.sqrt ε * Real.sqrt c ≤ Real.sqrt ε * Real.sqrt ε :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hεc.le) (Real.sqrt_nonneg _)
      _ = ε := Real.mul_self_sqrt hε

end CFC

/-- **Lipschitz constant at a strictly positive element**: if `b` is strictly positive, there is
`K ≥ 0` with `‖√a - √b‖ ≤ K ‖a - b‖` for every `a ≥ 0`.

Upstream candidate for Mathlib. -/
theorem IsStrictlyPositive.exists_norm_sqrt_sub_sqrt_le {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {b : A} (hb : IsStrictlyPositive b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : A, 0 ≤ a → ‖CFC.sqrt a - CFC.sqrt b‖ ≤ K * ‖a - b‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, le_rfl, fun a _ => by simp [Subsingleton.elim (CFC.sqrt a - CFC.sqrt b) 0]⟩
  obtain ⟨c, hc, hcb⟩ := (CFC.exists_pos_algebraMap_le_iff b hb.nonneg.isSelfAdjoint).2
    fun x hx => hb.spectrum_pos hx
  refine ⟨1 / Real.sqrt c, by positivity, fun a ha => ?_⟩
  rw [one_div_mul_eq_div]
  exact CFC.norm_sqrt_sub_sqrt_le_div ha hc hcb
