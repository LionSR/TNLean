/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Fine meshes at adjacent layer scales

The fine-cell exponents are nondecreasing and increase by at most one
between consecutive layer scales. Hence adjacent fine-cell sides are equal
or differ by a factor of two. This arithmetic precedes the construction of
the elementary belt segments and their triangular fans.

Source: Section 11, `geometry:initial-stars`, lines 299–306 and 352–356
of OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026).
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The fine-cell exponent is nondecreasing with the layer scale.
Source: area-law Section 11, `geometry:initial-stars`, lines 299–306. -/
theorem fineScaleIndex_mono : Monotone fineScaleIndex := by
  intro k h hkh
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkh)
    (by norm_num [Exponents.zeta, Exponents.geometryDelta]))

/-- Consecutive fine-cell exponents are equal or differ by one.
Source: area-law Section 11, `geometry:initial-stars`, lines 299–306. -/
theorem fineScaleIndex_succ (k : ℕ) :
    fineScaleIndex (k + 1) = fineScaleIndex k ∨
      fineScaleIndex (k + 1) = fineScaleIndex k + 1 := by
  have hz : 0 ≤ (Exponents.zeta : ℝ) ∧ (Exponents.zeta : ℝ) ≤ 1 := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  have hu : fineScaleIndex (k + 1) ≤ fineScaleIndex k + 1 := by
    unfold fineScaleIndex
    calc
      Nat.floor ((Exponents.zeta : ℝ) * ((k + 1 : ℕ) : ℝ)) ≤
          Nat.floor ((Exponents.zeta : ℝ) * (k : ℝ) + 1) := by
        apply Nat.floor_mono
        simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
          add_le_add_right hz.2 ((Exponents.zeta : ℝ) * (k : ℝ))
      _ = Nat.floor ((Exponents.zeta : ℝ) * (k : ℝ)) + 1 :=
        Nat.floor_add_one (mul_nonneg hz.1 (Nat.cast_nonneg k))
  have hl : fineScaleIndex k ≤ fineScaleIndex (k + 1) :=
    fineScaleIndex_mono (Nat.le_succ k)
  omega

/-- Adjacent fine-cell side lengths are equal or differ by a factor of two.
Source: area-law Section 11, `geometry:initial-stars`, lines 299–306 and 352–356. -/
theorem fineScale_side_succ (k : ℕ) :
    (2 : ℕ) ^ fineScaleIndex (k + 1) = 2 ^ fineScaleIndex k ∨
      (2 : ℕ) ^ fineScaleIndex (k + 1) = 2 * 2 ^ fineScaleIndex k := by
  exact (fineScaleIndex_succ k).imp (congrArg (fun n ↦ (2 : ℕ) ^ n))
    (fun h ↦ by rw [h, pow_succ, mul_comm])

end TNLean.PEPS.AreaLaw.Geometry
