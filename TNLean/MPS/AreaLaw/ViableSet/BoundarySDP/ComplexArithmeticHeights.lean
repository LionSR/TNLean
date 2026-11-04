/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCodeHeights
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContractionCost

/-!
# Rational heights inside counted complex arithmetic

The counted complex multiplication forms four rational products and then one
subtraction and one addition. Their reduced numerator and denominator heights
are controlled by the heights of the two input coordinate pairs. The analogous
addition and conjugation estimates concern exactly the rational operations in
the existing counted evaluators.
-/

namespace TNLean.MPS.AreaLaw.RationalContractionCost

/-- All six rational operation results inside counted complex multiplication
have explicit coordinate-height bounds: four products, their real subtraction,
and their imaginary addition. -/
theorem complexMul_primitive_heights {Hx Hy : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight Hx (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight Hy (decodeRationalComplex y)) :
    let ac := (rationalMul x.1 y.1).run.1
    let bd := (rationalMul x.2 y.2).run.1
    let ad := (rationalMul x.1 y.2).run.1
    let bc := (rationalMul x.2 y.1).run.1
    rationalHeight ac ≤ Hx * Hy ∧ rationalHeight bd ≤ Hx * Hy ∧
      rationalHeight ad ≤ Hx * Hy ∧ rationalHeight bc ≤ Hx * Hy ∧
      rationalHeight (rationalSub ac bd).run.1 ≤ 2 * (Hx * Hy) ^ 2 ∧
      rationalHeight (rationalAdd ad bc).run.1 ≤ 2 * (Hx * Hy) ^ 2 := by
  obtain ⟨hxre, hxim⟩ := (RationalComplexCode.decode_height_iff x).mp hx
  obtain ⟨hyre, hyim⟩ := (RationalComplexCode.decode_height_iff y).mp hy
  have hac := (rationalHeight_mul_le x.1 y.1).trans (Nat.mul_le_mul hxre hyre)
  have hbd := (rationalHeight_mul_le x.2 y.2).trans (Nat.mul_le_mul hxim hyim)
  have had := (rationalHeight_mul_le x.1 y.2).trans (Nat.mul_le_mul hxre hyim)
  have hbc := (rationalHeight_mul_le x.2 y.1).trans (Nat.mul_le_mul hxim hyre)
  refine ⟨hac, hbd, had, hbc, ?_, ?_⟩
  · change rationalHeight (x.1 * y.1 - x.2 * y.2) ≤ 2 * (Hx * Hy) ^ 2
    apply (rationalHeight_sub_le _ _).trans
    rw [pow_two]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul (Nat.mul_le_mul_left 2 hac) hbd
  · change rationalHeight (x.1 * y.2 + x.2 * y.1) ≤ 2 * (Hx * Hy) ^ 2
    apply (rationalHeight_add_le _ _).trans
    rw [pow_two]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul (Nat.mul_le_mul_left 2 had) hbc

/-- The two coordinates actually returned by counted multiplication obey the
same bounds as its final rational subtraction and addition. -/
theorem complexMul_coordinate_heights {Hx Hy : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight Hx (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight Hy (decodeRationalComplex y)) :
    rationalHeight (complexMul x y).run.1.1 ≤ 2 * (Hx * Hy) ^ 2 ∧
      rationalHeight (complexMul x y).run.1.2 ≤ 2 * (Hx * Hy) ^ 2 :=
  (complexMul_primitive_heights x y hx hy).2.2.2.2

/-- Exponential input height bounds give a linear bound on the binary height
exponent of the actual complex multiplication output. -/
theorem complexMul_coordinate_heights_two_pow {ex ey : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight (2 ^ ex) (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight (2 ^ ey) (decodeRationalComplex y)) :
    rationalHeight (complexMul x y).run.1.1 ≤ 2 ^ (2 * (ex + ey) + 1) ∧
      rationalHeight (complexMul x y).run.1.2 ≤ 2 ^ (2 * (ex + ey) + 1) := by
  have hprod : (2 : ℕ) ^ ex * 2 ^ ey = 2 ^ (ex + ey) := (pow_add _ _ _).symm
  have hout : 2 * ((2 : ℕ) ^ (ex + ey)) ^ 2 = 2 ^ (2 * (ex + ey) + 1) := by
    calc
      _ = 2 ^ 1 * 2 ^ ((ex + ey) * 2) := by rw [pow_one, pow_mul]
      _ = 2 ^ (1 + (ex + ey) * 2) := (pow_add _ _ _).symm
      _ = _ := by congr 1; omega
  simpa only [hprod, hout] using complexMul_coordinate_heights x y hx hy

/-- Both rational additions used by counted complex addition have height at
most twice the product of the input heights. -/
theorem complexAdd_primitive_heights {Hx Hy : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight Hx (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight Hy (decodeRationalComplex y)) :
    rationalHeight (rationalAdd x.1 y.1).run.1 ≤ 2 * Hx * Hy ∧
      rationalHeight (rationalAdd x.2 y.2).run.1 ≤ 2 * Hx * Hy := by
  obtain ⟨hxre, hxim⟩ := (RationalComplexCode.decode_height_iff x).mp hx
  obtain ⟨hyre, hyim⟩ := (RationalComplexCode.decode_height_iff y).mp hy
  exact ⟨(rationalHeight_add_le _ _).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hxre) hyre),
    (rationalHeight_add_le _ _).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hxim) hyim)⟩

/-- The two coordinates returned by counted complex addition have precisely
the preceding rational-addition height bounds. -/
theorem complexAdd_coordinate_heights {Hx Hy : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight Hx (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight Hy (decodeRationalComplex y)) :
    rationalHeight (complexAdd x y).run.1.1 ≤ 2 * Hx * Hy ∧
      rationalHeight (complexAdd x y).run.1.2 ≤ 2 * Hx * Hy :=
  complexAdd_primitive_heights x y hx hy

end TNLean.MPS.AreaLaw.RationalContractionCost

namespace TNLean.MPS.AreaLaw.RationalGramContractionCost

open RationalContractionCost

/-- Counted conjugation subtracts the imaginary coordinate from zero. Its
subtraction result and both returned coordinates retain the input height bound. -/
theorem complexConj_primitive_heights {H : ℕ} (x : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex x)) :
    rationalHeight (0 : ℚ) ≤ max 1 H ∧
      rationalHeight (rationalSub 0 x.2).run.1 ≤ H ∧
      rationalHeight (complexConj x).run.1.1 ≤ H ∧
      rationalHeight (complexConj x).run.1.2 ≤ H := by
  obtain ⟨hxre, hxim⟩ := (RationalComplexCode.decode_height_iff x).mp hx
  refine ⟨?_, ?_, hxre, ?_⟩
  · have hzero : rationalHeight (0 : ℚ) = 1 := by norm_num [rationalHeight]
    rw [hzero]
    exact le_max_left 1 H
  · change rationalHeight (0 - x.2) ≤ H
    simpa only [zero_sub, rationalHeight_neg] using hxim
  · change rationalHeight (0 - x.2) ≤ H
    simpa only [zero_sub, rationalHeight_neg] using hxim

end TNLean.MPS.AreaLaw.RationalGramContractionCost
