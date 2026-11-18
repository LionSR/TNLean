/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTraceHeights

/-!
# Arithmetic heights of a weighted transfer summand

A summand conjugates the left tensor entry, multiplies by the physical weight,
then multiplies by the right tensor entry.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- Record the weighted transfer summand in the order used by the counted evaluation. -/
def weightedTerm (x w y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let l ← complexConj x
  let t ← complexMul l w
  complexMul t y

/-- Forgetting the operands gives the existing weighted transfer evaluation. -/
theorem erase_weightedTerm (x w y : ℚ × ℚ) :
    erase (weightedTerm x w y) = RationalGramContractionCost.weightedTerm x w y := by
  simp only [weightedTerm, erase_bind, erase_complexConj, erase_complexMul,
    RationalGramContractionCost.weightedTerm]

/-- Every operand and result in the thirteen recorded operations obeys the
bound obtained by applying the complex-product height estimate twice. -/
theorem weightedTerm_maxHeight_le {S : ℕ} (x w y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (hw : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex w))
    (hy : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex y)) :
    maxHeight (weightedTerm x w y).run.2 ≤ 2 * (2 * S ^ 4) ^ 4 := by
  let l := (complexConj x).run.1
  let t := (complexMul l w).run.1
  have hl : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex l) :=
    (RationalComplexCode.decode_height_iff l).mpr
      (RationalGramContractionCost.complexConj_primitive_heights x hx).2.2
  have ht : HasRationalComplexCoordinatesOfHeight (2 * S ^ 4) (decodeRationalComplex t) := by
    apply (RationalComplexCode.decode_height_iff t).mpr
    have he : (S * S) ^ 2 = S ^ 4 := by ring
    simpa only [he, t, run_complexMul, RationalContractionCost.run_complexMul] using
      RationalContractionCost.complexMul_coordinate_heights l w hl hw
  have hgrow (a : ℕ) : a ≤ 2 * a ^ 4 := by
    calc
      a ≤ a ^ 4 := Nat.le_self_pow (by decide) _
      _ ≤ 2 * a ^ 4 := by omega
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  simp only [weightedTerm, run_bind, List.mem_append] at hop
  rcases hop with h | h | h
  · exact ((maxHeight_le_iff _ _).mp (complexConj_maxHeight_le x hx) op h).trans
      ((hgrow S).trans (hgrow _))
  · exact ((maxHeight_le_iff _ _).mp (complexMul_maxHeight_le l w hl hw) op h).trans (hgrow _)
  · exact (maxHeight_le_iff _ _).mp (complexMul_maxHeight_le t y ht (hy.mono (hgrow S))) op h

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
