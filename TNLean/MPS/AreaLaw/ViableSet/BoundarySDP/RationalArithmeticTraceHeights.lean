/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ComplexArithmeticHeights

/-!
# Heights of actual recorded complex-arithmetic operands

For each operation in the recorded complex addition, multiplication, or
conjugation, the two actual rational operands and their computed result obey
explicit height bounds. The multiplication estimate includes the four products
used as operands of the final real subtraction and imaginary addition.

## References

These are auxiliary arithmetic estimates for the boundary minimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478. The statements concern the primitive evaluators themselves,
without asserting a height bound for an entire tensor contraction.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

private theorem one_le_of_decode_height {S : ℕ} (x : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x)) : 1 ≤ S := by
  have hxre := ((RationalComplexCode.decode_height_iff x).mp hx).1
  exact x.1.den_pos.trans_le ((den_le_rationalHeight _).trans hxre)

/-- Every actual recorded operand and result in complex multiplication has
height at most `2 S⁴` when the two input coordinate heights are at most `S`. -/
theorem complexMul_operation_heights {S : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex y))
    (operation : Operation) (hoperation : operation ∈ (complexMul x y).run.2) :
    rationalHeight operation.left ≤ 2 * S ^ 4 ∧
      rationalHeight operation.right ≤ 2 * S ^ 4 ∧
      rationalHeight operation.result ≤ 2 * S ^ 4 := by
  have hS := one_le_of_decode_height x hx
  have hprod : S * S ≤ 2 * S ^ 4 := by
    have hpow : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 4)
    rw [pow_two] at hpow
    omega
  have hsmall : S ≤ 2 * S ^ 4 :=
    (show S ≤ S * S by simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hS).trans hprod
  obtain ⟨hxre, hxim⟩ := (RationalComplexCode.decode_height_iff x).mp hx
  obtain ⟨hyre, hyim⟩ := (RationalComplexCode.decode_height_iff y).mp hy
  obtain ⟨hac, hbd, had, hbc, hreal, himag⟩ :=
    RationalContractionCost.complexMul_primitive_heights x y hx hy
  have hout : 2 * (S * S) ^ 2 = 2 * S ^ 4 := by ring
  rw [hout] at hreal himag
  simp only [run_complexMul, List.mem_cons, List.not_mem_nil, or_false] at hoperation
  rcases hoperation with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hxre.trans hsmall, hyre.trans hsmall, hac.trans hprod⟩
  · exact ⟨hxim.trans hsmall, hyim.trans hsmall, hbd.trans hprod⟩
  · exact ⟨hxre.trans hsmall, hyim.trans hsmall, had.trans hprod⟩
  · exact ⟨hxim.trans hsmall, hyre.trans hsmall, hbc.trans hprod⟩
  · exact ⟨hac.trans hprod, hbd.trans hprod, hreal⟩
  · exact ⟨had.trans hprod, hbc.trans hprod, himag⟩

/-- The maximum over the six actual recorded operations in complex
multiplication obeys the same uniform height bound. -/
theorem complexMul_maxHeight_le {S : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex y)) :
    maxHeight (complexMul x y).run.2 ≤ 2 * S ^ 4 := by
  apply (maxHeight_le_iff _ _).mpr
  intro operation hoperation
  exact (Operation.height_le_iff _ _).mpr
    (complexMul_operation_heights x y hx hy operation hoperation)

/-- Both actual operands and the result of every recorded complex-addition
operation have height at most `2 S²`. -/
theorem complexAdd_operation_heights {S : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex y))
    (operation : Operation) (hoperation : operation ∈ (complexAdd x y).run.2) :
    rationalHeight operation.left ≤ 2 * S ^ 2 ∧
      rationalHeight operation.right ≤ 2 * S ^ 2 ∧
      rationalHeight operation.result ≤ 2 * S ^ 2 := by
  have hS := one_le_of_decode_height x hx
  have hsmall : S ≤ 2 * S ^ 2 := by
    have hmul : S ≤ S * S := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hS
    rw [pow_two]
    omega
  obtain ⟨hxre, hxim⟩ := (RationalComplexCode.decode_height_iff x).mp hx
  obtain ⟨hyre, hyim⟩ := (RationalComplexCode.decode_height_iff y).mp hy
  obtain ⟨hreal, himag⟩ := RationalContractionCost.complexAdd_primitive_heights x y hx hy
  have hout : 2 * S * S = 2 * S ^ 2 := by ring
  rw [hout] at hreal himag
  simp only [run_complexAdd, List.mem_cons, List.not_mem_nil, or_false] at hoperation
  rcases hoperation with rfl | rfl
  · exact ⟨hxre.trans hsmall, hyre.trans hsmall, hreal⟩
  · exact ⟨hxim.trans hsmall, hyim.trans hsmall, himag⟩

/-- The greatest height of any recorded operand or result in complex addition
is bounded by `2 S²`. -/
theorem complexAdd_maxHeight_le {S : ℕ} (x y : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (hy : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex y)) :
    maxHeight (complexAdd x y).run.2 ≤ 2 * S ^ 2 := by
  apply (maxHeight_le_iff _ _).mpr
  intro operation hoperation
  exact (Operation.height_le_iff _ _).mpr
    (complexAdd_operation_heights x y hx hy operation hoperation)

/-- Recorded conjugation includes the zero operand and the actual imaginary
coordinate; neither operand nor the subtraction result exceeds height `S`. -/
theorem complexConj_operation_heights {S : ℕ} (x : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x))
    (operation : Operation) (hoperation : operation ∈ (complexConj x).run.2) :
    rationalHeight operation.left ≤ S ∧ rationalHeight operation.right ≤ S ∧
      rationalHeight operation.result ≤ S := by
  have hS := one_le_of_decode_height x hx
  have hxim := ((RationalComplexCode.decode_height_iff x).mp hx).2
  have hresult := (RationalGramContractionCost.complexConj_primitive_heights x hx).2.1
  simp only [run_complexConj, List.mem_singleton] at hoperation
  subst operation
  refine ⟨?_, hxim, hresult⟩
  change rationalHeight (0 : ℚ) ≤ S
  simpa only [rationalHeight, Rat.num_zero, Int.natAbs_zero, Rat.den_zero,
    max_eq_right (Nat.zero_le 1)] using hS

/-- The single recorded conjugation operation has maximum height at most
the common input coordinate height. -/
theorem complexConj_maxHeight_le {S : ℕ} (x : ℚ × ℚ)
    (hx : HasRationalComplexCoordinatesOfHeight S (decodeRationalComplex x)) :
    maxHeight (complexConj x).run.2 ≤ S := by
  apply (maxHeight_le_iff _ _).mpr
  intro operation hoperation
  exact (Operation.height_le_iff _ _).mpr
    (complexConj_operation_heights x hx operation hoperation)

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
