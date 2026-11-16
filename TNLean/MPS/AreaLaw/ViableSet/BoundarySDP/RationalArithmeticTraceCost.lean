/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SearchCost
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Schoolbook charges for recorded rational arithmetic

Each recorded operation is charged according to the existing rational schoolbook
model, using the largest bit length of its two operands and computed result.
A uniform height bound on the actual operation list therefore bounds its total
charge. This is a bound in that charged model, not a running-time theorem for
the integer gcd or rational normalization implementation.

## References

These bounds support the finite-precision analysis of contractions in Landau,
Vazirani and Vidick, arXiv:1307.5143v1, Claim 2.7; they do not establish that
claim or the running time of a machine implementation of rational arithmetic.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- The largest numerator-or-denominator bit length among the two operands
and the computed result of an operation. -/
def Operation.bitLength (operation : Operation) : ℕ :=
  max (rationalBitLength operation.left)
    (max (rationalBitLength operation.right) (rationalBitLength operation.result))

/-- An operation bit-length bound covers both operands and the computed result. -/
theorem Operation.bitLength_le_iff (operation : Operation) (B : ℕ) :
    operation.bitLength ≤ B ↔ rationalBitLength operation.left ≤ B ∧
      rationalBitLength operation.right ≤ B ∧ rationalBitLength operation.result ≤ B := by
  simp only [Operation.bitLength, max_le_iff]

/-- A uniform operation-height bound controls the bit lengths of both operands
and their result. -/
theorem Operation.bitLength_le_of_height_le {operation : Operation} {H : ℕ}
    (h : operation.height ≤ H) : operation.bitLength ≤ Nat.log2 H + 1 := by
  obtain ⟨hl, hr, hv⟩ := (Operation.height_le_iff operation H).mp h
  exact max_le (rationalBitLength_le hl)
    (max_le (rationalBitLength_le hr) (rationalBitLength_le hv))

/-- Every operation actually present in a height-bounded record has the
corresponding operand and result bit-length bound. -/
theorem operation_bitLength_le_of_mem {operations : List Operation}
    {operation : Operation} {H : ℕ} (h : maxHeight operations ≤ H)
    (hmem : operation ∈ operations) : operation.bitLength ≤ Nat.log2 H + 1 :=
  Operation.bitLength_le_of_height_le ((maxHeight_le_iff operations H).mp h operation hmem)

/-- Sum of the existing rational schoolbook charges over the actual recorded
operations, with the bit length of each operation determined by its operands
and computed result. -/
def schoolbookCharge (operations : List Operation) : ℕ :=
  (operations.map fun operation ↦ rationalSchoolbookOperationCost operation.bitLength).sum

/-- An empty operation list has zero schoolbook charge. -/
@[simp] theorem schoolbookCharge_nil : schoolbookCharge [] = 0 := rfl

/-- Concatenating operation records adds their schoolbook charges. -/
@[simp] theorem schoolbookCharge_append (first second : List Operation) :
    schoolbookCharge (first ++ second) = schoolbookCharge first + schoolbookCharge second := by
  simp only [schoolbookCharge, List.map_append, List.sum_append]

/-- A uniform height bound controls the sum of the existing schoolbook charges
for every operation in the actual record. -/
theorem schoolbookCharge_le_of_maxHeight_le {operations : List Operation} {H : ℕ}
    (h : maxHeight operations ≤ H) :
    schoolbookCharge operations ≤
      operations.length * rationalSchoolbookOperationCost (Nat.log2 H + 1) := by
  have hsum := List.sum_le_length_nsmul
    (operations.map fun operation ↦ rationalSchoolbookOperationCost operation.bitLength)
    (rationalSchoolbookOperationCost (Nat.log2 H + 1)) (by
      intro charge hmem
      obtain ⟨operation, hop, rfl⟩ := List.mem_map.mp hmem
      exact rationalSchoolbookOperationCost_mono (operation_bitLength_le_of_mem h hop))
  simpa only [schoolbookCharge, List.length_map, nsmul_eq_mul, Nat.cast_id] using hsum

/-- An exponential height bound gives a quadratic charge per recorded operation
in the existing schoolbook model. -/
theorem schoolbookCharge_le_of_maxHeight_le_two_pow {operations : List Operation} {B : ℕ}
    (h : maxHeight operations ≤ 2 ^ B) :
    schoolbookCharge operations ≤ operations.length * 8 * (B + 2) ^ 2 := by
  have hcharge := schoolbookCharge_le_of_maxHeight_le h
  rw [Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < 2)] at hcharge
  simpa only [rationalSchoolbookOperationCost, Nat.add_assoc, Nat.mul_assoc] using hcharge

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
