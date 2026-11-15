/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContractionCost
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContractionCost
import Mathlib.Data.List.MinMax

/-!
# Records of rational arithmetic operations

Each operation records its two actual rational operands; its result is determined
by those operands. The writer output retains these operations in execution order.
Replacing the record by its length recovers the existing arithmetic counter,
including for complex addition and multiplication. No uniform height bound for
a complete tensor contraction is asserted here.

## References

This construction supports the finite-precision analysis of the contractions
used in Landau, Vazirani and Vidick, arXiv:1307.5143v1, Claim 2.7. The results
here compare concrete arithmetic evaluators; they do not assert that source
claim.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- One rational operation, with its actual operands. -/
inductive Operation where
  /-- Rational addition. -/
  | add (x y : ℚ)
  /-- Rational subtraction. -/
  | sub (x y : ℚ)
  /-- Rational multiplication. -/
  | mul (x y : ℚ)

/-- The first operand of a recorded rational operation. -/
def Operation.left : Operation → ℚ
  | .add x _ | .sub x _ | .mul x _ => x

/-- The second operand of a recorded rational operation. -/
def Operation.right : Operation → ℚ
  | .add _ y | .sub _ y | .mul _ y => y

/-- The result is computed from the recorded operands. -/
def Operation.result : Operation → ℚ
  | .add x y => x + y
  | .sub x y => x - y
  | .mul x y => x * y

/-- The largest reduced rational height of the two operands and their result. -/
def Operation.height (operation : Operation) : ℕ :=
  max (rationalHeight operation.left)
    (max (rationalHeight operation.right) (rationalHeight operation.result))

/-- An operation-height bound covers both operands and the computed result. -/
theorem Operation.height_le_iff (operation : Operation) (H : ℕ) :
    operation.height ≤ H ↔ rationalHeight operation.left ≤ H ∧
      rationalHeight operation.right ≤ H ∧ rationalHeight operation.result ≤ H := by
  simp only [Operation.height, max_le_iff]

/-- The greatest operation height in a list, with value zero for an empty list. -/
def maxHeight (operations : List Operation) : ℕ :=
  (operations.map Operation.height).foldr max 0

/-- The maximum bounds exactly the heights of all recorded operations. -/
theorem maxHeight_le_iff (operations : List Operation) (H : ℕ) :
    maxHeight operations ≤ H ↔ ∀ operation ∈ operations, operation.height ≤ H := by
  constructor
  · intro h operation hmem
    exact (List.le_max_of_le (List.mem_map.mpr ⟨operation, hmem, rfl⟩) le_rfl).trans h
  · intro h
    apply List.max_le_of_forall_le
    intro height hmem
    obtain ⟨operation, hop, rfl⟩ := List.mem_map.mp hmem
    exact h operation hop

/-- Rational computations retaining their operations in execution order. -/
abbrev Arithmetic := WriterT (List Operation) Id

/-- Sequential composition concatenates records in execution order. -/
@[simp] theorem run_bind {α β : Type} (x : Arithmetic α) (f : α → Arithmetic β) :
    (x >>= f).run = ((f x.run.1).run.1, x.run.2 ++ (f x.run.1).run.2) := rfl

/-- Returning an already computed value records no arithmetic. -/
@[simp] theorem run_pure {α : Type} (x : α) :
    (pure x : Arithmetic α).run = (x, []) := rfl

/-- Concatenation of operation records satisfies the laws of sequential
composition for the existing list-valued writer. -/
instance : LawfulMonad Arithmetic := LawfulMonad.mk'
  (bind_pure_comp := fun f x ↦ by
    apply WriterT.ext
    change (f x.run.1, x.run.2 ++ []) = (f x.run.1, x.run.2)
    rw [List.append_nil])
  (id_map := fun _ ↦ by apply WriterT.ext; rfl)
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun _ _ _ ↦ by
    apply WriterT.ext
    simp only [run_bind, List.append_assoc])

/-- Replace the list of performed operations by its arithmetic count. -/
def erase {α : Type} (x : Arithmetic α) : RationalContractionCost.Arithmetic α :=
  WriterT.adapt (fun operations ↦ Multiplicative.ofAdd operations.length) x

/-- Erasure preserves the computed value and counts precisely the recorded operations. -/
@[simp] theorem run_erase {α : Type} (x : Arithmetic α) :
    (erase x).run = (x.run.1, Multiplicative.ofAdd x.run.2.length) := rfl

/-- Returning a value records no arithmetic operation. -/
@[simp] theorem erase_pure {α : Type} (x : α) :
    erase (pure x) = (pure x : RationalContractionCost.Arithmetic α) := rfl

/-- Erasure commutes with sequential composition. -/
@[simp] theorem erase_bind {α β : Type} (x : Arithmetic α) (f : α → Arithmetic β) :
    erase (x >>= f) = (erase x >>= fun a ↦ erase (f a)) := by
  apply WriterT.ext
  change ((f x.run.1).run.1,
      Multiplicative.ofAdd (x.run.2 ++ (f x.run.1).run.2).length) =
    ((f x.run.1).run.1,
      Multiplicative.ofAdd x.run.2.length * Multiplicative.ofAdd (f x.run.1).run.2.length)
  simp only [List.length_append]
  rfl

/-- One rational addition with its actual operation recorded. -/
def rationalAdd (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x + y, [.add x y])

/-- One rational subtraction with its actual operation recorded. -/
def rationalSub (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x - y, [.sub x y])

/-- One rational multiplication with its actual operation recorded. -/
def rationalMul (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x * y, [.mul x y])

/-- Erasing a recorded addition gives the existing counted addition. -/
@[simp] theorem erase_rationalAdd (x y : ℚ) :
    erase (rationalAdd x y) = RationalContractionCost.rationalAdd x y := rfl

/-- Erasing a recorded subtraction gives the existing counted subtraction. -/
@[simp] theorem erase_rationalSub (x y : ℚ) :
    erase (rationalSub x y) = RationalContractionCost.rationalSub x y := rfl

/-- Erasing a recorded multiplication gives the existing counted multiplication. -/
@[simp] theorem erase_rationalMul (x y : ℚ) :
    erase (rationalMul x y) = RationalContractionCost.rationalMul x y := rfl

/-- Complex addition, recording the real addition before the imaginary addition. -/
def complexAdd (x y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let real ← rationalAdd x.1 y.1
  let imag ← rationalAdd x.2 y.2
  pure (real, imag)

/-- Complex multiplication in precisely the order used by the counted evaluator. -/
def complexMul (x y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let ac ← rationalMul x.1 y.1
  let bd ← rationalMul x.2 y.2
  let ad ← rationalMul x.1 y.2
  let bc ← rationalMul x.2 y.1
  let real ← rationalSub ac bd
  let imag ← rationalAdd ad bc
  pure (real, imag)

/-- The two recorded additions are exactly the operations executed. -/
@[simp] theorem run_complexAdd (x y : ℚ × ℚ) :
    (complexAdd x y).run =
      (RationalComplexCode.add x y, [.add x.1 y.1, .add x.2 y.2]) := rfl

/-- The six recorded operations retain their actual intermediate operands. -/
@[simp] theorem run_complexMul (x y : ℚ × ℚ) :
    (complexMul x y).run =
      (RationalComplexCode.mul x y,
        [.mul x.1 y.1, .mul x.2 y.2, .mul x.1 y.2, .mul x.2 y.1,
          .sub (x.1 * y.1) (x.2 * y.2), .add (x.1 * y.2) (x.2 * y.1)]) := rfl

/-- Erasing the recorded complex addition gives the existing counted program. -/
@[simp] theorem erase_complexAdd (x y : ℚ × ℚ) :
    erase (complexAdd x y) = RationalContractionCost.complexAdd x y := by
  simp only [complexAdd, erase_bind, erase_rationalAdd, erase_pure]
  rfl

/-- Erasing the recorded complex multiplication gives the existing counted program. -/
@[simp] theorem erase_complexMul (x y : ℚ × ℚ) :
    erase (complexMul x y) = RationalContractionCost.complexMul x y := by
  simp only [complexMul, erase_bind, erase_rationalMul, erase_rationalSub,
    erase_rationalAdd, erase_pure]
  rfl

/-- Complex conjugation performs one rational subtraction from zero. -/
def complexConj (z : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let imag ← rationalSub 0 z.2
  pure (z.1, imag)

/-- Conjugation records precisely its subtraction, including the zero operand. -/
@[simp] theorem run_complexConj (z : ℚ × ℚ) :
    (complexConj z).run = ((z.1, 0 - z.2), [.sub 0 z.2]) := rfl

/-- Erasing recorded conjugation gives the counted weighted-transfer primitive. -/
@[simp] theorem erase_complexConj (z : ℚ × ℚ) :
    erase (complexConj z) = RationalGramContractionCost.complexConj z := by
  simp only [complexConj, erase_bind, erase_rationalSub, erase_pure]
  rfl

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
