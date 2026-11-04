/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalArithmeticTrace

/-!
# Arithmetic records for sequential rational coefficient contraction

Each scalar product records its rational operations in their evaluation order.
Every intermediate row is stored as a finite vector before the next site is
processed. Replacing the operation list by its length gives exactly the existing
counted contraction, so its correctness and arithmetic count apply without a
second counting argument. Zero-padding accommodates varying bond dimensions,
and the scalar cap and the empty chain are included.

## References

These concrete arithmetic records support the finite-precision analysis of
the contractions used in LVV, arXiv:1307.5143v1, Claim 2.7.
-/

namespace TNLean.MPS.AreaLaw

namespace RationalArithmeticTrace

/-- Erasure commutes with storing a row, without requiring equal arithmetic
counts for its entries. The entries retain their original evaluation order. -/
theorem erase_vectorOfFnM {α : Type} {D : ℕ} (f : Fin D → Arithmetic α) :
    erase (Vector.ofFnM f) = Vector.ofFnM (fun i ↦ erase (f i)) := by
  induction D with
  | zero => simp only [Vector.ofFnM_zero, erase_pure]
  | succ D ih =>
    rw [Vector.ofFnM_succ, Vector.ofFnM_succ]
    simp only [erase_bind, ih, erase_pure]

/-- A counted evaluation obtained by erasure determines both the traced
value and the length of its actual operation list. -/
theorem value_length_of_run_erase {α : Type} {x : Arithmetic α} {v : α} {c : ℕ}
    (h : (erase x).run = (v, Multiplicative.ofAdd c)) :
    x.run.1 = v ∧ x.run.2.length = c := by
  rw [run_erase] at h
  exact ⟨congrArg Prod.fst h, congrArg Multiplicative.toAdd (congrArg Prod.snd h)⟩

end RationalArithmeticTrace

namespace RationalContractionTrace

open RationalArithmeticTrace

/-- Evaluate a scalar product in increasing coordinate order, recording each
complex multiplication followed by its addition to the previous partial sum. -/
def dot : (D : ℕ) → (Fin D → ℚ × ℚ) → (Fin D → ℚ × ℚ) → Arithmetic (ℚ × ℚ)
  | 0, _, _ => pure (0, 0)
  | D + 1, v, w => do
    let previous ← dot D (fun i ↦ v i.castSucc) (fun i ↦ w i.castSucc)
    let term ← complexMul (v (Fin.last D)) (w (Fin.last D))
    complexAdd previous term

/-- Erasing the scalar-product record gives the existing counted evaluator. -/
@[simp] theorem erase_dot (D : ℕ) (v w : Fin D → ℚ × ℚ) :
    erase (dot D v w) = RationalContractionCost.dot D v w := by
  induction D with
  | zero => rfl
  | succ D ih =>
    simp only [dot, erase_bind, ih, erase_complexMul, erase_complexAdd]
    rfl

/-- Evaluate and store every entry of the next row before returning its
coordinate function. All scalar-product operation lists are retained. -/
def rowMul {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) : Arithmetic (Fin D → ℚ × ℚ) := do
  let row ← Vector.ofFnM fun j ↦ dot D v (fun i ↦ A i j)
  pure fun j ↦ row[j.val]

/-- The row is stored in exactly the same order as in the counted evaluator. -/
@[simp] theorem erase_rowMul {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) :
    erase (rowMul v A) = RationalContractionCost.rowMul v A := by
  simp only [rowMul, erase_bind, erase_vectorOfFnM, erase_dot, erase_pure]
  rfl

/-- Propagate the stored row sequentially, recording the operations at each
site before proceeding to the remaining suffix. -/
def rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    Arithmetic (Fin D → ℚ × ℚ) :=
  match As with
  | [] => pure v
  | A :: As => do
    let next ← rowMul v A
    rowProduct next As

/-- Erasure preserves the sequential propagation through every site. -/
@[simp] theorem erase_rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    erase (rowProduct v As) = RationalContractionCost.rowProduct v As := by
  induction As generalizing v with
  | nil => rfl
  | cons A As ih =>
    simp only [rowProduct, erase_bind, erase_rowMul, ih]
    rfl

/-- Contract the sequentially propagated row at a specified boundary
coordinate and multiply by the rational scalar cap. -/
def contract {D : ℕ} (cap : ℚ × ℚ) (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (j : Fin D) :
    Arithmetic (ℚ × ℚ) := do
  let row ← rowProduct v As
  complexMul cap (row j)

/-- Erasure includes the final scalar-cap multiplication. -/
@[simp] theorem erase_contract {D : ℕ} (cap : ℚ × ℚ) (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (j : Fin D) :
    erase (contract cap v As j) = RationalContractionCost.contract cap v As j := by
  simp only [contract, erase_bind, erase_rowProduct, erase_complexMul]
  rfl

/-- Evaluate one coefficient of rational open-chain data with its full
operation record. The varying bond spaces are padded in the same way as in
the counted evaluator. -/
def coefficientOfRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (σ : Fin n → Fin q) : Arithmetic (ℚ × ℚ) :=
  contract cap (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0)
    (List.ofFn fun p : Fin n ↦ OBCChainTensor.zeroPadRationalParameters A P p (σ p))
    ⟨0, A.bondBound_pos⟩

/-- Erasing the coefficient record gives exactly the existing counted
coefficient evaluator, including for the empty chain. -/
@[simp] theorem erase_coefficientOfRationalParameters {q D n : ℕ}
    (A : OBCChainTensor q D n) (cap : ℚ × ℚ)
    (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q) :
    erase (coefficientOfRationalParameters A cap P σ) =
      RationalContractionCost.coefficientOfRationalParameters A cap P σ := by
  exact erase_contract _ _ _ _

/-- The recorded scalar product has the existing rational value and exactly
eight operations per coordinate, as follows from its erasure. -/
theorem dot_value_length (D : ℕ) (v w : Fin D → ℚ × ℚ) :
    (dot D v w).run.1 = ∑ i, RationalComplexCode.mul (v i) (w i) ∧
      (dot D v w).run.2.length = 8 * D := by
  apply value_length_of_run_erase
  simpa only [erase_dot] using RationalContractionCost.run_dot D v w

/-- The traced materialized row has the counted row's value and operation
count; no independent enumeration of its operations is needed. -/
theorem rowMul_value_length {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) :
    (rowMul v A).run.1 = RationalRectMatrixCode.rowMul v A ∧
      (rowMul v A).run.2.length = 8 * D ^ 2 := by
  apply value_length_of_run_erase
  simpa only [erase_rowMul] using RationalContractionCost.run_rowMul v A

/-- The traced propagation has the existing sequential value and exactly
eight times the number of sites times the squared row dimension operations. -/
theorem rowProduct_value_length {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    (rowProduct v As).run.1 = RationalRectMatrixCode.rowProduct v As ∧
      (rowProduct v As).run.2.length = 8 * As.length * D ^ 2 := by
  apply value_length_of_run_erase
  simpa only [erase_rowProduct] using RationalContractionCost.run_rowProduct v As

/-- The boundary contraction has the existing rational value and its final
cap contributes exactly six recorded rational operations. -/
theorem contract_value_length {D : ℕ} (cap : ℚ × ℚ) (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (j : Fin D) :
    (contract cap v As j).run.1 =
        RationalComplexCode.mul cap (RationalRectMatrixCode.rowProduct v As j) ∧
      (contract cap v As j).run.2.length = 8 * As.length * D ^ 2 + 6 := by
  apply value_length_of_run_erase
  simpa only [erase_contract] using RationalContractionCost.run_contract cap v As j

/-- The actual traced open-chain coefficient has the existing rational value
and exactly `8nD²+6` recorded operations, including at length zero. -/
theorem coefficientOfRationalParameters_value_length {q D n : ℕ}
    (A : OBCChainTensor q D n) (cap : ℚ × ℚ)
    (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q) :
    (coefficientOfRationalParameters A cap P σ).run.1 =
        OBCChainTensor.coefficientOfRationalParameters A cap P σ ∧
      (coefficientOfRationalParameters A cap P σ).run.2.length = 8 * n * D ^ 2 + 6 := by
  apply value_length_of_run_erase
  simpa only [erase_coefficientOfRationalParameters] using
    RationalContractionCost.run_coefficientOfRationalParameters A cap P σ

/-- Decoding the returned value gives the actual open-chain physical
coefficient, multiplied by the decoded scalar cap. -/
theorem decode_coefficientOfRationalParameters {q D n : ℕ}
    (A : OBCChainTensor q D n) (cap : ℚ × ℚ)
    (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (hP : ∀ e, decodeRationalComplex (P e) = OBCChainTensor.parameters A e)
    (σ : Fin n → Fin q) :
    decodeRationalComplex (coefficientOfRationalParameters A cap P σ).run.1 =
      decodeRationalComplex cap * A.coeff σ := by
  rw [(coefficientOfRationalParameters_value_length A cap P σ).1]
  exact OBCChainTensor.decode_coefficientOfRationalParameters A cap P hP σ

end RationalContractionTrace

end TNLean.MPS.AreaLaw
