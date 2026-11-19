/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.LocalEnergyTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.NatBinaryBounds

/-!
# Polynomial schoolbook charge of a local Hamiltonian matrix element

All operands and results of the nested evaluator are included. The charge counts
rational arithmetic in the schoolbook model and leaves gcd normalization and
the cost of the surrounding boundary minimization algorithm open.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- A coarse common exponent, linear in the bit budget at fixed dimensions. -/
def localTermsBitBudget (q Da Db n m P h : ℕ) : ℕ :=
  (84 * n + 74) * (2 * P * h + h + 1) + 28 * n * (Da + Db + 2 * q) + 28 * q + 2 * m + 15

/-- Bound the full local matrix-element record height by an explicit binary exponent. -/
theorem localTermsHeight_le_two_pow {q Da Db n m P H h : ℕ} (hH : H ≤ 2 ^ h) :
    localTermsHeight q Da Db n m (H ^ (2 * P)) (2 * H) ≤
      2 ^ localTermsBitBudget q Da Db n m P h := by
  have hM := pow_le_two_pow_mul (2 * P) hH
  have hC := mul_le_two_pow_add (show 2 ≤ 2 ^ 1 by decide) hH
  have one : 1 ≤ (2 : ℕ) ^ 0 := by decide
  have two : 2 ≤ (2 : ℕ) ^ 1 := by decide
  have dim (a : ℕ) : a ≤ 2 ^ a := (Nat.lt_two_pow_self).le
  have hD := mul_le_two_pow_add (dim Da) (dim Db)
  have hK := mul_le_two_pow_add (pow_le_two_pow_mul 2 (dim q)) (pow_le_two_pow_mul 3 hC)
  have hU := mul_le_two_pow_add (pow_le_two_pow_mul 3 hM) (max_le_two_pow_add one hK)
  have hS := max_le_two_pow_add hU
    (pow_le_two_pow_mul n (mul_le_two_pow_add (mul_le_two_pow_add (pow_le_two_pow_mul 3 hM) hD)
      (max_le_two_pow_add one hK)))
  have hX := mul_le_two_pow_add hM (max_le_two_pow_add one hC)
  have hrow := pow_le_two_pow_mul n (mul_le_two_pow_add hD hK)
  have hF := max_le_two_pow_add hX
    (mul_le_two_pow_add (pow_le_two_pow_mul (3 * n) hM) (max_le_two_pow_add one hrow))
  have hg {a u : ℕ} (ha : a ≤ 2 ^ u) := mul_le_two_pow_add two (pow_le_two_pow_mul 4 ha)
  have htransfer := max_le_two_pow_add (hg (hg hX))
    (mul_le_two_pow_add two (pow_le_two_pow_mul 2 hU))
  have hoverlap := max_le_two_pow_add htransfer (max_le_two_pow_add (hg hS) (hg (hg hF)))
  have hV := mul_le_two_pow_add (pow_le_two_pow_mul (3 * n + 2) hM)
    (max_le_two_pow_add one (mul_le_two_pow_add (pow_le_two_pow_mul 2 hC) hrow))
  have hterm := max_le_two_pow_add hoverlap (hg (max_le_two_pow_add hX hV))
  have hR := mul_le_two_pow_add (pow_le_two_pow_mul 4 (dim q))
    (mul_le_two_pow_add (pow_le_two_pow_mul 3 hC) hrow)
  have hN := pow_le_two_pow_mul (3 * n + 3) hM
  have hi := mul_le_two_pow_add two
    (pow_le_two_pow_mul 2 (mul_le_two_pow_add hN (max_le_two_pow_add one hR)))
  have ho := mul_le_two_pow_add two
    (pow_le_two_pow_mul 2 (mul_le_two_pow_add hN
      (max_le_two_pow_add one (mul_le_two_pow_add (dim m) hR))))
  apply (max_le_two_pow_add (max_le_two_pow_add hterm hi) ho).trans
  apply Nat.pow_le_pow_right (by decide)
  unfold localTermsBitBudget
  exact le_of_eq (by ring)

variable {q Da Db n m H : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hK : ∀ i a b, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (K i a b)))

include hcapA hcapB hPA hPB hK

/-- Full operation-list charge from the input bit budget and the dimensions. -/
theorem localTerms_polynomial_schoolbookCharge {h : ℕ} (hH : H ≤ 2 ^ h) :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4
    let T := m * (q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8) + 2)
    schoolbookCharge (matrixElementOfLocalTerms A B capA capB PA PB p r K).run.2 ≤
      T * 8 * (localTermsBitBudget q Da Db n m P h + 2) ^ 2 := by
  intro P T
  have hmax := localTerms_maxHeight_of_inputHeight A B capA capB PA PB p r K hcapA hcapB hPA hPB hK
  have hc := schoolbookCharge_le_of_maxHeight_le_two_pow
    (hmax.trans (localTermsHeight_le_two_pow hH))
  rwa [(localTerms_value_length A B capA capB PA PB p r K).2] at hc

omit hcapA hcapB hPA hPB hK in
/-- Empty support returns zero with an empty record, even for a nonempty chain. -/
theorem localTerms_empty_sum (p r : Fin 0 → Fin n)
    (K : Fin 0 → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    (matrixElementOfLocalTerms A B capA capB PA PB p r K).run = ((0, 0), []) := rfl

omit hcapA hcapB hPA hPB hK in
/-- On an empty chain, giving a site for every local term forces the term set to be empty. -/
theorem localTerms_empty_chain {m : ℕ} (p : Fin m → Fin 0) : m = 0 := by
  cases m with
  | zero => rfl
  | succ m => exact Fin.elim0 (p 0)

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
