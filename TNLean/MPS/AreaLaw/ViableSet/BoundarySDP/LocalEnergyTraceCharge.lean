/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.LocalEnergyTrace

/-!
# Polynomial schoolbook charge of a local Hamiltonian matrix element

All operands and results of the nested evaluator are included. The charge counts
rational arithmetic in the schoolbook model and leaves gcd normalization and
the cost of the surrounding boundary minimization algorithm open.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

private theorem bitsMul {a b u v : ℕ} (ha : a ≤ 2 ^ u) (hb : b ≤ 2 ^ v) :
    a * b ≤ 2 ^ (u + v) := by rw [pow_add]; exact Nat.mul_le_mul ha hb

private theorem bitsMax {a b u v : ℕ} (ha : a ≤ 2 ^ u) (hb : b ≤ 2 ^ v) :
    max a b ≤ 2 ^ (u + v) := by
  apply max_le
  · exact ha.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact hb.trans (Nat.pow_le_pow_right (by decide) (by omega))

private theorem bitsPow {a u : ℕ} (k : ℕ) (ha : a ≤ 2 ^ u) :
    a ^ k ≤ 2 ^ (u * k) := by rw [pow_mul]; exact Nat.pow_le_pow_left ha k

/-- A coarse common exponent, linear in the bit budget at fixed dimensions. -/
def localTermsBitBudget (q Da Db n m P h : ℕ) : ℕ :=
  (84 * n + 74) * (2 * P * h + h + 1) + 28 * n * (Da + Db + 2 * q) + 28 * q + 2 * m + 15

theorem localTermsHeight_le_two_pow {q Da Db n m P H h : ℕ} (hH : H ≤ 2 ^ h) :
    localTermsHeight q Da Db n m (H ^ (2 * P)) (2 * H) ≤
      2 ^ localTermsBitBudget q Da Db n m P h := by
  have hM := bitsPow (2 * P) hH
  have hC := bitsMul (show 2 ≤ 2 ^ 1 by decide) hH
  have one : 1 ≤ (2 : ℕ) ^ 0 := by decide
  have two : 2 ≤ (2 : ℕ) ^ 1 := by decide
  have dim (a : ℕ) : a ≤ 2 ^ a := (Nat.lt_two_pow_self).le
  have hD := bitsMul (dim Da) (dim Db)
  have hK := bitsMul (bitsPow 2 (dim q)) (bitsPow 3 hC)
  have hU := bitsMul (bitsPow 3 hM) (bitsMax one hK)
  have hS := bitsMax hU (bitsPow n (bitsMul (bitsMul (bitsPow 3 hM) hD) (bitsMax one hK)))
  have hX := bitsMul hM (bitsMax one hC)
  have hrow := bitsPow n (bitsMul hD hK)
  have hF := bitsMax hX (bitsMul (bitsPow (3 * n) hM) (bitsMax one hrow))
  have hg {a u : ℕ} (ha : a ≤ 2 ^ u) := bitsMul two (bitsPow 4 ha)
  have htransfer := bitsMax (hg (hg hX)) (bitsMul two (bitsPow 2 hU))
  have hoverlap := bitsMax htransfer (bitsMax (hg hS) (hg (hg hF)))
  have hV := bitsMul (bitsPow (3 * n + 2) hM) (bitsMax one (bitsMul (bitsPow 2 hC) hrow))
  have hterm := bitsMax hoverlap (hg (bitsMax hX hV))
  have hR := bitsMul (bitsPow 4 (dim q)) (bitsMul (bitsPow 3 hC) hrow)
  have hN := bitsPow (3 * n + 3) hM
  have hi := bitsMul two (bitsPow 2 (bitsMul hN (bitsMax one hR)))
  have ho := bitsMul two (bitsPow 2 (bitsMul hN (bitsMax one (bitsMul (dim m) hR))))
  apply (bitsMax (bitsMax hterm hi) ho).trans
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
