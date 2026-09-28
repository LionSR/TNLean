/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Dimension bound for a family of matrices with `∑ Aᵢᴴ Aᵢ = 1`

If `A_0, …, A_{d-1}` are `a × b` complex matrices with `∑_i A_i^† A_i = 1`, then
the stacked `(a d) × b` matrix has orthonormal columns, so `b ≤ a d`.

## Main results

* `Matrix.card_le_mul_of_sum_conjTranspose_mul_eq_one` — the bound `b ≤ a d`.
-/

open scoped Matrix

namespace Matrix

/-- If `A_0, …, A_{d-1}` are `a × b` matrices with `∑_i A_i^† A_i = 1`, then
`b ≤ a d`: the stacked `(a d) × b` matrix has orthonormal columns. -/
theorem card_le_mul_of_sum_conjTranspose_mul_eq_one {d a b : ℕ}
    (A : Fin d → Matrix (Fin a) (Fin b) ℂ) (hA : ∑ i, (A i)ᴴ * A i = 1) : b ≤ a * d := by
  let S : Matrix (Fin a × Fin d) (Fin b) ℂ := Matrix.of fun x β => A x.2 x.1 β
  have hS : Sᴴ * S = 1 := by
    rw [← hA]
    ext β β'
    simp only [S, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  simpa using Matrix.IsIsometry.card_le S hS

end Matrix
