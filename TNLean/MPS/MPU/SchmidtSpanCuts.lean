/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Internal cut ranks of Schmidt-space elements

Applying a linear functional to the discarded sites contracts columns or rows
of a coefficient matrix. Such contraction is matrix multiplication and cannot
increase rank. These two estimates are the finite-coordinate form of the
Schmidt-space inheritance argument in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Lemma 5.
-/

open scoped BigOperators

namespace Matrix

variable {K m n k : Type*} [Field K] [Fintype n] [Fintype k]

/-- Contracting the last coordinate by a scalar functional does not increase rank. -/
theorem rank_contract_right_le (M : Matrix m (n × k) K) (f : k → K) :
    Matrix.rank (fun i j => ∑ a : k, M i (j, a) * f a : Matrix m n K) ≤ M.rank := by
  classical
  let Q : Matrix (n × k) n K := fun r j => if r.1 = j then f r.2 else 0
  have hMQ : M * Q = fun i j => ∑ a : k, M i (j, a) * f a := by
    ext i j
    change (∑ r : n × k, M i r * Q r j) = _
    simp [Q, Fintype.sum_prod_type]
  rw [← hMQ]
  exact rank_mul_le_left M Q

/-- Contracting the first coordinate by a scalar functional does not increase rank. -/
theorem rank_contract_left_le [Finite m] (M : Matrix (k × m) n K) (f : k → K) :
    Matrix.rank (fun i j => ∑ a : k, f a * M (a, i) j : Matrix m n K) ≤ M.rank := by
  classical
  let : Fintype m := Fintype.ofFinite m
  let P : Matrix m (k × m) K := fun i r => if r.2 = i then f r.1 else 0
  have hPM : P * M = fun i j => ∑ a : k, f a * M (a, i) j := by
    ext i j
    change (∑ r : k × m, P i r * M r j) = _
    simp [P, Fintype.sum_prod_type]
  rw [← hPM]
  exact rank_mul_le_right P M

end Matrix
