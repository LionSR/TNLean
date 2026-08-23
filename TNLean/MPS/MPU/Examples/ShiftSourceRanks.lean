/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.Shift
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Source cuts and ranks of the cyclic shifts

This module computes the raw source cuts and source ranks of the primitive
right- and left-shift tensors from arXiv:1703.09188, lines 450--477 and
1980--1987.

For the right shift, the first source cut is the identity on the doubled
physical index. The second is the outer product of the vectorized identity
with itself. The left-shift formulas follow by physical adjunction.

No compact-SVD factors or standard-form data are chosen here.
-/

namespace MPOTensor

open scoped Matrix

/-- The first raw source cut of the right-shift tensor is the identity on the
product of two physical indices.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem sourceCutM₁_rightShiftTensor (d : ℕ) :
    sourceCutM₁ (rightShiftTensor d) = 1 := by
  ext row col
  rcases row with ⟨α, j⟩
  rcases col with ⟨i, β⟩
  simp [sourceCutM₁, rightShiftTensor, Matrix.single_apply, Matrix.one_apply,
    Prod.ext_iff, eq_comm]

/-- The second raw source cut of the right-shift tensor is the outer product
of the vectorized identity with itself.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem sourceCutM₂_rightShiftTensor (d : ℕ) :
    sourceCutM₂ (rightShiftTensor d) =
      Matrix.vecMulVec (1 : Matrix (Fin d) (Fin d) ℂ).vec
        (1 : Matrix (Fin d) (Fin d) ℂ).vec := by
  ext row col
  rcases row with ⟨α, i⟩
  rcases col with ⟨j, β⟩
  by_cases hαi : α = i <;> by_cases hjβ : j = β <;>
    simp [sourceCutM₂, rightShiftTensor, Matrix.vecMulVec_apply,
      hαi, hjβ, eq_comm]

/-- The right source rank of the right shift is $d^2$, including at $d=0$.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem rightRank_rightShiftTensor (d : ℕ) :
    r[rightShiftTensor d] = d * d := by
  rw [rightRank, sourceCutM₁_rightShiftTensor, Matrix.rank_one]
  simp

/-- The left source rank of the right shift is one for positive physical
dimension.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem leftRank_rightShiftTensor (d : ℕ) [NeZero d] :
    ℓ[rightShiftTensor d] = 1 := by
  rw [leftRank, sourceCutM₂_rightShiftTensor]
  let i : Fin d := Classical.choice (inferInstance : Nonempty (Fin d))
  let v := (1 : Matrix (Fin d) (Fin d) ℂ).vec
  have hle : (Matrix.vecMulVec v v).rank ≤ 1 := Matrix.rank_vecMulVec_le v v
  have hminor :
      (Matrix.vecMulVec v v).submatrix (fun _ : Fin 1 ↦ (i, i))
          (fun _ : Fin 1 ↦ (i, i)) = 1 := by
    ext a b
    simp [v, Matrix.vecMulVec_apply, Matrix.one_apply, Subsingleton.elim a b]
  have hlower := Matrix.rank_submatrix_le (Matrix.vecMulVec v v)
    (fun _ : Fin 1 ↦ (i, i)) (fun _ : Fin 1 ↦ (i, i))
  rw [hminor, Matrix.rank_one] at hlower
  simpa using Nat.le_antisymm hle hlower

/-- The first raw source cut of the left-shift tensor is the outer product of
the vectorized identity with itself.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem sourceCutM₁_leftShiftTensor (d : ℕ) :
    sourceCutM₁ (leftShiftTensor d) =
      Matrix.vecMulVec (1 : Matrix (Fin d) (Fin d) ℂ).vec
        (1 : Matrix (Fin d) (Fin d) ℂ).vec := by
  rw [leftShiftTensor, sourceCutM₁_physicalAdjointTensor,
    sourceCutM₂_rightShiftTensor]
  ext row col
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vec]
  by_cases hr : row.2 = row.1 <;> by_cases hc : col.2 = col.1 <;>
    simp [Matrix.one_apply, hr, hc]

/-- The second raw source cut of the left-shift tensor is the identity on the
product of two physical indices.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem sourceCutM₂_leftShiftTensor (d : ℕ) :
    sourceCutM₂ (leftShiftTensor d) = 1 := by
  rw [leftShiftTensor, sourceCutM₂_physicalAdjointTensor,
    sourceCutM₁_rightShiftTensor]
  ext row col
  simp [Matrix.one_apply]

/-- The right source rank of the left shift is one for positive physical
dimension. This follows from physical adjunction and the right-shift left-rank
calculation.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem rightRank_leftShiftTensor (d : ℕ) [NeZero d] :
    r[leftShiftTensor d] = 1 := by
  rw [leftShiftTensor, rightRank_physicalAdjointTensor,
    leftRank_rightShiftTensor]

/-- The left source rank of the left shift is $d^2$, including at $d=0$.
This follows from physical adjunction and the right-shift right-rank
calculation.

Source: arXiv:1703.09188, lines 450--477 and 1980--1987. -/
theorem leftRank_leftShiftTensor (d : ℕ) :
    ℓ[leftShiftTensor d] = d * d := by
  rw [leftShiftTensor, leftRank_physicalAdjointTensor,
    rightRank_rightShiftTensor]

end MPOTensor
