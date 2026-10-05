/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleVirtualRescaling
import TNLean.MPS.Core.Blocking

/-!
# The two-block uncle tensor

The regular interpolating tensor below is obtained by multiplying both
virtual off-diagonal blocks of the blocked perturbed tensor by \(\varepsilon^{-1}\).
Its value at zero is the explicit uncle tensor in arXiv:1210.6613,
Theorem `thm:unclehamiltonian`, equation "eq:uncletensor-2site".
-/

open scoped Matrix

namespace MPSTensor

/-- Assemble four virtual blocks in the standard finite-index order. -/
noncomputable def uncleBlockMatrix {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (R : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin b) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A R L B)

private theorem uncleBlockMatrix_mul {a b : ℕ}
    (A A' : Matrix (Fin a) (Fin a) ℂ) (R R' : Matrix (Fin a) (Fin b) ℂ)
    (L L' : Matrix (Fin b) (Fin a) ℂ) (B B' : Matrix (Fin b) (Fin b) ℂ) :
    uncleBlockMatrix A R L B * uncleBlockMatrix A' R' L' B' =
      uncleBlockMatrix (A * A' + R * L') (A * R' + R * B')
        (L * A' + B * L') (L * R' + B * B') := by
  change (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks A R L B)) *
    (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks A' R' L' B')) = _
  rw [← map_mul, Matrix.fromBlocks_multiply]
  rfl

private theorem twoBlockVirtualScale_uncleBlockMatrix {a b : ℕ} (z : ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) (R : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin b) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    twoBlockVirtualScale (a := a) z (uncleBlockMatrix A R L B) =
      uncleBlockMatrix A (z • R) (z • L) B := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [twoBlockVirtualScale, uncleBlockMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply]

/-- A general perturbation of a two-block diagonal tensor. -/
noncomputable def twoBlockPerturbation {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (ε : ℂ) :
    MPSTensor d (a + b) := fun i =>
  uncleBlockMatrix (A i + ε • P i) (ε • R i) (ε • L i) (B i + ε • Q i)

/-- The regular two-site tensor obtained after rescaling the off-diagonal
blocks. Its diagonal perturbations disappear at zero. -/
noncomputable def uncleTensorInterpolant {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (ε : ℂ) :
    MPSTensor (blockPhysDim d 2) (a + b) := fun σ =>
  let i := decodeBlock d 2 σ 0
  let j := decodeBlock d 2 σ 1
  uncleBlockMatrix
    ((A i + ε • P i) * (A j + ε • P j) + ε ^ 2 • (R i * L j))
    (A i * R j + R i * B j + ε • (P i * R j + R i * Q j))
    (L i * A j + B i * L j + ε • (L i * P j + Q i * L j))
    ((B i + ε • Q i) * (B j + ε • Q j) + ε ^ 2 • (L i * R j))

/-- The explicit two-block uncle tensor. Only the off-diagonal perturbation
blocks survive in this first-order physical limit. -/
noncomputable def uncleTensor {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    MPSTensor (blockPhysDim d 2) (a + b) := fun σ =>
  let i := decodeBlock d 2 σ 0
  let j := decodeBlock d 2 σ 1
  uncleBlockMatrix (A i * A j) (A i * R j + R i * B j)
    (L i * A j + B i * L j) (B i * B j)

/-- The regular interpolant has the printed uncle tensor as its value at zero. -/
@[simp] theorem uncleTensorInterpolant_zero {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    uncleTensorInterpolant A P B Q R L 0 = uncleTensor A B R L := by
  funext σ
  simp [uncleTensorInterpolant, uncleTensor]

/-- Away from zero, virtual rescaling of the actual blocked perturbed tensor
is exactly the regular interpolant. This is the printed singular-rescaling
step, with its nonzero-parameter hypothesis explicit. -/
theorem twoBlockVirtualScale_blockTensor {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) {ε : ℂ} (hε : ε ≠ 0) :
    (fun σ => twoBlockVirtualScale (a := a) ε⁻¹
      (blockTensor (twoBlockPerturbation A P B Q R L ε) 2 σ)) =
      uncleTensorInterpolant A P B Q R L ε := by
  funext σ
  have hb : blockTensor (twoBlockPerturbation A P B Q R L ε) 2 σ =
      twoBlockPerturbation A P B Q R L ε (decodeBlock d 2 σ 0) *
        twoBlockPerturbation A P B Q R L ε (decodeBlock d 2 σ 1) := by
    simp [blockTensor, Kraus.blockTensor, Kraus.wordOfBlock, List.ofFn_succ,
      Kraus.evalWord, decodeBlock]
  rw [hb]
  simp only [twoBlockPerturbation, uncleBlockMatrix_mul,
    twoBlockVirtualScale_uncleBlockMatrix, uncleTensorInterpolant]
  congr 1
  · simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  · simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, hε]
    abel
  · simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, hε]
    abel
  · simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, add_comm]

/-- The rescaled two-site interpolant is polynomial, hence continuous,
including at the singular parameter of the original rescaling. -/
theorem continuous_uncleTensorInterpolant {d a b : ℕ}
    (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    Continuous (uncleTensorInterpolant A P B Q R L) := by
  apply continuous_pi
  intro σ
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp only [uncleTensorInterpolant, uncleBlockMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] <;>
    fun_prop

end MPSTensor
