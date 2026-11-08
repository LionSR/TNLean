/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTensor

/-!
# The coefficient product for a single uncle domain wall

Concatenating the source's four boundary sectors multiplies the diagonal
blocks and propagates either off-diagonal block once. Products of two
off-diagonal blocks are discarded. This is an operation on the existing
matrix space, with its ordinary vector-space structure; no new algebra
instance is introduced.

Source: arXiv:1210.6613, equation (Sn-def), lines 1077–1095 and Appendix
"intersection-closure", lines 1768–1940. The operation keeps exactly the
single-domain-wall sums in that passage, rather than ordinary products of
uncle matrices with alternating walls.
-/

open scoped Matrix

namespace MPSTensor

variable {a b : ℕ}

private noncomputable def uncleBlockEquiv :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ ≃ₐ[ℂ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv

private theorem uncleBlockEquiv_symm_block
    (A : Matrix (Fin a) (Fin a) ℂ) (R : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin b) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    uncleBlockEquiv.symm (uncleBlockMatrix A R L B) = Matrix.fromBlocks A R L B :=
  uncleBlockEquiv.symm_apply_apply _

/-- Every boundary matrix has four blocks in the source's virtual order. -/
theorem exists_eq_uncleBlockMatrix (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    ∃ A R L B, M = uncleBlockMatrix A R L B := by
  let N := uncleBlockEquiv.symm M
  refine ⟨N.toBlocks₁₁, N.toBlocks₁₂, N.toBlocks₂₁, N.toBlocks₂₂, ?_⟩
  change M = uncleBlockEquiv
    (Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  rw [Matrix.fromBlocks_toBlocks]
  exact (uncleBlockEquiv.apply_symm_apply M).symm

/-- Block assembly preserves addition. -/
theorem uncleBlockMatrix_add
    (A A' : Matrix (Fin a) (Fin a) ℂ) (R R' : Matrix (Fin a) (Fin b) ℂ)
    (L L' : Matrix (Fin b) (Fin a) ℂ) (B B' : Matrix (Fin b) (Fin b) ℂ) :
    uncleBlockMatrix A R L B + uncleBlockMatrix A' R' L' B' =
      uncleBlockMatrix (A + A') (R + R') (L + L') (B + B') := by
  change uncleBlockEquiv (Matrix.fromBlocks A R L B) +
    uncleBlockEquiv (Matrix.fromBlocks A' R' L' B') = _
  rw [← map_add, Matrix.fromBlocks_add]
  rfl

/-- Block assembly preserves scalar multiplication. -/
theorem uncleBlockMatrix_smul (c : ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) (R : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin b) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    c • uncleBlockMatrix A R L B = uncleBlockMatrix (c • A) (c • R) (c • L) (c • B) := by
  change c • uncleBlockEquiv (Matrix.fromBlocks A R L B) = _
  rw [← map_smul, Matrix.fromBlocks_smul]
  rfl

/-- The identity has both diagonal identities and vanishing off-diagonal blocks. -/
theorem uncleBlockMatrix_one :
    uncleBlockMatrix (1 : Matrix (Fin a) (Fin a) ℂ) 0 0
      (1 : Matrix (Fin b) (Fin b) ℂ) = 1 := by
  change uncleBlockEquiv (Matrix.fromBlocks 1 0 0 1) = 1
  rw [Matrix.fromBlocks_one, map_one]

/-- The source coefficient product retaining at most one domain wall;
arXiv:1210.6613, equation (Sn-def) and Appendix intersection proof. -/
noncomputable def uncleBoundaryMul
    (M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  let X := uncleBlockEquiv.symm M
  let Y := uncleBlockEquiv.symm N
  uncleBlockMatrix (X.toBlocks₁₁ * Y.toBlocks₁₁)
    (X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂)
    (X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁)
    (X.toBlocks₂₂ * Y.toBlocks₂₂)

/-- The four explicit source blocks of the boundary product. -/
theorem uncleBoundaryMul_block
    (A A' : Matrix (Fin a) (Fin a) ℂ) (R R' : Matrix (Fin a) (Fin b) ℂ)
    (L L' : Matrix (Fin b) (Fin a) ℂ) (B B' : Matrix (Fin b) (Fin b) ℂ) :
    uncleBoundaryMul (uncleBlockMatrix A R L B) (uncleBlockMatrix A' R' L' B') =
      uncleBlockMatrix (A * A') (A * R' + R * B') (L * A' + B * L') (B * B') := by
  simp only [uncleBoundaryMul, uncleBlockEquiv_symm_block,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]

/-- The boundary product is associative without introducing alternating walls. -/
theorem uncleBoundaryMul_assoc (M N P : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    uncleBoundaryMul (uncleBoundaryMul M N) P = uncleBoundaryMul M (uncleBoundaryMul N P) := by
  obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
  obtain ⟨A', R', L', B', rfl⟩ := exists_eq_uncleBlockMatrix N
  obtain ⟨A'', R'', L'', B'', rfl⟩ := exists_eq_uncleBlockMatrix P
  simp only [uncleBoundaryMul_block, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
  congr 1 <;> abel

/-- The ordinary identity is a left unit for the source boundary product. -/
theorem one_uncleBoundaryMul (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    uncleBoundaryMul 1 M = M := by
  obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
  rw [← uncleBlockMatrix_one (a := a) (b := b), uncleBoundaryMul_block]
  simp

/-- The ordinary identity is a right unit for the source boundary product. -/
theorem uncleBoundaryMul_one (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    uncleBoundaryMul M 1 = M := by
  obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
  rw [← uncleBlockMatrix_one (a := a) (b := b), uncleBoundaryMul_block]
  simp

/-- Right multiplication in the boundary product, as a linear map on the
existing matrix space. -/
noncomputable def uncleBoundaryMulRight (N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ where
  toFun M := uncleBoundaryMul M N
  map_add' M P := by
    obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
    obtain ⟨A', R', L', B', rfl⟩ := exists_eq_uncleBlockMatrix P
    obtain ⟨A'', R'', L'', B'', rfl⟩ := exists_eq_uncleBlockMatrix N
    simp only [uncleBlockMatrix_add, uncleBoundaryMul_block, Matrix.add_mul]
    congr 1 <;> abel
  map_smul' c M := by
    obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
    obtain ⟨A', R', L', B', rfl⟩ := exists_eq_uncleBlockMatrix N
    simp only [uncleBlockMatrix_smul, uncleBoundaryMul_block, Matrix.smul_mul, smul_add,
      RingHom.id_apply]

/-- Left multiplication in the boundary product, as a linear map. -/
noncomputable def uncleBoundaryMulLeft (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ where
  toFun N := uncleBoundaryMul M N
  map_add' N P := by
    obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
    obtain ⟨A', R', L', B', rfl⟩ := exists_eq_uncleBlockMatrix N
    obtain ⟨A'', R'', L'', B'', rfl⟩ := exists_eq_uncleBlockMatrix P
    simp only [uncleBlockMatrix_add, uncleBoundaryMul_block, Matrix.mul_add]
    congr 1 <;> abel
  map_smul' c N := by
    obtain ⟨A, R, L, B, rfl⟩ := exists_eq_uncleBlockMatrix M
    obtain ⟨A', R', L', B', rfl⟩ := exists_eq_uncleBlockMatrix N
    simp only [uncleBlockMatrix_smul, uncleBoundaryMul_block, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

@[simp] theorem uncleBoundaryMulRight_apply
    (N M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    uncleBoundaryMulRight N M = uncleBoundaryMul M N := rfl

@[simp] theorem uncleBoundaryMulLeft_apply
    (M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    uncleBoundaryMulLeft M N = uncleBoundaryMul M N := rfl

end MPSTensor
