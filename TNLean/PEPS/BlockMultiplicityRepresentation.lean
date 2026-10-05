/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBlockMultiplicityState

/-!
# Arbitrary positive multiplicities of matrix representation blocks

The copy multiplicities need not equal the irreducible dimensions. To restore
mᵢ copies of a block, the single-copy source uses the fourth-root weight mᵢ^(1/4).
Two endpoint weights give √mᵢ, exactly the normalization canceled by the
mᵢ-copy bond isometry. At mᵢ=dᵢ this is the Section 7 construction.

Source: SCP10, arXiv:1001.3807, the semi-regular block decomposition in
Section 4.1 and the bond isometry of Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix Kronecker
namespace TNLean.PEPS
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

/-- Repeat each supplied matrix representation by an arbitrary copy multiplicity. -/
def blockMultiplicityRepresentation (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    G →* Matrix (Σ i, Fin (d i) × Fin (m i)) (Σ i, Fin (d i) × Fin (m i)) ℂ where
  toFun g := Matrix.blockDiagonal' (fun i => D i g ⊗ₖ (1 : Matrix (Fin (m i)) (Fin (m i)) ℂ))
  map_one' := by
    simp only [map_one, Matrix.one_kronecker_one]
    exact Matrix.blockDiagonal'_one
  map_mul' g h := by
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, map_mul]

/-- The source fourth-root weights adapted to the desired copy multiplicities. -/
def blockMultiplicityRootWeight (d m : I → ℕ) :
    Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ :=
  Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) •
    (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))

/-- Dimension multiplicities recover the established regular block representation. -/
@[simp] theorem blockMultiplicityRepresentation_self (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockMultiplicityRepresentation d d D = multiplicityRestoredRepresentation d D := rfl

omit [Group G] [Fintype I] in
/-- Dimension multiplicities recover the source's fourth-root dimension weights. -/
@[simp] theorem blockMultiplicityRootWeight_self (d : I → ℕ) :
    blockMultiplicityRootWeight d d = blockFourthRootWeight d := rfl

/-- A single endpoint retains one fourth-root copy factor in every block. -/
theorem blockMultiplicityRootWeight_mul (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    blockMultiplicityRootWeight d m * blockMatrixRepresentation d D g =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) • D i g) := by
  change Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) •
    (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) * Matrix.blockDiagonal' (fun i => D i g) = _
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  rw [Matrix.smul_mul, Matrix.one_mul]

/-- The same endpoint factor appears on the other side of a block matrix. -/
theorem mul_blockMultiplicityRootWeight (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    blockMatrixRepresentation d D g * blockMultiplicityRootWeight d m =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) • D i g) := by
  change Matrix.blockDiagonal' (fun i => D i g) *
    Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) •
      (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) = _
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  rw [Matrix.mul_smul, Matrix.mul_one]

/-- Copy weights commute with all matrices of the block representation. -/
theorem blockMultiplicityRootWeight_commute (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    Commute (blockMultiplicityRootWeight d m) (blockMatrixRepresentation d D g) := by
  exact (blockMultiplicityRootWeight_mul d m D g).trans
    (mul_blockMultiplicityRootWeight d m D g).symm

/-- The two endpoint copy weights combine to the square-root normalization
required by the actual mᵢ-copy restoration map. -/
theorem blockMultiplicityRootWeight_sq_mul (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    blockMultiplicityRootWeight d m ^ 2 * blockMatrixRepresentation d D g =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g) := by
  change Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) •
    (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) ^ 2 * Matrix.blockDiagonal' (fun i => D i g) = _
  rw [pow_two, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [← pow_two, Complex.ofReal_sqrt_sq _ (Real.sqrt_nonneg _)]

end TNLean.PEPS
