/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PiMatrixRepresentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Non-unital matrix representation regression tests

The decomposition signatures allow zero-dimensional source factors and zero
multiplicities. A non-symmetric idempotent checks that the range factorization
requires no orthogonal-projection hypothesis.
-/

-- These regressions intentionally inspect declaration and kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix

namespace PiMatrixRepresentationTest

private def oblique : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 0]

private theorem oblique_idempotent : oblique * oblique = oblique := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_two]

example : oblique.transpose ≠ oblique := by
  intro h
  have hentry := congrArg (fun M => M 0 1) h
  norm_num [oblique, Matrix.transpose_apply] at hentry

example : ∃ (W : Matrix (Fin 2) (Fin oblique.rank) ℚ)
    (V : Matrix (Fin oblique.rank) (Fin 2) ℚ), V * W = 1 ∧ W * V = oblique :=
  Matrix.exists_rankFactorization_of_idempotent oblique oblique_idempotent

private def obliqueRepresentation : Matrix (Fin 1) (Fin 1) ℚ →ₗ[ℚ]
    Matrix (Fin 2) (Fin 2) ℚ where
  toFun M := M 0 0 • oblique
  map_add' M N := by simp [add_smul]
  map_smul' a M := by simp [smul_smul]

private theorem obliqueRepresentation_mul (M N : Matrix (Fin 1) (Fin 1) ℚ) :
    obliqueRepresentation (M * N) = obliqueRepresentation M * obliqueRepresentation N := by
  change (M * N) 0 0 • oblique = (M 0 0 • oblique) * (N 0 0 • oblique)
  rw [Matrix.smul_mul, Matrix.mul_smul, oblique_idempotent, smul_smul]
  simp [Matrix.mul_apply]

example : obliqueRepresentation 1 ≠ 1 := by
  intro h
  have hentry := congrArg (fun M ↦ M 1 1) h
  norm_num [obliqueRepresentation, oblique] at hentry

-- This representation has a proper, non-self-adjoint support. The
-- reconstructed support remains rho(1), rather than becoming ambient 1.
example : ∃ (m : ℕ)
    (W : Fin m → Matrix (Fin 2) (Fin 1) ℚ)
    (V : Fin m → Matrix (Fin 1) (Fin 2) ℚ),
    (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
    (∀ M, obliqueRepresentation M = ∑ μ, W μ * M * V μ) ∧
    oblique = ∑ μ, W μ * V μ := by
  obtain ⟨m, W, V, hVW, hsum⟩ :=
    Matrix.exists_multiplicativeLinearMap_blocks_of_fintype
      obliqueRepresentation obliqueRepresentation_mul
  exact ⟨m, W, V, hVW, hsum, by simpa [obliqueRepresentation] using hsum 1⟩

example :
    ∃ (m : Fin 1 → ℕ)
      (W : ∀ c, Fin (m c) → Matrix (Fin 2) (Fin 0) ℚ)
      (V : ∀ c, Fin (m c) → Matrix (Fin 0) (Fin 2) ℚ),
      (∀ c μ ν, V c μ * W c ν = if μ = ν then 1 else 0) ∧
      (∀ c d, c ≠ d → ∀ μ ν, V c μ * W d ν = 0) ∧
      (∀ M : Fin 1 → Matrix (Fin 0) (Fin 0) ℚ,
        (0 : Matrix (Fin 2) (Fin 2) ℚ) = ∑ c, ∑ μ, W c μ * M c * V c μ) ∧
      (0 : Matrix (Fin 2) (Fin 2) ℚ) = ∑ c, ∑ μ, W c μ * V c μ := by
  simpa using Matrix.exists_piMatrix_blocks (K := ℚ) (D := 2) (fun _ : Fin 1 => 0)
    0 (by simp)

-- A zero representation of positive-dimensional factors is allowed too;
-- no nonzero-representation or unitality assumption is hidden in the API.
example :
    ∃ (m : Fin 2 → ℕ)
      (W : ∀ c, Fin (m c) → Matrix (Fin 3) (Fin 2) ℚ)
      (V : ∀ c, Fin (m c) → Matrix (Fin 2) (Fin 3) ℚ),
      (∀ c μ ν, V c μ * W c ν = if μ = ν then 1 else 0) ∧
      (∀ c d, c ≠ d → ∀ μ ν, V c μ * W d ν = 0) ∧
      (∀ M : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ,
        (0 : Matrix (Fin 3) (Fin 3) ℚ) = ∑ c, ∑ μ, W c μ * M c * V c μ) ∧
      (0 : Matrix (Fin 3) (Fin 3) ℚ) = ∑ c, ∑ μ, W c μ * V c μ := by
  simpa using Matrix.exists_piMatrix_blocks (K := ℚ) (D := 3) (fun _ : Fin 2 => 2)
    0 (by simp)

-- The product representation theorem does not require an inhabited family.
example :
    ∃ (m : Fin 0 → ℕ)
      (W : ∀ c, Fin (m c) → Matrix (Fin 2) (Fin 1) ℚ)
      (V : ∀ c, Fin (m c) → Matrix (Fin 1) (Fin 2) ℚ),
      (∀ c μ ν, V c μ * W c ν = if μ = ν then 1 else 0) ∧
      (∀ c d, c ≠ d → ∀ μ ν, V c μ * W d ν = 0) ∧
      (∀ M : Fin 0 → Matrix (Fin 1) (Fin 1) ℚ,
        (0 : Matrix (Fin 2) (Fin 2) ℚ) = ∑ c, ∑ μ, W c μ * M c * V c μ) ∧
      (0 : Matrix (Fin 2) (Fin 2) ℚ) = ∑ c, ∑ μ, W c μ * V c μ := by
  exact Matrix.exists_piMatrix_blocks (K := ℚ) (D := 2) (fun _ : Fin 0 => 1)
    0 (by simp)

/--
info: 'Matrix.exists_rankFactorization_of_idempotent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_rankFactorization_of_idempotent
/--
info: 'Matrix.exists_matrixUnitBlocks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_matrixUnitBlocks
/--
info: 'Matrix.exists_piMatrix_blocks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_piMatrix_blocks

end PiMatrixRepresentationTest
