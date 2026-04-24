/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermitian matrix helpers

This file provides small reusable helpers for Hermitian complex matrices over
`Fin D`: the unitary identities for the eigenvector matrix, the standard
`U * diagonal * Uᴴ` spectral decomposition, and the adjoint identity for the
matrix-vector dot-product pairing.
-/

open scoped Matrix

variable {D : ℕ}

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Spectral decomposition of a Hermitian complex matrix** (polymorphic in the
index type): `M = U * diagonal λ * Uᴴ` where `U = hM.eigenvectorUnitary` and
`λ = hM.eigenvalues` are the eigenvector unitary and real eigenvalues provided
by Mathlib's Hermitian spectral theorem. -/
theorem spectral_decomp_eq_of_generalIndex
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  convert h using 2

end Matrix.IsHermitian

/-- `Uᴴ * U = 1` for the eigenvector unitary of a Hermitian matrix. -/
theorem eig_conj_mul [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary

/-- `U * Uᴴ = 1` for the eigenvector unitary of a Hermitian matrix. -/
theorem eig_mul_conj [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.prop

/-- The spectral decomposition of a Hermitian matrix in `U * diagonal * Uᴴ` form. -/
theorem spectral_decomp_eq [DecidableEq (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ :=
  hM.spectral_decomp_eq_of_generalIndex

namespace HermitianHelpers

/-- Adjoint identity for the matrix-vector dot-product pairing. -/
theorem dotProduct_mulVec_conjTranspose
    (M : Matrix (Fin D) (Fin D) ℂ) (x y : Fin D → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

end HermitianHelpers
