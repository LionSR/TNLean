/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermitian matrix spectral decomposition and adjoint identities

This file provides lemmas for Hermitian complex matrices over `Fin D`: the
standard `U * diagonal * Uᴴ` spectral decomposition, extremal eigenvalue
lemmas, scalar-shift spectral formulae, and the adjoint identity for the
matrix-vector dot-product pairing.
-/

open scoped Matrix ComplexOrder

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
  rwa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h

end Matrix.IsHermitian

/-- Smallest eigenvalue of a Hermitian matrix on a nonempty finite space. -/
noncomputable def minEigenvalue [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) : ℝ :=
  (Finset.univ.image hM.eigenvalues).min' (Finset.Nonempty.image Finset.univ_nonempty _)

/-- The smallest eigenvalue is bounded above by every eigenvalue. -/
theorem minEigenvalue_le [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) (i : Fin D) :
    minEigenvalue hM ≤ hM.eigenvalues i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- The smallest eigenvalue is attained by some eigenvector. -/
theorem minEigenvalue_achieved [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    ∃ i : Fin D, hM.eigenvalues i = minEigenvalue hM := by
  have hne := Finset.Nonempty.image Finset.univ_nonempty hM.eigenvalues
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  exact ⟨i, hi⟩

/-- A positive definite Hermitian matrix has positive smallest eigenvalue. -/
theorem minEigenvalue_pos_of_posDef [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) (hPD : M.PosDef) :
    (0 : ℝ) < minEigenvalue hM := by
  simp only [minEigenvalue, Finset.lt_min'_iff, Finset.mem_image, Finset.mem_univ, true_and]
  rintro _ ⟨i, rfl⟩
  exact hM.posDef_iff_eigenvalues_pos.mp hPD i

/-- Largest eigenvalue of a Hermitian matrix on a nonempty finite space. -/
noncomputable def maxEigenvalue [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) : ℝ :=
  (Finset.univ.image hM.eigenvalues).max' (Finset.Nonempty.image Finset.univ_nonempty _)

/-- Every eigenvalue is bounded above by the largest eigenvalue. -/
theorem le_maxEigenvalue [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) (i : Fin D) :
    hM.eigenvalues i ≤ maxEigenvalue hM :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- The largest eigenvalue is attained by some eigenvector. -/
theorem maxEigenvalue_achieved [Nonempty (Fin D)]
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) :
    ∃ i : Fin D, hM.eigenvalues i = maxEigenvalue hM := by
  have hne := Finset.Nonempty.image Finset.univ_nonempty hM.eigenvalues
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
  exact ⟨i, hi⟩

/-- Diagonal form of `diag(v) - c • 1`. -/
theorem diagonal_sub_smul_one (v : Fin D → ℝ) (c : ℝ) :
    Matrix.diagonal (fun j => (↑(v j) : ℂ)) -
        (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
      Matrix.diagonal (fun j => (↑(v j - c) : ℂ)) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
  congr 1
  ext i
  simp [Pi.smul_apply, Complex.ofReal_sub]

/-- Diagonal form of `c • 1 - diag(v)`. -/
theorem diagonal_smul_one_sub (v : Fin D → ℝ) (c : ℝ) :
    (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) -
        Matrix.diagonal (fun j => (↑(v j) : ℂ)) =
      Matrix.diagonal (fun j => (↑(c - v j) : ℂ)) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
  congr 1
  ext i
  simp [Pi.smul_apply, Complex.ofReal_sub]

/-- Spectral form of subtracting a scalar multiple of the identity from a Hermitian matrix. -/
theorem hermitian_sub_scalar_spectral
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) (c : ℝ) :
    M - (↑c : ℂ) • 1 =
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(hM.eigenvalues j - c) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hM.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.prop)
  have h_cI : (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
      U * ((↑c : ℂ) • 1) * Uᴴ := by
    calc
      (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) = (↑c : ℂ) • (U * Uᴴ) := by
        rw [hUU]
      _ = U * ((↑c : ℂ) • 1) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
  calc
    M - (↑c : ℂ) • 1
        = U * Matrix.diagonal (fun j => ↑(hM.eigenvalues j)) * Uᴴ -
            U * ((↑c : ℂ) • 1) * Uᴴ := by
              conv_lhs =>
                rw [hM.spectral_decomp_eq_of_generalIndex]
                rw [h_cI]
    _ = U * (Matrix.diagonal (fun j => ↑(hM.eigenvalues j)) - (↑c : ℂ) • 1) * Uᴴ := by
          noncomm_ring
    _ = U * Matrix.diagonal (fun j => ↑(hM.eigenvalues j - c)) * Uᴴ := by
          congr 1
          congr 1
          exact diagonal_sub_smul_one hM.eigenvalues c

/-- Spectral form of subtracting a Hermitian matrix from a scalar multiple of the identity. -/
theorem smul_one_sub_hermitian_spectral
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian) (c : ℝ) :
    (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - M =
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun j => (↑(c - hM.eigenvalues j) : ℂ)) *
      (↑hM.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hM.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.prop)
  have h_cI : (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
      U * ((↑c : ℂ) • 1) * Uᴴ := by
    calc
      (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) = (↑c : ℂ) • (U * Uᴴ) := by
        rw [hUU]
      _ = U * ((↑c : ℂ) • 1) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
  calc
    (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - M
        = U * ((↑c : ℂ) • 1) * Uᴴ -
            U * Matrix.diagonal (fun j => ↑(hM.eigenvalues j)) * Uᴴ := by
              conv_lhs =>
                rw [hM.spectral_decomp_eq_of_generalIndex]
                rw [h_cI]
    _ = U * ((↑c : ℂ) • 1 -
          Matrix.diagonal (fun j => ↑(hM.eigenvalues j))) * Uᴴ := by
          noncomm_ring
    _ = U * Matrix.diagonal (fun j => ↑(c - hM.eigenvalues j)) * Uᴴ := by
          congr 1
          congr 1
          exact diagonal_smul_one_sub hM.eigenvalues c

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
