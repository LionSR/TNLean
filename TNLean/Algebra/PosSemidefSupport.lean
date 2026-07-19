/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import TNLean.Algebra.OrthogonalProjection

/-!
# Support projections of positive semidefinite matrices

This file contains the spectral support projection of a positive semidefinite
matrix and its elementary algebraic properties.  These facts depend only on
finite-dimensional complex matrix theory.

## Main declarations

* `Matrix.PosSemidef.supportProj` -- the orthogonal projection onto the support
  of a positive semidefinite matrix.
* `Matrix.PosSemidef.supportProj_mul_self` -- the support projection absorbs the
  matrix on the left.
* `Matrix.PosSemidef.mul_supportProj_self` -- the corresponding right absorption.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix.PosSemidef

variable {D : ℕ} {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)

/-- The orthogonal projection onto the support of a positive semidefinite matrix. -/
noncomputable def supportProj : Matrix (Fin D) (Fin D) ℂ :=
  let U : Matrix (Fin D) (Fin D) ℂ := ↑hρ.isHermitian.eigenvectorUnitary
  let sgnEig : Fin D → ℂ := fun i => if 0 < hρ.isHermitian.eigenvalues i then 1 else 0
  U * Matrix.diagonal sgnEig * Uᴴ

private noncomputable def supportU : Matrix (Fin D) (Fin D) ℂ :=
  (↑hρ.isHermitian.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)

private noncomputable def supportIndicator : Fin D → ℂ :=
  fun i => if 0 < hρ.isHermitian.eigenvalues i then 1 else 0

private lemma supportProj_eq :
    hρ.supportProj = hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ := by
  rfl

private lemma supportIndicator_star : star hρ.supportIndicator = hρ.supportIndicator := by
  classical
  ext i
  simp [supportIndicator]

private lemma supportIndicator_sq :
    ∀ i, hρ.supportIndicator i * hρ.supportIndicator i = hρ.supportIndicator i := by
  classical
  intro i
  simp [supportIndicator]

/-- The support projection is Hermitian. -/
theorem supportProj_isHermitian : hρ.supportProj.IsHermitian := by
  classical
  rw [hρ.supportProj_eq]
  have hsgn : star hρ.supportIndicator = hρ.supportIndicator :=
    hρ.supportIndicator_star
  change (hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ)ᴴ =
    hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hsgn,
    Matrix.mul_assoc]

/-- The support projection is idempotent. -/
theorem supportProj_idem : hρ.supportProj * hρ.supportProj = hρ.supportProj := by
  classical
  have hUU : hρ.supportUᴴ * hρ.supportU = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    change star (↑hρ.isHermitian.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) *
      (↑hρ.isHermitian.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) = 1
    exact Matrix.UnitaryGroup.star_mul_self hρ.isHermitian.eigenvectorUnitary
  rw [hρ.supportProj_eq]
  change hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ *
      (hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ) =
    hρ.supportU * Matrix.diagonal hρ.supportIndicator * hρ.supportUᴴ
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc hρ.supportUᴴ hρ.supportU, hUU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal hρ.supportIndicator),
    Matrix.diagonal_mul_diagonal,
    show (fun i => hρ.supportIndicator i * hρ.supportIndicator i) =
      hρ.supportIndicator from funext hρ.supportIndicator_sq]

/-- The support projection is an orthogonal projection. -/
theorem isOrthogonalProjection_supportProj : IsOrthogonalProjection hρ.supportProj :=
  ⟨hρ.supportProj_isHermitian, hρ.supportProj_idem⟩

/-- The support projection absorbs the matrix on the left. -/
theorem supportProj_mul_self : hρ.supportProj * ρ = ρ := by
  classical
  let hH : ρ.IsHermitian := hρ.isHermitian
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set sgn : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    simp [U]
  have hsign_mul_eig : sgn * (fun j => (↑(hH.eigenvalues j) : ℂ)) =
      (fun j => (↑(hH.eigenvalues j) : ℂ)) := by
    ext i
    simp only [sgn, Pi.mul_apply]
    split
    · simp
    · rename_i hi
      push Not at hi
      have hnonneg : 0 ≤ hH.eigenvalues i := hρ.eigenvalues_nonneg i
      simp [le_antisymm hi hnonneg]
  have hρspec : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hH.spectral_theorem
  have hPdef : hρ.supportProj = U * Matrix.diagonal sgn * Uᴴ := by
    simp [supportProj, U, sgn]
  rw [hPdef, hρspec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal sgn), Matrix.diagonal_mul_diagonal,
    show (fun i => sgn i * ↑(hH.eigenvalues i)) =
      (fun j => (↑(hH.eigenvalues j) : ℂ)) from hsign_mul_eig]

/-- The support projection absorbs the matrix on the right. -/
theorem mul_supportProj_self : ρ * hρ.supportProj = ρ := by
  have h := congrArg Matrix.conjTranspose hρ.supportProj_mul_self
  simpa [Matrix.conjTranspose_mul, hρ.supportProj_isHermitian.eq,
    hρ.isHermitian.eq] using h

/-- If the matrix annihilates a vector, then its support projection does also. -/
theorem supportProj_mulVec_eq_zero_of_mulVec_eq_zero
    (v : Fin D → ℂ) (hv : ρ *ᵥ v = 0) : hρ.supportProj *ᵥ v = 0 := by
  classical
  let hH : ρ.IsHermitian := hρ.isHermitian
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  set s : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    simp [U]
  set w : Fin D → ℂ := Uᴴ *ᵥ v
  have hρspec : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hH.spectral_theorem
  have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
    have hρv :
        (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 := by
      rw [← hρspec]
      exact hv
    have hUΛw : U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hρv
    have hUΛw' :
        Uᴴ *ᵥ
          (U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w)) = 0 := by
      simp [hUΛw]
    have :
        (Uᴴ * U) *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hUΛw'
    simpa [Matrix.mulVec_mulVec, hUU] using this
  have hcomp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := fun j => by
    have h := congrFun hΛw j
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using h
  have hSw : Matrix.diagonal s *ᵥ w = 0 := by
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : 0 < hH.eigenvalues j
    · have hwj : w j = 0 := by
        have heig : (↑(hH.eigenvalues j) : ℂ) ≠ 0 := by
          exact_mod_cast ne_of_gt hj
        exact (mul_eq_zero.mp (hcomp j)).resolve_left heig
      simp [s, hj, hwj]
    · simp [s, hj]
  have hPdef : hρ.supportProj = U * Matrix.diagonal s * Uᴴ := by
    rfl
  have hPeval :
      (U * Matrix.diagonal s * Uᴴ) *ᵥ v = U *ᵥ (Matrix.diagonal s *ᵥ w) := by
    simp [w, U, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp [hPdef, hPeval, hSw]

end Matrix.PosSemidef
