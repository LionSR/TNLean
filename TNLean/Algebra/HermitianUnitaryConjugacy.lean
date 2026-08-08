/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Unitary conjugacy of Hermitian matrices

Two finite complex Hermitian matrices with the same characteristic polynomial are unitarily
conjugate. The proof identifies their ordered eigenvalue lists and compares their unitary spectral
decompositions.
-/

open scoped Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two finite complex Hermitian matrices with the same characteristic polynomial are unitarily
conjugate. -/
theorem exists_unitary_conj_of_charpoly_eq {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hcharpoly : A.charpoly = B.charpoly) :
    ∃ U : Matrix.unitaryGroup n ℂ, B = (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ) := by
  have heigenvalues : hA.eigenvalues = hB.eigenvalues :=
    (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hcharpoly
  let U : Matrix.unitaryGroup n ℂ := hB.eigenvectorUnitary * star hA.eigenvectorUnitary
  refine ⟨U, ?_⟩
  change B = Unitary.conjStarAlgAut ℂ _ U A
  rw [hA.spectral_theorem, hB.spectral_theorem]
  simp only [U, heigenvalues, Unitary.conjStarAlgAut_mul_apply]
  rw [← Unitary.conjStarAlgAut_symm]
  exact congrArg (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary)
    ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary).symm_apply_apply _).symm


end Matrix.IsHermitian
