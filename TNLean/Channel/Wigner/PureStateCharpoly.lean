/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianUnitaryConjugacy
import TNLean.Channel.Wigner.ProjectivePureState

/-!
# Pure-state matrices from characteristic polynomials

A Hermitian matrix whose characteristic polynomial agrees with that of a normalized pure-state
matrix is itself a normalized pure-state matrix. Unitary conjugacy of Hermitian matrices reduces the
claim to the unitary action on projective rays.

## Main declaration

* `Projectivization.exists_pureStateMatrix_eq_of_isHermitian_charpoly_eq`
-/

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

variable {d : ℕ}

/-- A Hermitian matrix with the characteristic polynomial of a normalized pure-state matrix is the
normalized pure-state matrix of another projective ray. This supplies the pure-state image
identification used in the spectrum-preserving-map argument of Wolf, Chapter 1, lines 287--296. -/
theorem exists_pureStateMatrix_eq_of_isHermitian_charpoly_eq
    (A : Matrix (Fin d) (Fin d) ℂ) (p : ℙ ℂ (Fin d → ℂ)) (hA : A.IsHermitian)
    (hcharpoly : A.charpoly = (pureStateMatrix p).charpoly) :
    ∃ q : ℙ ℂ (Fin d → ℂ), pureStateMatrix q = A := by
  have hP : (pureStateMatrix p).IsHermitian :=
    (isOrthogonalProjection_pureStateMatrix p).1
  have heigenvalues : hP.eigenvalues = hA.eigenvalues :=
    (hP.eigenvalues_eq_eigenvalues_iff hA).mpr hcharpoly.symm
  let oneFin : Matrix (Fin d) (Fin d) ℂ := 1
  have hconj : ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U * star U = oneFin ∧ A = U * pureStateMatrix p * star U := by
    letI : DecidableEq (Fin d) := Classical.decEq (Fin d)
    have hcharpoly' : (pureStateMatrix p).charpoly = A.charpoly :=
      (hP.eigenvalues_eq_eigenvalues_iff hA).mp heigenvalues
    rcases Matrix.IsHermitian.exists_unitary_conj_of_charpoly_eq hP hA hcharpoly' with
      ⟨U, hU⟩
    refine ⟨U, ?_, hU⟩
    calc
      (U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff.mp U.property
      _ = oneFin := by
        ext i j
        simp [oneFin, Matrix.one_apply]
  rcases hconj with ⟨Umat, hUmat, hconj⟩
  have hUmat' : Umat * star Umat = 1 := by simpa only [oneFin] using hUmat
  let U : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨Umat, Matrix.mem_unitaryGroup_iff.mpr hUmat'⟩
  refine ⟨unitaryAction U p, ?_⟩
  calc
    pureStateMatrix (unitaryAction U p) =
        (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := pureStateMatrix_unitaryAction U p
    _ = A := hconj.symm

end Projectivization
