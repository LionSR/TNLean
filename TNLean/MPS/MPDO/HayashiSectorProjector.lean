/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Algebra.ScalarCommutant
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Canonical projectors of a Hayashi--Markov decomposition

A quantum-Markov decomposition of a tripartite state splits its middle
physical space as
\[
  \mathcal H_B=\bigoplus_k \mathcal H^L_k\otimes\mathcal H^R_k.
\]
This file defines the corresponding one-site projectors in the original
physical basis and proves that they are orthogonal and resolve the identity.

The projectors $Q_k$ are defined in arXiv:1606.00608, Appendix C.2,
lines 1364--1368.  Their resolution of the identity is recalled at lines
1693--1697.

## Main declarations

* `MPOTensor.EtaStructure.coordinateSectorProjection`
* `MPOTensor.EtaStructure.sectorProjection`
* `MPOTensor.EtaStructure.sectorProjection_isOrthogonal`
* `MPOTensor.EtaStructure.sectorProjection_mul_eq_zero`
* `MPOTensor.EtaStructure.sum_sectorProjection`
-/

open scoped Matrix BigOperators

namespace MPOTensor.EtaStructure

variable {d : ℕ}
  {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-- The coordinate projection onto one summand
$\mathcal H^L_k\otimes\mathcal H^R_k$ of the middle-site Markov
decomposition.

Source: arXiv:1606.00608, Appendix C.2, lines 1364--1368. -/
noncomputable def coordinateSectorProjection (hη : EtaStructure rho)
    (k : Fin hη.m) :
    Matrix (Σ j : Fin hη.m, Fin (hη.dL j) × Fin (hη.dR j))
      (Σ j : Fin hη.m, Fin (hη.dL j) × Fin (hη.dR j)) ℂ :=
  Matrix.blockProjection (n := fun j => Fin (hη.dL j) × Fin (hη.dR j)) k

private theorem coordinateSectorProjection_isStarProjection
    (hη : EtaStructure rho) (k : Fin hη.m) :
    IsStarProjection (hη.coordinateSectorProjection k) := by
  classical
  rw [isStarProjection_iff']
  constructor
  · rw [coordinateSectorProjection, Matrix.blockProjection,
      ← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    by_cases hi : i = k
    · simp [hi]
    · simp [hi]
  · simp only [Matrix.star_eq_conjTranspose]
    rw [coordinateSectorProjection, Matrix.blockProjection,
      Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext i
    by_cases hi : i = k
    · simp [hi]
    · simp [hi]

private theorem sum_coordinateSectorProjection (hη : EtaStructure rho) :
    ∑ k : Fin hη.m, hη.coordinateSectorProjection k = 1 := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · simp [coordinateSectorProjection, Matrix.blockProjection,
        Matrix.one_apply]
    · intro k _ hki
      have hik : i ≠ k := Ne.symm hki
      simp [coordinateSectorProjection, Matrix.blockProjection, hik]
    · simp
  · simp [Matrix.sum_apply, coordinateSectorProjection, Matrix.blockProjection,
      Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]

private noncomputable def basisSectorProjection (hη : EtaStructure rho)
    (k : Fin hη.m) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.reindex hη.decompB.symm hη.decompB.symm
    (hη.coordinateSectorProjection k)

private theorem sum_basisSectorProjection (hη : EtaStructure rho) :
    ∑ k : Fin hη.m, basisSectorProjection hη k = 1 := by
  classical
  ext i j
  have hentry := congrFun (congrFun (sum_coordinateSectorProjection hη)
    (hη.decompB i)) (hη.decompB j)
  simpa [basisSectorProjection, Matrix.sum_apply, Matrix.reindex_apply,
    Matrix.one_apply] using hentry

private theorem basisSectorProjection_isStarProjection
    (hη : EtaStructure rho) (k : Fin hη.m) :
    IsStarProjection (basisSectorProjection hη k) := by
  rw [isStarProjection_iff']
  obtain ⟨hidem, hstar⟩ :=
    (isStarProjection_iff'.mp (coordinateSectorProjection_isStarProjection hη k))
  constructor
  · change
      Matrix.reindex hη.decompB.symm hη.decompB.symm
          (hη.coordinateSectorProjection k) *
        Matrix.reindex hη.decompB.symm hη.decompB.symm
          (hη.coordinateSectorProjection k) =
      Matrix.reindex hη.decompB.symm hη.decompB.symm
          (hη.coordinateSectorProjection k)
    calc
      _ = Matrix.reindex hη.decompB.symm hη.decompB.symm
          (hη.coordinateSectorProjection k * hη.coordinateSectorProjection k) := by
        simpa only [Matrix.coe_reindexLinearEquiv] using
          (Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
            hη.decompB.symm hη.decompB.symm hη.decompB.symm
            (hη.coordinateSectorProjection k) (hη.coordinateSectorProjection k))
      _ = _ := congrArg
        (Matrix.reindex hη.decompB.symm hη.decompB.symm) hidem
  · simp only [Matrix.star_eq_conjTranspose]
    change
      (Matrix.reindex hη.decompB.symm hη.decompB.symm
        (hη.coordinateSectorProjection k))ᴴ =
      Matrix.reindex hη.decompB.symm hη.decompB.symm
        (hη.coordinateSectorProjection k)
    rw [Matrix.conjTranspose_reindex]
    simpa only [Matrix.star_eq_conjTranspose] using congrArg
      (Matrix.reindex hη.decompB.symm hη.decompB.symm) hstar

/-- The projector $Q_k$ onto the $k$-th Markov summand, transported to the
original middle-site basis.  If $E_k$ is the coordinate block projection,
then
\[
  Q_k=U_B^*\,E_k\,U_B,
\]
where $U_B$ is the unitary implementing the middle-site Markov decomposition.

Source: arXiv:1606.00608, Appendix C.2, lines 1364--1368 and 1437--1440. -/
noncomputable def sectorProjection (hη : EtaStructure rho) (k : Fin hη.m) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ *
    basisSectorProjection hη k *
    (hη.U_B : Matrix (Fin d) (Fin d) ℂ)

/-- Each canonical Hayashi-sector matrix is an orthogonal projection.

Source: arXiv:1606.00608, Appendix C.2, lines 1364--1368. -/
theorem sectorProjection_isOrthogonal (hη : EtaStructure rho) (k : Fin hη.m) :
    IsOrthogonalProjection (hη.sectorProjection k) := by
  apply IsStarProjection.isOrthogonalProjection
  apply IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
    (basisSectorProjection_isStarProjection hη k)
    (hη.U_B : Matrix (Fin d) (Fin d) ℂ)
  simpa [Matrix.star_eq_conjTranspose] using
    Unitary.mul_star_self_of_mem hη.U_B.prop

/-- The canonical Hayashi-sector projections resolve the physical identity:
$\sum_k Q_k=\mathbf 1$.

Source: arXiv:1606.00608, Appendix C.2, lines 1693--1697. -/
theorem sum_sectorProjection (hη : EtaStructure rho) :
    ∑ k : Fin hη.m, hη.sectorProjection k = 1 := by
  classical
  simp_rw [sectorProjection]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_basisSectorProjection,
    Matrix.mul_one]
  simpa [Matrix.star_eq_conjTranspose] using
    Unitary.coe_star_mul_self hη.U_B

/-- Projections onto distinct Hayashi sectors are mutually orthogonal.

Source: arXiv:1606.00608, Appendix C.2, lines 1364--1368. -/
theorem sectorProjection_mul_eq_zero (hη : EtaStructure rho)
    {k l : Fin hη.m} (hkl : k ≠ l) :
    hη.sectorProjection k * hη.sectorProjection l = 0 := by
  exact orthogonalProjection_mul_eq_zero_of_sum_eq_one
    hη.sectorProjection hη.sectorProjection_isOrthogonal
    hη.sum_sectorProjection hkl

end MPOTensor.EtaStructure
