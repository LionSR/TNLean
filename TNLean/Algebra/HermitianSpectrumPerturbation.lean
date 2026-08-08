/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Instances.Matrix

/-!
# Simple-spectrum perturbations of Hermitian matrices

A Hermitian matrix has ordered real eigenvalues
`λ₀ ≥ λ₁ ≥ ⋯`.  We split repeated eigenvalues by replacing `λᵢ` with
`λᵢ + ε (d - i)` for `ε > 0`, without changing the chosen eigenvectors.
The resulting matrices have simple spectrum and converge to the original
matrix as `ε → 0`.  Every statement also covers `d = 0`.

## Main declarations

* `Matrix.IsHermitian.orderedPerturbedEigenvalue`: the explicitly split,
  ordered eigenvalue family.
* `Matrix.IsHermitian.simpleSpectrumPerturbation`: the corresponding matrix.
* `Matrix.IsHermitian.simpleSpectrumPerturbation_roots_nodup`: its
  characteristic roots have no repetitions when `ε > 0`.
* `Matrix.IsHermitian.tendsto_simpleSpectrumPerturbation`: convergence as the
  perturbation parameter tends to zero.
-/

open scoped Matrix BigOperators

open Polynomial

namespace Matrix.IsHermitian

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The ordered eigenvalue `λᵢ` shifted by `ε (d - i)`. -/
noncomputable def orderedPerturbedEigenvalue (hA : A.IsHermitian) (ε : ℝ)
    (i : Fin (Fintype.card (Fin d))) : ℝ :=
  hA.eigenvalues₀ i + ε * (Fintype.card (Fin d) - i : ℕ)

/-- For a positive perturbation parameter, the shifted ordered eigenvalues are
strictly decreasing.  The assertion is vacuous when `d = 0`. -/
theorem orderedPerturbedEigenvalue_strictAnti (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    StrictAnti (hA.orderedPerturbedEigenvalue ε) := by
  intro i j hij
  have hlam : hA.eigenvalues₀ j ≤ hA.eigenvalues₀ i :=
    hA.eigenvalues₀_antitone hij.le
  have hoffNat : Fintype.card (Fin d) - (j : ℕ) <
      Fintype.card (Fin d) - (i : ℕ) := by omega
  have hoff : ((Fintype.card (Fin d) - (j : ℕ) : ℕ) : ℝ) <
      ((Fintype.card (Fin d) - (i : ℕ) : ℕ) : ℝ) := by exact_mod_cast hoffNat
  exact add_lt_add_of_le_of_lt hlam (mul_lt_mul_of_pos_left hoff hε)

/-- Positive ordered eigenvalue splitting is injective. -/
theorem orderedPerturbedEigenvalue_injective (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (hA.orderedPerturbedEigenvalue ε) :=
  (hA.orderedPerturbedEigenvalue_strictAnti hε).injective

/-- The Hermitian matrix obtained by retaining the chosen eigenvectors and
splitting its ordered eigenvalues by `ε (d - i)`. -/
noncomputable def simpleSpectrumPerturbation (hA : A.IsHermitian) (ε : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  U * Matrix.diagonal (fun i => (hA.orderedPerturbedEigenvalue ε (e.symm i) : ℂ)) * star U

/-- The explicit perturbation remains Hermitian. -/
theorem simpleSpectrumPerturbation_isHermitian (hA : A.IsHermitian) (ε : ℝ) :
    (hA.simpleSpectrumPerturbation ε).IsHermitian := by
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hdiag : (Matrix.diagonal (fun i =>
      (hA.orderedPerturbedEigenvalue ε (e.symm i) : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  rw [simpleSpectrumPerturbation]
  change (U * Matrix.diagonal _ * star U).IsHermitian
  rw [Matrix.star_eq_conjTranspose]
  exact Matrix.isHermitian_mul_mul_conjTranspose U hdiag

/-- At parameter zero the explicit perturbation is the original matrix. -/
@[simp]
theorem simpleSpectrumPerturbation_zero (hA : A.IsHermitian) :
    hA.simpleSpectrumPerturbation 0 = A := by
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hdiag : (fun i : Fin d =>
      (hA.orderedPerturbedEigenvalue 0 (e.symm i) : ℂ)) =
      RCLike.ofReal ∘ hA.eigenvalues := by
    funext i
    simp [orderedPerturbedEigenvalue, Matrix.IsHermitian.eigenvalues, e]
  rw [simpleSpectrumPerturbation]
  change U * Matrix.diagonal _ * star U = A
  rw [hdiag]
  simpa [U, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem.symm

private theorem charpoly_simpleSpectrumPerturbation (hA : A.IsHermitian) (ε : ℝ) :
    (hA.simpleSpectrumPerturbation ε).charpoly =
      (Matrix.diagonal (fun i =>
        (hA.orderedPerturbedEigenvalue ε
          ((Fintype.equivOfCardEq (Fintype.card_fin _) :
            Fin (Fintype.card (Fin d)) ≃ Fin d).symm i) : ℂ))).charpoly := by
  let e : Fin (Fintype.card (Fin d)) ≃ Fin d :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  rw [simpleSpectrumPerturbation]
  rw [Matrix.charpoly_mul_comm (U * Matrix.diagonal (fun i =>
    (hA.orderedPerturbedEigenvalue ε (e.symm i) : ℂ))) (star U)]
  rw [← Matrix.mul_assoc]
  have hunit : star U * U = 1 := by
    change star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hunit, Matrix.one_mul]

/-- A positive perturbation has simple spectrum: every characteristic root
occurs once.  This includes the zero-dimensional matrix. -/
theorem simpleSpectrumPerturbation_roots_nodup
    (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    (hA.simpleSpectrumPerturbation ε).charpoly.roots.Nodup := by
  classical
  rw [hA.charpoly_simpleSpectrumPerturbation ε, Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    exact Finset.univ.nodup.map <| by
      intro i j hij
      apply (Fintype.equivOfCardEq (Fintype.card_fin _) :
        Fin (Fintype.card (Fin d)) ≃ Fin d).symm.injective
      apply hA.orderedPerturbedEigenvalue_injective hε
      exact Complex.ofReal_injective hij
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

/-- The matrix-valued simple-spectrum perturbation depends continuously on its
real parameter. -/
theorem continuous_simpleSpectrumPerturbation (hA : A.IsHermitian) :
    Continuous hA.simpleSpectrumPerturbation := by
  unfold simpleSpectrumPerturbation orderedPerturbedEigenvalue
  fun_prop

/-- The explicit simple-spectrum perturbations converge to the original matrix
as the real parameter tends to zero. -/
theorem tendsto_simpleSpectrumPerturbation (hA : A.IsHermitian) :
    Filter.Tendsto hA.simpleSpectrumPerturbation (nhds 0) (nhds A) := by
  simpa using hA.continuous_simpleSpectrumPerturbation.tendsto 0

/-- The positive sequence `εₙ = 1 / (n + 1)` gives simple-spectrum matrices
converging to the original Hermitian matrix. -/
theorem tendsto_simpleSpectrumPerturbation_one_div (hA : A.IsHermitian) :
    Filter.Tendsto (fun n : ℕ => hA.simpleSpectrumPerturbation (1 / (n + 1 : ℝ)))
      Filter.atTop (nhds A) :=
  hA.tendsto_simpleSpectrumPerturbation.comp tendsto_one_div_add_atTop_nhds_zero_nat

end Matrix.IsHermitian
