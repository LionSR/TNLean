/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap

/-!
# Translates of a local matrix on the ring

The Hamiltonian of the translates of a local matrix around the ring
(`ManyBody.Interaction.translationInvariant`) is monotone and homogeneous in the local matrix
and positive semidefinite for a positive semidefinite local matrix. A two-sided comparison of
two positive semidefinite matrices transfers a lower bound on the nonzero eigenvalues.
Interactions longer than the ring give zero.

These are the local-to-global comparisons for positive parent interactions
in CPGSV21, arXiv:2011.12127, Section IV.C, lines 1995--2007 and 2183--2187.
-/

open scoped BigOperators ComplexOrder

/-! ### Translates of a local matrix on the ring

Order, scalar multiples and positivity of the Hamiltonian of the translates of a local matrix on
the ring (`ManyBody.Interaction.translationInvariant`), and the transfer of a gap above the
kernel along a two-sided comparison of positive semidefinite matrices. -/

namespace ManyBody

open scoped MatrixOrder

/-- **Gap transfer along a comparison.** If positive semidefinite matrices satisfy
`κ A ≤ B ≤ C A` with `κ, C > 0` and every eigenvalue of `A` other than zero is at least `γ > 0`,
then every eigenvalue of `B` other than zero is at least `κ γ`. -/
theorem forall_hasEigenvalue_of_smul_le_of_le_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) {κ C γ : ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (hγ : 0 < γ) (hLower : (κ : ℂ) • A ≤ B)
    (hUpper : B ≤ (C : ℂ) • A)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ →
      μ = 0 ∨ ((κ * γ : ℝ) : ℂ) ≤ μ := by
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hLower
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
  rw [map_smul] at h1 h2
  refine (forall_hasEigenvalue_iff_norm hB).mpr ?_
  simpa only [div_one] using
    LinearMap.IsPositive.norm_gap_of_smul_le_of_le_smul
      (Matrix.isPositive_toEuclideanLin_iff.mpr hA)
      (Matrix.isPositive_toEuclideanLin_iff.mpr hB) (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using h1)
      (by simpa only [Complex.ofReal_one, one_smul] using h2)
      ((forall_hasEigenvalue_iff_norm hA).mp hGap)

namespace Interaction

variable {α : Type*} [Fintype α] [DecidableEq α] {R N : ℕ} [NeZero N]

/-- The Hamiltonian of the translates on the ring is monotone in the local matrix. -/
theorem hamiltonian_translationInvariant_mono {h h' : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hle : h ≤ h') :
    (translationInvariant N h).hamiltonian ≤ (translationInvariant N h').hamiltonian := by
  by_cases hRN : R ≤ N
  · rw [hamiltonian_translationInvariant_of_le _ hRN, hamiltonian_translationInvariant_of_le _ hRN]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hle
  · rw [hamiltonian_translationInvariant_of_not_le _ hRN,
      hamiltonian_translationInvariant_of_not_le _ hRN]

/-- The Hamiltonian of the translates on the ring of a scalar multiple. -/
theorem hamiltonian_translationInvariant_smul (c : ℂ) (h : Matrix (Fin R → α) (Fin R → α) ℂ) :
    (translationInvariant N (c • h)).hamiltonian = c • (translationInvariant N h).hamiltonian := by
  by_cases hRN : R ≤ N
  · simp only [hamiltonian_translationInvariant_of_le _ hRN, ManyBody.placeAlong_smul,
      Finset.smul_sum]
  · rw [hamiltonian_translationInvariant_of_not_le _ hRN,
      hamiltonian_translationInvariant_of_not_le _ hRN, smul_zero]

/-- A positive semidefinite local matrix has a positive semidefinite Hamiltonian on the ring. -/
theorem posSemidef_hamiltonian_translationInvariant {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : h.PosSemidef) : (translationInvariant N h).hamiltonian.PosSemidef :=
  posSemidef_hamiltonian fun i ↦
    Matrix.nonneg_iff_posSemidef.mp (translationInvariant_term_nonneg hh.nonneg i)

end Interaction

end ManyBody
