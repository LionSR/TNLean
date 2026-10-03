/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductSpectralGap
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The uniform gap in independent-bond coordinates

In independent-bond coordinates, the parent Hamiltonian of a unit bond vector
`η` is the sum of the penalties `1 - |η⟩⟨η|` over all bonds. It is positive
semidefinite, its spectrum contains zero, and every other spectral value is at
least one, for every chain length. Along the normalized bond interpolation the
local penalty is a continuous orthogonal projection of operator norm at most
one, so the gap bound is uniform in both the parameter and the chain length.

These are the spectral assertions for the bond interpolation of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma` and source lines 899–906. The corresponding statements in
physical-site coordinates are in `BondProductSpectralGap`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- The penalty of a unit bond vector has operator norm at most one.
Source: arXiv:1010.3732, Section II.C.1, the bound on interaction strengths. -/
theorem bondPenalty_norm_le_one {q : ℕ} (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) : ‖bondPenalty η‖ ≤ 1 :=
  (bondPenalty_isStarProjection η hη).norm_le _

/-- The independent-bond parent Hamiltonian of a unit bond vector is positive
semidefinite. Source: arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
theorem bondProductParentHamiltonian_posSemidef {q N : ℕ} (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) (hN : 1 ≤ N) :
    (bondProductParentHamiltonian η hN).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun i _ =>
    Matrix.nonneg_iff_posSemidef.mp (bondPenaltyAt_isStarProjection η hη hN i).nonneg

/-- The independent-bond parent Hamiltonian of a unit bond vector has ground
energy zero, and every other spectral value is at least one, uniformly in the
chain length and the bond vector. Source: arXiv:1010.3732, Section II.F.2,
source lines 899–906. -/
theorem bondProductParentHamiltonian_spectrum_gap_one {q N : ℕ} (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) (hN : 1 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ (bondProductParentHamiltonian η hN) ∧
      ∀ z ∈ spectrum ℂ (bondProductParentHamiltonian η hN),
        0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  constructor
  · have hker : LinearMap.ker (bondProductParentHamiltonianLin η hN) ≠ ⊥ := by
      rw [bondProductParentHamiltonian_groundSpace_eq_span η hη hN, Ne,
        Submodule.span_singleton_eq_bot]
      exact bondProductState_ne_zero η hη N
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
    simpa [bondProductParentHamiltonianLin, bondMatrixEquiv_symm_eq_toEuclideanLin] using hker
  · apply spectrum_separated_of_quadratic_gap _
      (bondProductParentHamiltonian_posSemidef η hη hN)
    intro v
    simpa [bondProductParentHamiltonianLin, bondMatrixEquiv_symm_eq_toEuclideanLin] using
      bondProductParentHamiltonian_gap_one η hη hN v

/-- Along the normalized bond interpolation, the local penalty is a continuous
orthogonal projection of norm at most one, and the independent-bond
Hamiltonians have ground energy zero and a gap of at least one for every real
parameter and every positive chain length, including both endpoints.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma` and source
lines 899–906. -/
theorem normalizedBondInterpolation_parent_uniform_gap {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (fun γ : ℝ => bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)) ∧
    (∀ γ : ℝ, IsStarProjection (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)) ∧
      ‖bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)‖ ≤ 1) ∧
    ∀ (γ : ℝ) (N : ℕ) (hN : 1 ≤ N),
      (0 : ℂ) ∈ spectrum ℂ
        (bondProductParentHamiltonian (normalizedBondInterpolationVector D₀ D₁ γ) hN) ∧
      ∀ z ∈ spectrum ℂ
        (bondProductParentHamiltonian (normalizedBondInterpolationVector D₀ D₁ γ) hN),
        0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) :=
  ⟨(continuous_bondPenalty _).comp (continuous_normalizedBondInterpolationVector h₀ h₁),
    fun γ => ⟨bondPenalty_isStarProjection _ (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ),
      bondPenalty_norm_le_one _ (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)⟩,
    fun γ _ hN => bondProductParentHamiltonian_spectrum_gap_one _
      (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN⟩

end MPSTensor
