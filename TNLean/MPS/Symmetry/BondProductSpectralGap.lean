/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductPhysicalParentHamiltonian
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.Martingale.AbstractCriterion
import Mathlib.Analysis.Matrix.Order

/-!
# Spectral form of the independent-bond gap

The quadratic-form inequality for the commuting parent Hamiltonian implies
that its nonzero eigenvalues are at least one. With its ground line this is
the uniform gap above zero used in the gapped-path definition of
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2.
-/

open scoped Matrix MatrixOrder InnerProductSpace ComplexOrder

namespace MPSTensor

/-- A positive semidefinite matrix satisfying the quadratic gap `A² ≥ A` has every
eigenvalue equal to `0` or at least `1`. Source: arXiv:1010.3732, Section II.F.2, applied to
the commuting bond parent Hamiltonian. -/
theorem forall_hasEigenvalue_of_quadratic_gap {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (hPos : A.PosSemidef)
    (hGap : ∀ v : EuclideanSpace ℂ n,
      (⟪Matrix.toEuclideanLin A v, v⟫_ℂ).re ≤
        (⟪Matrix.toEuclideanLin A v,
          Matrix.toEuclideanLin A v⟫_ℂ).re) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ := by
  simpa only [Complex.ofReal_one] using (ManyBody.forall_hasEigenvalue_iff_norm hPos).mpr
    (FrustrationFree.spectralGap_of_martingale_of_finiteDimensional one_pos
      (Matrix.isPositive_toEuclideanLin_iff.mpr hPos) (by simpa only [one_mul] using hGap))

/-- The physical parent Hamiltonian of unit bonds is positive
semidefinite. Source: arXiv:1010.3732, Section II.F.2. -/
theorem physicalBondProductParentHamiltonian_posSemidef
    {D N : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    (physicalBondProductParentHamiltonian η hN).PosSemidef := by
  have hbond : (bondProductParentHamiltonian η hN).PosSemidef := by
    unfold bondProductParentHamiltonian
    apply Matrix.posSemidef_sum Finset.univ
    intro i hi
    exact Matrix.nonneg_iff_posSemidef.mp
      (bondPenaltyAt_isStarProjection η hη hN i).nonneg
  unfold physicalBondProductParentHamiltonian
  exact hbond.mul_mul_conjTranspose_same
    ((incomingBondPerm D N).permMatrix ℂ)

/-- The physical parent Hamiltonian is gapped above its zero ground energy with gap one,
uniformly in the chain length and bond vector; its ground space is the line of the physically
reordered bond-product state. Source: arXiv:1010.3732, Section II.F.2. -/
theorem isGapped_physicalBondProductParentHamiltonian
    {D N : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    ManyBody.IsGapped (physicalBondProductParentHamiltonian η hN) 0 1 := by
  have hpos := physicalBondProductParentHamiltonian_posSemidef η hη hN
  have hlin : physicalBondProductParentHamiltonianLin η hN =
      Matrix.toEuclideanLin (physicalBondProductParentHamiltonian η hN) := by
    simpa [bondMatrixEquiv_symm_eq_toEuclideanLin] using
      physicalBondProductParentHamiltonianLin_eq_matrix η hN
  have hUψ : incomingBondUnitaryLin D N (bondProductState η N) ≠ 0 := by
    intro hzero
    have h := congrArg (fun v => star (incomingBondUnitaryLin D N) v) hzero
    apply bondProductState_ne_zero η hη N
    rw [← Module.End.mul_apply, incomingBondUnitaryLin_star_mul_self D N] at h
    simpa using h
  refine (ManyBody.isGapped_zero_iff_norm hpos).mpr ⟨?_, ?_⟩
  · rw [ManyBody.groundSpace_zero, ← hlin, physicalBondProductParentHamiltonian_groundSpace η hη hN,
      Ne, Submodule.span_singleton_eq_bot]
    exact hUψ
  · rw [← ManyBody.forall_hasEigenvalue_iff_norm hpos, Complex.ofReal_one]
    refine forall_hasEigenvalue_of_quadratic_gap _ hpos fun v ↦ ?_
    rw [← hlin]
    exact physicalBondProductParentHamiltonian_gap_one η hη hN v

/-- Uniform gap along the normalized interpolation, above the zero ground energy.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem isGapped_normalizedPhysicalBondInterpolation_parent
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (γ : ℝ) (hN : 1 ≤ N) :
    ManyBody.IsGapped (physicalBondProductParentHamiltonian
      (normalizedBondInterpolationVector D₀ D₁ γ) hN) 0 1 :=
  isGapped_physicalBondProductParentHamiltonian _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN

end MPSTensor
