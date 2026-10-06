/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductPhysicalParentHamiltonian
import TNLean.Algebra.CommonKernelSpectralGap
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order

/-!
# Spectral form of the independent-bond gap

The quadratic-form inequality for the commuting parent Hamiltonian implies
that its nonzero spectral values are at least one. This gives the spectral
form of the uniform gap used in the gapped-path definition of
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2.
-/

open scoped Matrix MatrixOrder InnerProductSpace ComplexOrder

namespace MPSTensor

/-- A positive Hermitian matrix satisfying the quadratic gap `A² ≥ A`
has spectrum in `{0} ∪ [1,∞)`. Source: arXiv:1010.3732,
Section II.F.2, applied to the commuting bond parent Hamiltonian. -/
theorem spectrum_separated_of_quadratic_gap {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (hPos : A.PosSemidef)
    (hGap : ∀ v : EuclideanSpace ℂ n,
      (⟪Matrix.toEuclideanLin A v, v⟫_ℂ).re ≤
        (⟪Matrix.toEuclideanLin A v,
          Matrix.toEuclideanLin A v⟫_ℂ).re) :
    ∀ z ∈ spectrum ℂ A, 0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  classical
  let hA := hPos.isHermitian
  intro z hz
  rw [hA.spectrum_eq_image_range] at hz
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hz
  have hnonneg : 0 ≤ hA.eigenvalues i := hPos.eigenvalues_nonneg i
  let v := hA.eigenvectorBasis i
  have hnorm : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.norm_eq_one i
  have hlin : Matrix.toEuclideanLin A v = (hA.eigenvalues i : ℂ) • v :=
    hA.toEuclideanLin_eigenvectorBasis i
  have hg := hGap v
  rw [hlin] at hg
  have hinner : ⟪v, v⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hineq : hA.eigenvalues i ≤ (hA.eigenvalues i) ^ 2 := by
    rw [inner_smul_left, inner_smul_right, inner_smul_left, hinner] at hg
    simpa [Complex.star_def, pow_two] using hg
  constructor
  · simp [hnonneg]
  · by_cases hzero : hA.eigenvalues i = 0
    · left; simp [hzero]
    · right
      have hpos : 0 < hA.eigenvalues i := lt_of_le_of_ne hnonneg (Ne.symm hzero)
      change 1 ≤ hA.eigenvalues i
      nlinarith

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

/-- The unique ground line gives the zero spectral value of the physical
parent Hamiltonian. Source: arXiv:1010.3732, Section II.F.2. -/
theorem physicalBondProductParentHamiltonian_zero_mem_spectrum
    {D N : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ (physicalBondProductParentHamiltonian η hN) := by
  let U := incomingBondUnitaryLin D N
  let ψ := bondProductState η N
  have hψ : ψ ≠ 0 := bondProductState_ne_zero η hη N
  have hUψ : U ψ ≠ 0 := by
    intro hzero
    have h := congrArg (fun v => star U v) hzero
    apply hψ
    rw [← Module.End.mul_apply, incomingBondUnitaryLin_star_mul_self D N] at h
    simpa using h
  have hker : LinearMap.ker (physicalBondProductParentHamiltonianLin η hN) ≠ ⊥ := by
    intro hbot
    have hmem : U ψ ∈ LinearMap.ker (physicalBondProductParentHamiltonianLin η hN) := by
      rw [physicalBondProductParentHamiltonian_groundSpace η hη hN]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hz : U ψ = 0 := by
      rw [hbot] at hmem
      simpa using hmem
    exact hUψ hz
  rw [← Matrix.spectrum_toLpLin (p := 2)]
  apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
  simpa [physicalBondProductParentHamiltonianLin_eq_matrix,
    bondMatrixEquiv_symm_eq_toEuclideanLin] using hker

/-- The physical parent spectrum consists of its zero ground value and
values at least one, with a bound uniform in the chain length and bond
vector. Source: arXiv:1010.3732, Section II.F.2. -/
theorem physicalBondProductParentHamiltonian_spectrum_gap_one
    {D N : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ (physicalBondProductParentHamiltonian η hN) ∧
      ∀ z ∈ spectrum ℂ (physicalBondProductParentHamiltonian η hN),
        0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  constructor
  · exact physicalBondProductParentHamiltonian_zero_mem_spectrum η hη hN
  · apply spectrum_separated_of_quadratic_gap _
      (physicalBondProductParentHamiltonian_posSemidef η hη hN)
    intro v
    simpa [physicalBondProductParentHamiltonianLin_eq_matrix,
      bondMatrixEquiv_symm_eq_toEuclideanLin] using
      physicalBondProductParentHamiltonian_gap_one η hη hN v

/-- Uniform spectral gap along the normalized interpolation, including
the zero ground value. Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (γ : ℝ) (hN : 1 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ
      (physicalBondProductParentHamiltonian
        (normalizedBondInterpolationVector D₀ D₁ γ) hN) ∧
      ∀ z ∈ spectrum ℂ
        (physicalBondProductParentHamiltonian
          (normalizedBondInterpolationVector D₀ D₁ γ) hN),
        0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) :=
  physicalBondProductParentHamiltonian_spectrum_gap_one _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN

end MPSTensor
