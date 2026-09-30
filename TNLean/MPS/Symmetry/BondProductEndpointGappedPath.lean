/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductEndpointPeriodicGroundSpace
import TNLean.MPS.Symmetry.FixedPointGappedPathWitness
import TNLean.MPS.Symmetry.InjectiveParentGappedPath
import TNLean.MPS.Symmetry.InteractionHamiltonianOrder
import TNLean.Algebra.CommonKernelSpectralGap

/-!
# Joining the bond-product and embedded parent interactions

At the first fixed-point endpoint, the bond-product interaction and the
canonical parent of the embedded matrix-unit summand act on the same physical
space. This file records their affine interpolation and the verified gap
inputs for the endpoint segment in Schuch--Pérez-García--Cirac,
arXiv:1010.3732, Section II.F.2. Establishing the full symmetric gapped
path additionally requires the local projection order and endpoint symmetry.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace MPSTensor

/-- The affine interaction joining the first bond-product endpoint to the
canonical parent of its embedded matrix-unit summand. Source:
arXiv:1010.3732, Section II.F.2. -/
noncomputable def firstEndpointInteraction (D₀ D₁ : ℕ) [NeZero D₀]
    (t : ℝ) : MPOTensor.ChainOperator ((D₀ + D₁) * (D₀ + D₁)) 2 :=
  normalizedBondInteraction D₀ D₁ 0 +
    t • (canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) -
      normalizedBondInteraction D₀ D₁ 0)

@[simp] theorem firstEndpointInteraction_zero (D₀ D₁ : ℕ) [NeZero D₀] :
    firstEndpointInteraction D₀ D₁ 0 = normalizedBondInteraction D₀ D₁ 0 := by
  simp [firstEndpointInteraction]

@[simp] theorem firstEndpointInteraction_one (D₀ D₁ : ℕ) [NeZero D₀] :
    firstEndpointInteraction D₀ D₁ 1 =
      canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) := by
  simp [firstEndpointInteraction]

private theorem firstEndpointInteraction_eq_convex (D₀ D₁ : ℕ)
    [NeZero D₀] (t : ℝ) :
    firstEndpointInteraction D₀ D₁ t =
      (1 - t) • normalizedBondInteraction D₀ D₁ 0 +
        t • canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) := by
  simp [firstEndpointInteraction, sub_smul, smul_sub]
  module

/-- The affine endpoint interaction is Hermitian at every parameter.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem firstEndpointInteraction_isHermitian
    (D₀ D₁ : ℕ) [NeZero D₀]
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (t : ℝ) :
    (firstEndpointInteraction D₀ D₁ t).IsHermitian := by
  have hA : (normalizedBondInteraction D₀ D₁ 0).IsHermitian := by
    have h := normalizedBondInteraction_isStarProjection h₀ h₁ (0 : ℝ)
    simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using
      h.isSelfAdjoint.star_eq
  have hB : (canonicalParentMatrix
      (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)).IsHermitian := by
    have h := parentInteraction_toMatrix'_isStarProjection
      (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2
    simpa only [canonicalParentMatrix, Matrix.IsHermitian,
      Matrix.star_eq_conjTranspose] using h.isSelfAdjoint.star_eq
  rw [firstEndpointInteraction_eq_convex]
  exact (hA.smul (by rfl : IsSelfAdjoint (1 - t))).add
    (hB.smul (by rfl : IsSelfAdjoint t))

/-- The local strength of the affine endpoint interaction is at most one.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem firstEndpointInteraction_norm_le_one
    (D₀ D₁ : ℕ) [NeZero D₀]
    (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖firstEndpointInteraction D₀ D₁ t‖ ≤ 1 := by
  have ht₀ : 0 ≤ t := ht.1
  have ht₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hA : ‖normalizedBondInteraction D₀ D₁ 0‖ ≤ 1 :=
    (normalizedBondInteraction_isStarProjection h₀ h₁ 0).norm_le _
  have hB : ‖canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)‖ ≤ 1 :=
    parentInteraction_toMatrix'_norm_le_one (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2
  rw [firstEndpointInteraction_eq_convex]
  calc
    ‖(1 - t) • normalizedBondInteraction D₀ D₁ 0 +
        t • canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)‖ ≤
        ‖(1 - t) • normalizedBondInteraction D₀ D₁ 0‖ +
          ‖t • canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)‖ :=
      norm_add_le _ _
    _ = (1 - t) * ‖normalizedBondInteraction D₀ D₁ 0‖ +
        t * ‖canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀, abs_of_nonneg ht₁]
    _ ≤ (1 - t) * 1 + t * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hA ht₁)
        (mul_le_mul_of_nonneg_left hB ht₀)
    _ = 1 := by ring

/-- The affine endpoint interaction depends continuously on its parameter.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem continuous_firstEndpointInteraction (D₀ D₁ : ℕ) [NeZero D₀] :
    Continuous (firstEndpointInteraction D₀ D₁) := by
  unfold firstEndpointInteraction
  fun_prop

private theorem firstEndpointBond_hamiltonian_eq_physical
    {D₀ D₁ N : ℕ} (hN : 2 ≤ N) :
    interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN =
      physicalBondProductParentHamiltonian
        (normalizedBondInterpolationVector D₀ D₁ 0) (by omega : 1 ≤ N) := by
  have hNZ : NeZero N := ⟨by omega⟩
  exact @interactionHamiltonian_twoSiteBondPenalty (D₀ + D₁) N hNZ hN _

private theorem firstEndpointBond_hamiltonian_posSemidef
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (hN : 2 ≤ N) :
    (interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN).PosSemidef := by
  apply interactionHamiltonian_posSemidef _ hN
  exact Matrix.nonneg_iff_posSemidef.mp
    (normalizedBondInteraction_isStarProjection h₀ h₁ 0).nonneg

private theorem firstEndpointBond_hamiltonian_quadratic_gap
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (hN : 2 ≤ N) :
    ∀ x : EuclideanSpace ℂ
      (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁))),
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN)))ᗮ →
      (1 : ℝ) * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ
          (interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN *ᵥ
            x.ofLp)).re := by
  rw [firstEndpointBond_hamiltonian_eq_physical hN]
  have hSpec := (normalizedPhysicalBondInterpolation_parent_spectrum_gap_one
    h₀ h₁ 0 (by omega : 1 ≤ N)).2
  exact Matrix.orthogonal_quadratic_gap_of_spectrum_separated _
    (physicalBondProductParentHamiltonian_posSemidef _
      (normalizedBondInterpolationVector_sum_normSq h₀ h₁ 0) (by omega)).isHermitian
    (fun z hz => (hSpec z hz).2)

private theorem firstEndpointBond_hamiltonian_nonzero_kernel
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (hN : 2 ≤ N) :
    ∃ x : EuclideanSpace ℂ
      (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁))),
      x ≠ 0 ∧
        Matrix.toEuclideanLin
          (interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN) x = 0 := by
  let η := normalizedBondInterpolationVector D₀ D₁ 0
  let U := incomingBondUnitaryLin (D₀ + D₁) N
  let ψ := bondProductState η N
  have hη : ∑ p, Complex.normSq (η p) = 1 :=
    normalizedBondInterpolationVector_sum_normSq h₀ h₁ 0
  have hψ : ψ ≠ 0 := bondProductState_ne_zero η hη N
  have hUψ : U ψ ≠ 0 := by
    intro hzero
    have h := congrArg (fun v => star U v) hzero
    apply hψ
    rw [← Module.End.mul_apply, incomingBondUnitaryLin_star_mul_self] at h
    simpa using h
  refine ⟨U ψ, hUψ, ?_⟩
  rw [firstEndpointBond_hamiltonian_eq_physical hN]
  have hmem : U ψ ∈ LinearMap.ker
      (physicalBondProductParentHamiltonianLin η (by omega : 1 ≤ N)) := by
    rw [physicalBondProductParentHamiltonian_groundSpace η hη (by omega)]
    exact Submodule.subset_span (Set.mem_singleton _)
  simpa only [physicalBondProductParentHamiltonianLin_eq_matrix,
    bondMatrixEquiv_symm_eq_toEuclideanLin] using
    (LinearMap.mem_ker.mp hmem)

private theorem firstEndpointBond_ker_le_parent
    {D₀ D₁ N : ℕ} [NeZero D₀] (h₁ : 0 < D₁) (hN : 2 ≤ N)
    (x : (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁))) → ℂ)
    (hx : interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN *ᵥ x = 0) :
    interactionHamiltonian
      (canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)) hN *ᵥ x = 0 := by
  obtain ⟨L, rfl⟩ : ∃ L, N = L + 2 := ⟨N - 2, by omega⟩
  have hxES : Matrix.toEuclideanLin
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ 0) hN)
      (WithLp.toLp 2 x) = 0 := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hx
  have hbond : (WithLp.toLp 2 x) ∈ LinearMap.ker
      (physicalBondProductParentHamiltonianLin
        (normalizedBondInterpolationVector D₀ D₁ 0) (by omega : 1 ≤ L + 2)) := by
    rw [LinearMap.mem_ker, physicalBondProductParentHamiltonianLin_eq_matrix,
      bondMatrixEquiv_symm_eq_toEuclideanLin]
    simpa only [firstEndpointBond_hamiltonian_eq_physical hN] using hxES
  have hparent : parentHamiltonianES (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)
      2 (L + 2) (WithLp.toLp 2 x) = 0 := by
    have hmem := (normalizedPhysicalBondInterpolation_zero_ker_le_leftEmbedded_parent_ker
      D₀ D₁ L h₁) hbond
    simpa only [LinearMap.mem_ker] using hmem
  have hxB : Matrix.toEuclideanLin
      (interactionHamiltonian
        (canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)) hN)
      (WithLp.toLp 2 x) = 0 := by
    rw [canonicalParentMatrix_hamiltonian_toEuclideanLin]
    exact hparent
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hxB

end MPSTensor
