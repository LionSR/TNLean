/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommonKernelSpectralGap
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry
import TNLean.MPS.ParentHamiltonian.CompactParentGap

/-!
# Canonical parent interactions along an injective path

A continuous path of one-site injective tensors with a fixed on-site
unitary symmetry gives a symmetric gapped interaction path between its
canonical two-site parent interactions. The gap follows from compactness;
no finite-window bound is assumed.

**Scope restriction (one-site injective tensors):** this is the single-block,
one-site injective case of arXiv:1010.3732, Section II.C and Appendix A.
The source also treats several-block normal forms. Documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- A norm gap for a positive matrix bounds its nonzero spectral values. -/
private theorem spectrum_separated_of_orthogonal_norm_gap
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.PosSemidef) {δ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin M v‖) :
    ∀ z ∈ spectrum ℂ M, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  intro z hz
  rw [hM.isHermitian.spectrum_eq_image_range] at hz
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hz
  have hNonneg := hM.eigenvalues_nonneg i
  refine ⟨by simpa using hNonneg, ?_⟩
  by_cases hzero : hM.isHermitian.eigenvalues i = 0
  · left
    simpa using hzero
  · right
    let v := hM.isHermitian.eigenvectorBasis i
    have hNorm : ‖v‖ = 1 := hM.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
    have hEigen : Matrix.toEuclideanLin M v = (hM.isHermitian.eigenvalues i : ℂ) • v :=
      hM.isHermitian.toEuclideanLin_eigenvectorBasis i
    have hSym : (Matrix.toEuclideanLin M).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.isHermitian
    have hOrth : v ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
      rw [LinearMap.orthogonal_ker, hSym.adjoint_eq]
      refine ⟨(hM.isHermitian.eigenvalues i : ℂ)⁻¹ • v, ?_⟩
      rw [map_smul, hEigen, smul_smul, inv_mul_cancel₀, one_smul]
      exact_mod_cast hzero
    have h := hGap v hOrth
    simpa [hNorm, hEigen, norm_smul, Complex.norm_real, abs_of_nonneg hNonneg] using h

/-- Canonical parent matrices vary continuously along an injective family.
Source: arXiv:1010.3732, Section II.C and Appendix A, continuity of local
parent interactions. -/
theorem continuous_parentInteraction_matrix_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (L : ℕ)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => LinearMap.toMatrix' (parentInteraction (A x) L) := by
  let b := (EuclideanSpace.basisFun (Cfg d L) ℂ).toBasis
  have hT := continuous_parentInteractionES_family A hA L hInj
  have hMat : Continuous fun T :
      EuclideanSpace ℂ (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d L) =>
      LinearMap.toMatrix b b T.toLinearMap :=
    ((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℂ)).continuous_of_finiteDimensional
  simpa only [parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix,
    Function.comp_def, b, LinearMap.coe_toContinuousLinearMap] using hMat.comp hT

/-- For an injective tensor, a canonical parent norm gap is a spectral gap
above the zero ground energy. Source: arXiv:1010.3732, Section II.C and
Appendix A, spectral interpretation of the parent gap. -/
theorem interactionHamiltonian_parent_spectrum_gap
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D) (hInj : Kraus.IsInjective A)
    (hN : 2 ≤ N) {δ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (parentHamiltonianES A 2 N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A 2 N v‖) :
    let H := interactionHamiltonian (LinearMap.toMatrix' (parentInteraction A 2)) hN
    (0 : ℂ) ∈ spectrum ℂ H ∧
      ∀ z ∈ spectrum ℂ H, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  let H := interactionHamiltonian (LinearMap.toMatrix' (parentInteraction A 2)) hN
  have hH : parentHamiltonianES A 2 N = Matrix.toEuclideanLin H :=
    parentHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator A hN
  constructor
  · change (0 : ℂ) ∈ spectrum ℂ H
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
    change LinearMap.ker (Matrix.toEuclideanLin H) ≠ ⊥
    rw [← hH, ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap
      A hInj hN]
    intro hbot
    have hv : periodicMpvLineMap A N 1 ∈ (periodicMpvLineMap A N).range :=
      ⟨1, rfl⟩
    rw [hbot] at hv
    have heq : periodicMpvLineMap A N 1 = periodicMpvLineMap A N 0 := by
      simpa using hv
    exact one_ne_zero (periodicMpvLineMap_injective_of_isInjective A
      hInj hN heq)
  · have hPos : H.PosSemidef := Matrix.isPositive_toEuclideanLin_iff.mp
      (hH ▸ parentHamiltonianES_isPositive A 2 N)
    have hNormGap : ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin H))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v‖ := by
      rw [← hH]
      exact hGap
    simpa only [zero_add] using spectrum_separated_of_orthogonal_norm_gap H hPos hNormGap

set_option maxHeartbeats 400000 in
-- The compactness argument and dependent path conditions together exceed the default limit.
/-- A continuous one-site injective tensor path with fixed unitary on-site
symmetry determines a symmetric uniformly gapped path of its canonical
nearest-neighbor parent interactions. Source: arXiv:1010.3732, Section II.C
and Appendix A, single-block injective case. -/
noncomputable def canonicalInjectiveGappedPath
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A : ℝ → MPSTensor d D) (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hInj : ∀ γ ∈ Set.Icc (0 : ℝ) 1, Kraus.IsInjective (A γ))
    (hCov : ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ g : G,
      GaugeEquiv (A γ) (rotatePhysical (U g) (A γ))) :
    SymmetricGappedInteractionPath U
      (LinearMap.toMatrix' (parentInteraction (A 0) 2))
      (LinearMap.toMatrix' (parentInteraction (A 1) 2)) where
  interaction γ := LinearMap.toMatrix' (parentInteraction (A γ) 2)
  interaction_zero := rfl
  interaction_one := rfl
  hermitian γ _ := (parentInteraction_toMatrix'_isStarProjection (A γ) 2).isSelfAdjoint
  norm_le_one γ _ := parentInteraction_toMatrix'_norm_le_one (A γ) 2
  continuous := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_parentInteraction_matrix_family
      (fun γ : Set.Icc (0 : ℝ) 1 => A γ)
      (continuousOn_iff_continuous_domRestrict.mp hA) 2
    intro γ
    exact isNBlkInjective_of_le zero_lt_one
      (Kraus.isNBlkInjective_one_of_isInjective (hInj γ γ.property)) one_le_two
  gap := by
    let B : Set.Icc (0 : ℝ) 1 → MPSTensor d D := fun γ => A γ
    obtain ⟨δ, hδ, hGap⟩ :=
      exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths B
        (continuousOn_iff_continuous_domRestrict.mp hA)
        (fun γ => hInj γ γ.property) isCompact_univ
    refine ⟨δ, hδ, fun γ hγ N hN => ⟨0, ?_⟩⟩
    simpa only [Complex.ofReal_zero, zero_add] using
      interactionHamiltonian_parent_spectrum_gap (A γ) (hInj γ hγ) hN
        (hGap ⟨γ, hγ⟩ (Set.mem_univ _) N hN)
  symmetric γ hγ g N hN := by
    rw [interactionHamiltonian, ← onSiteTensorPow_eq_finKronecker]
    apply Commute.sum_left
    intro i _
    exact embedLocalOperator_commute_onSiteTensorPow (U g) 2 hN i
      (LinearMap.toMatrix' (parentInteraction (A γ) 2))
      (parentInteraction_matrix_commute_onSiteTensorPow (A γ) (U g)
        (SetLike.coe_mem _) (hCov γ hγ g) 2)

end MPSTensor
