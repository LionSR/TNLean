/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry
import TNLean.MPS.ParentHamiltonian.CompactParentGap
import TNLean.MPS.Symmetry.BondProductSpectralGap
import TNLean.Algebra.CommonKernelSpectralGap
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Order.ProjIcc

/-!
# Gapped canonical parents along injective tensor paths

For a continuous one-site injective covariant tensor family, the canonical
nearest-neighbor parent projections form a continuous, uniformly bounded,
symmetric path. The finite-volume gap is uniform over the parameter and all
periodic lengths at least two. This is the injective-path ingredient of
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Appendix A and Section II.F.2.

The construction presupposes a continuous covariant injective tensor path on
one fixed physical space. It does not construct such a path between arbitrary
endpoints or identify the virtual cohomology classes.
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace MPSTensor

/-- The canonical nearest-neighbor interaction of a one-site tensor, in
matrix coordinates. Source: arXiv:1010.3732, Section II.D. -/
noncomputable def canonicalParentMatrix {d D : ℕ} (A : MPSTensor d D) :
    MPOTensor.ChainOperator d 2 :=
  LinearMap.toMatrix' (parentInteraction A 2)

/-- The canonical local parent matrix varies continuously along a continuous
one-site injective tensor family. Source: arXiv:1010.3732, Appendix A. -/
theorem continuous_canonicalParentMatrix_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) :
    Continuous fun x => canonicalParentMatrix (A x) := by
  have hBlock (x : X) : Kraus.IsNBlkInjective (A x) 2 :=
    isNBlkInjective_of_le (by norm_num : 0 < 1)
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x))
      (by norm_num : 1 ≤ 2)
  have hP := continuous_parentInteractionES_family A hA 2 hBlock
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hEval : Continuous fun T : EuclideanSpace ℂ (Cfg d 2) →L[ℂ]
      EuclideanSpace ℂ (Cfg d 2) => T (EuclideanSpace.single j 1) i := by
    fun_prop
  convert hEval.comp hP using 1
  ext x
  change (LinearMap.toMatrix' (parentInteraction (A x) 2)) i j = _
  rw [parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_apply]

/-- The periodic matrix Hamiltonian coincides with the Euclidean parent
Hamiltonian. Source: arXiv:1010.3732, Section II.C.1. -/
theorem canonicalParentMatrix_hamiltonian_toEuclideanLin
    {d D N : ℕ} (A : MPSTensor d D) (hN : 2 ≤ N) :
    Matrix.toEuclideanLin (interactionHamiltonian (canonicalParentMatrix A) hN) =
      parentHamiltonianES A 2 N := by
  unfold interactionHamiltonian canonicalParentMatrix
  exact (parentHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator A hN).symm

/-- The canonical periodic parent Hamiltonian is positive. Source:
arXiv:1010.3732, Section II.D. -/
theorem parentHamiltonianES_two_isPositive {d D N : ℕ}
    (A : MPSTensor d D) : (parentHamiltonianES A 2 N).IsPositive := by
  rw [← periodicInteractionHamiltonianES_parentInteractionES A (by norm_num : 0 < 2) N]
  exact periodicInteractionHamiltonianES_isPositive
    (parentInteractionES_isPositive A 2) N

/-- The canonical periodic parent matrix is positive semidefinite. Source:
arXiv:1010.3732, Section II.D. -/
theorem canonicalParentMatrix_hamiltonian_posSemidef
    {d D N : ℕ} (A : MPSTensor d D) (hN : 2 ≤ N) :
    (interactionHamiltonian (canonicalParentMatrix A) hN).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  rw [canonicalParentMatrix_hamiltonian_toEuclideanLin A hN]
  exact parentHamiltonianES_two_isPositive A

/-- A positive finite-dimensional Hamiltonian with a zero vector and a
norm gap above its kernel has the corresponding spectral gap. -/
theorem spectrum_gap_of_positive_norm_gap {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) (hPos : M.PosSemidef)
    {δ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin M v‖) :
    ∀ z ∈ spectrum ℂ M, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  classical
  have hSym : M.IsHermitian := hPos.isHermitian
  have hLinSym : (Matrix.toEuclideanLin M).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hSym
  intro z hz
  rw [hSym.spectrum_eq_image_range] at hz
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hz
  let v := hSym.eigenvectorBasis i
  have hnorm : ‖v‖ = 1 := hSym.eigenvectorBasis.orthonormal.norm_eq_one i
  have hlin : Matrix.toEuclideanLin M v = (hSym.eigenvalues i : ℂ) • v :=
    Matrix.IsHermitian.toEuclideanLin_eigenvectorBasis hSym i
  have hnonneg : 0 ≤ hSym.eigenvalues i := hPos.eigenvalues_nonneg i
  constructor
  · simp [hnonneg]
  · by_cases hzero : hSym.eigenvalues i = 0
    · left; simp [hzero]
    · right
      have hmem : v ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        rw [LinearMap.orthogonal_ker, hLinSym.adjoint_eq]
        refine ⟨(hSym.eigenvalues i : ℂ)⁻¹ • v, ?_⟩
        rw [map_smul, hlin]
        have hzeroC : (hSym.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hzero
        change ((hSym.eigenvalues i : ℂ)⁻¹ •
          ((hSym.eigenvalues i : ℂ) • v)) = v
        rw [smul_smul, inv_mul_cancel₀ hzeroC, one_smul]
      have hg := hGap v hmem
      rw [hlin, norm_smul, hnorm] at hg
      have hpos : 0 < hSym.eigenvalues i := lt_of_le_of_ne hnonneg (Ne.symm hzero)
      simpa [Complex.norm_real, abs_of_nonneg hnonneg] using hg

/-- The nonzero periodic MPS state supplies the zero eigenvalue of its
canonical parent Hamiltonian. Source: arXiv:1010.3732, Section II.D. -/
theorem canonicalParentMatrix_zero_mem_spectrum {d D N : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hN : 2 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ
      (interactionHamiltonian (canonicalParentMatrix A) hN) := by
  let M := interactionHamiltonian (canonicalParentMatrix A) hN
  let ψ := periodicMpvLineMap A N 1
  have hψ : ψ ≠ 0 := by
    intro hz
    have hi := periodicMpvLineMap_injective_of_isInjective A hA hN
    have hzero : periodicMpvLineMap A N 0 = 0 := map_zero _
    have : (1 : ℂ) = 0 := hi (by simpa [ψ, hzero] using hz)
    exact one_ne_zero this
  have hker : ψ ∈ LinearMap.ker (parentHamiltonianES A 2 N) := by
    rw [ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap A hA hN]
    exact ⟨1, rfl⟩
  have hkerM : Matrix.toEuclideanLin M ψ = 0 := by
    rw [canonicalParentMatrix_hamiltonian_toEuclideanLin A hN]
    exact hker
  rw [← Matrix.spectrum_toLpLin (p := 2)]
  apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
  intro hbot
  have hmem : ψ ∈ LinearMap.ker (Matrix.toEuclideanLin M) := by
    simpa only [LinearMap.mem_ker] using hkerM
  rw [hbot] at hmem
  exact hψ (by simpa using hmem)

/-- The uniform norm gap for a nearest-neighbor parent Hamiltonian gives
the spectral gap, with zero as ground energy. Source: arXiv:1010.3732,
Appendix A. -/
theorem canonicalParentMatrix_spectrum_gap {d D N : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hN : 2 ≤ N)
    {δ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (parentHamiltonianES A 2 N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A 2 N v‖) :
    (0 : ℂ) ∈ spectrum ℂ
      (interactionHamiltonian (canonicalParentMatrix A) hN) ∧
      ∀ z ∈ spectrum ℂ (interactionHamiltonian (canonicalParentMatrix A) hN),
        0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  constructor
  · exact canonicalParentMatrix_zero_mem_spectrum A hA hN
  · apply spectrum_gap_of_positive_norm_gap _
      (canonicalParentMatrix_hamiltonian_posSemidef A hN)
    simpa only [canonicalParentMatrix_hamiltonian_toEuclideanLin A hN] using hGap

/-- The canonical parents of a continuous covariant one-site injective MPS
path form a symmetric gapped path on their common physical space. The
covariance is exact up to a virtual gauge at each parameter; no uniform gap
is assumed. Source: arXiv:1010.3732, Section II.F.2 and Appendix A. -/
noncomputable def injectiveParentGappedPath
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A : Set.Icc (0 : ℝ) 1 → MPSTensor d D)
    (hA : Continuous A)
    (hInj : ∀ γ, Kraus.IsInjective (A γ))
    (hCov : ∀ γ g, GaugeEquiv (A γ) (rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) (A γ))) :
    SymmetricGappedInteractionPath U
      (canonicalParentMatrix (A ⟨0, by norm_num⟩))
      (canonicalParentMatrix (A ⟨1, by norm_num⟩)) := by
  let B : ℝ → MPSTensor d D := fun γ => A (Set.projIcc 0 1 zero_le_one γ)
  have hB : Continuous B := hA.comp continuous_projIcc
  have hBInj (γ : ℝ) : Kraus.IsInjective (B γ) :=
    hInj (Set.projIcc 0 1 zero_le_one γ)
  have hBCov (γ : ℝ) (g : G) :
      GaugeEquiv (B γ) (rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) (B γ)) :=
    hCov (Set.projIcc 0 1 zero_le_one γ) g
  have hGap := exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths
    B hB hBInj (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  refine {
    interaction := fun γ => canonicalParentMatrix (B γ)
    interaction_zero := ?_
    interaction_one := ?_
    hermitian := ?_
    norm_le_one := ?_
    continuous := ?_
    gap := ?_
    symmetric := ?_ }
  · change canonicalParentMatrix (A (Set.projIcc 0 1 zero_le_one 0)) = _
    rw [Set.projIcc_of_mem (h := zero_le_one) (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
  · change canonicalParentMatrix (A (Set.projIcc 0 1 zero_le_one 1)) = _
    rw [Set.projIcc_of_mem (h := zero_le_one) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
  · intro γ hγ
    have h := parentInteraction_toMatrix'_isStarProjection (B γ) 2
    simpa only [canonicalParentMatrix, Matrix.IsHermitian,
      Matrix.star_eq_conjTranspose] using h.isSelfAdjoint.star_eq
  · intro γ hγ
    exact parentInteraction_toMatrix'_norm_le_one (B γ) 2
  · exact (continuous_canonicalParentMatrix_family B hB hBInj).continuousOn
  · obtain ⟨δ, hδ, hGap⟩ := hGap
    refine ⟨δ, hδ, ?_⟩
    intro γ hγ N hN
    refine ⟨0, ?_, ?_⟩
    · exact (canonicalParentMatrix_spectrum_gap (B γ) (hBInj γ) hN
        (hGap γ hγ N hN)).1
    · intro z hz
      have hspec := (canonicalParentMatrix_spectrum_gap (B γ) (hBInj γ) hN
        (hGap γ hγ N hN)).2 z hz
      simpa using hspec
  · intro γ hγ g N hN
    change Commute (interactionHamiltonian (canonicalParentMatrix (B γ)) hN)
      (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))
    rw [← onSiteTensorPow_eq_finKronecker]
    unfold interactionHamiltonian
    apply (commute_iff_eq _ _).2
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (embedLocalOperator_commute_onSiteTensorPow
      (U g : Matrix (Fin d) (Fin d) ℂ) 2 hN i
      (canonicalParentMatrix (B γ))
      (parentInteraction_matrix_commute_onSiteTensorPow (B γ)
        (U g : Matrix (Fin d) (Fin d) ℂ) (U g).property (hBCov γ g) 2)).eq

end MPSTensor
