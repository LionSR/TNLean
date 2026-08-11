/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.RFP.AppendixBTwoSiteBasicSupport
import TNLean.MPS.RFP.PairLiftCoordinates

/-!
# Appendix B virtual-pair commutation

This file expresses the virtual bond projector and its physical transport in
pair-matrix coordinates and proves commutation of the two virtual placements.
-/

open scoped Matrix BigOperators InnerProductSpace Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-! ### Virtual replacement slices -/

/-- The first two coordinates of a three-coordinate function, without a
restriction on the coordinate type. -/
private def appendixBFirstPairCfg {alpha : Type*} (p : Fin 3 → alpha) : Fin 2 → alpha :=
  ![p 0, p 1]

/-- The final two coordinates of a three-coordinate function, without a
restriction on the coordinate type. -/
private def appendixBLastPairCfg {alpha : Type*} (p : Fin 3 → alpha) : Fin 2 → alpha :=
  ![p 1, p 2]

/-- Restricting a replacement on the first virtual bond to the first two sites
is the corresponding two-site replacement. -/
private theorem AppendixBStructuralData.axPairCfg_replaceVirtualBond01
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    appendixBFirstPairCfg (hStruct.replaceVirtualBond01 p k) =
      hStruct.replaceTwoSiteVirtualBond (appendixBFirstPairCfg p) k := by
  funext t
  fin_cases t <;> simp [appendixBFirstPairCfg]

/-- Restricting a replacement on the second virtual bond to the final two
sites is the corresponding two-site replacement. -/
private theorem AppendixBStructuralData.xbPairCfg_replaceVirtualBond12
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    appendixBLastPairCfg (hStruct.replaceVirtualBond12 p k) =
      hStruct.replaceTwoSiteVirtualBond (appendixBLastPairCfg p) k := by
  funext t
  fin_cases t <;> simp [appendixBLastPairCfg]

/-- A first-bond replacement gives a prescribed virtual triple precisely when
its first face and untouched final pair agree. -/
private theorem AppendixBStructuralData.replaceVirtualBond01_eq_iff
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p q : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond01 p k = q ↔
      hStruct.replaceTwoSiteVirtualBond (appendixBFirstPairCfg p) k =
          appendixBFirstPairCfg q ∧ p 2 = q 2 := by
  constructor
  · intro h
    exact ⟨by
      rw [← hStruct.axPairCfg_replaceVirtualBond01]
      exact congrArg appendixBFirstPairCfg h,
      congrFun h 2⟩
  · rintro ⟨hface, hs⟩
    funext t
    fin_cases t
    · simpa [appendixBFirstPairCfg] using congrFun hface 0
    · simpa [appendixBFirstPairCfg] using congrFun hface 1
    · simpa using hs

/-- A second-bond replacement gives a prescribed virtual triple precisely when
its final face and untouched initial pair agree. -/
private theorem AppendixBStructuralData.replaceVirtualBond12_eq_iff
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p q : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond12 p k = q ↔
      hStruct.replaceTwoSiteVirtualBond (appendixBLastPairCfg p) k =
          appendixBLastPairCfg q ∧ p 0 = q 0 := by
  constructor
  · intro h
    exact ⟨by
      rw [← hStruct.xbPairCfg_replaceVirtualBond12]
      exact congrArg appendixBLastPairCfg h,
      congrFun h 0⟩
  · rintro ⟨hface, hs⟩
    funext t
    fin_cases t
    · simpa using hs
    · simpa [appendixBLastPairCfg] using congrFun hface 0
    · simpa [appendixBLastPairCfg] using congrFun hface 1

/-! ### Matrices of the physical and virtual two-site transports -/

/-- The one-site physical isometry in the pair-index basis.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
noncomputable def AppendixBStructuralData.physicalIsometryMatrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix (Fin d) (Fin D × Fin D) ℂ :=
  fun i p ↦ hStruct.U i p.1 p.2

/-- The reindexed two-site tensor-power matrix is the Kronecker square of the
one-site physical isometry.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
theorem AppendixBStructuralData.physicalIsometryTensorPower_two_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin D × Fin D))
        (LinearMap.toMatrix' (hStruct.physicalIsometryTensorPower 2)) =
      hStruct.physicalIsometryMatrix ⊗ₖ hStruct.physicalIsometryMatrix := by
  classical
  ext σ p
  simp [Matrix.reindex_apply, LinearMap.toMatrix'_apply,
    AppendixBStructuralData.physicalIsometryTensorPower,
    AppendixBStructuralData.physicalIsometryMatrix, finTwoArrowEquiv,
    Pi.single_apply, Fin.prod_univ_two]

/-- The reindexed two-site coefficient-adjoint matrix is the Kronecker square
of the conjugate transpose of the one-site physical isometry.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
theorem AppendixBStructuralData.physicalIsometryTensorPowerLeftInverse_two_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' (hStruct.physicalIsometryTensorPowerLeftInverse 2)) =
      hStruct.physicalIsometryMatrixᴴ ⊗ₖ hStruct.physicalIsometryMatrixᴴ := by
  classical
  ext p σ
  simp [Matrix.reindex_apply, LinearMap.toMatrix'_apply,
    AppendixBStructuralData.physicalIsometryTensorPowerLeftInverse,
    AppendixBStructuralData.physicalIsometryMatrix, finTwoArrowEquiv,
    Pi.single_apply, Fin.prod_univ_two, Matrix.conjTranspose_apply]

/-- The reindexed two-site transported matrix is the virtual bond matrix
sandwiched by the Kronecker square of the physical isometry.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
theorem AppendixBStructuralData.transportedTwoSiteBondProjection_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection) =
      (hStruct.physicalIsometryMatrix ⊗ₖ hStruct.physicalIsometryMatrix) *
        Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
          (finTwoArrowEquiv (Fin D × Fin D))
          (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection) *
        (hStruct.physicalIsometryMatrixᴴ ⊗ₖ hStruct.physicalIsometryMatrixᴴ) := by
  rw [AppendixBStructuralData.transportedTwoSiteBondProjection,
    LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
  rw [← Matrix.mul_assoc]
  rw [← hStruct.physicalIsometryTensorPower_two_matrix,
    ← hStruct.physicalIsometryTensorPowerLeftInverse_two_matrix]
  exact reindex_three_mul (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin D × Fin D)) (finTwoArrowEquiv (Fin D × Fin D))
    (finTwoArrowEquiv (Fin d)) _ _ _

/-- Reindexing the first three-site virtual bond projector gives the standard
left pair matrix of the two-site virtual projector. -/
private theorem AppendixBStructuralData.leftVirtualBondProjection_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finThreeArrowEquiv (Fin D × Fin D))
        (finThreeArrowEquiv (Fin D × Fin D))
        (LinearMap.toMatrix' hStruct.leftVirtualBondProjection) =
      appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
        (finTwoArrowEquiv (Fin D × Fin D))
        (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) := by
  classical
  ext p q
  by_cases hs : p.2.2 = q.2.2
  · simp [appendixBLeftPairMatrix, appendixBLeftPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.leftVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond01_eq_iff,
      appendixBFirstPairCfg, finThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]
  · simp [appendixBLeftPairMatrix, appendixBLeftPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.leftVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond01_eq_iff,
      appendixBFirstPairCfg, finThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]

/-- Reindexing the second three-site virtual bond projector gives the standard
right pair matrix of the two-site virtual projector. -/
private theorem AppendixBStructuralData.rightVirtualBondProjection_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finThreeArrowEquiv (Fin D × Fin D))
        (finThreeArrowEquiv (Fin D × Fin D))
        (LinearMap.toMatrix' hStruct.rightVirtualBondProjection) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
        (finTwoArrowEquiv (Fin D × Fin D))
        (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) := by
  classical
  ext p q
  by_cases hs : p.1 = q.1
  · simp [appendixBRightPairMatrix, appendixBRightPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.rightVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond12_eq_iff,
      appendixBLastPairCfg, finThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, Matrix.one_apply, hs]
  · simp [appendixBRightPairMatrix, appendixBRightPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.rightVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond12_eq_iff,
      appendixBLastPairCfg, finThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]

/-- The two standard pair matrices of the virtual bond projector commute.

Source: arXiv:1606.00608, Appendix B, lines 1305--1307. -/
theorem AppendixBStructuralData.virtualPairMatrices_comm
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
          (finTwoArrowEquiv (Fin D × Fin D))
          (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) *
        appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
          (finTwoArrowEquiv (Fin D × Fin D))
          (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
          (finTwoArrowEquiv (Fin D × Fin D))
          (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) *
        appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
          (finTwoArrowEquiv (Fin D × Fin D))
          (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)) := by
  rw [← hStruct.leftVirtualBondProjection_matrix,
    ← hStruct.rightVirtualBondProjection_matrix]
  let e := finThreeArrowEquiv (Fin D × Fin D)
  have hMatrix := congrArg LinearMap.toMatrix'
    hStruct.leftVirtualBondProjection_comp_right
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at hMatrix
  calc
    _ = Matrix.reindex e e
        (LinearMap.toMatrix' hStruct.leftVirtualBondProjection *
          LinearMap.toMatrix' hStruct.rightVirtualBondProjection) := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' hStruct.leftVirtualBondProjection)
          (LinearMap.toMatrix' hStruct.rightVirtualBondProjection)
    _ = Matrix.reindex e e
        (LinearMap.toMatrix' hStruct.rightVirtualBondProjection *
          LinearMap.toMatrix' hStruct.leftVirtualBondProjection) := congrArg _ hMatrix
    _ = _ := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' hStruct.rightVirtualBondProjection)
          (LinearMap.toMatrix' hStruct.leftVirtualBondProjection)).symm


end MPSTensor
