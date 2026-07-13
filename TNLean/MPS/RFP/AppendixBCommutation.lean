/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.AppendixBSupport
import TNLean.MPS.RFP.KroneckerTransport

/-!
# Appendix B support-projector commutation

This file transports the two commuting placements of the virtual rank-one bond
projector through the three-site physical isometry.  The calculation uses the
identity \(U^*U=1\) and does not require the physical isometry to be
surjective.  It proves a local three-site commutator, which is transported to
every periodic chain with \(N>2\) in
`TNLean.MPS.RFP.AppendixBChainCommutation`.  The remaining canonical-form and
ground-space spanning restrictions are recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578, and the
parent-space construction, lines 511--524.
-/

open scoped Matrix BigOperators InnerProductSpace Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-! ### Matrices of adjacent pair lifts -/

/-- The right-associated identification of a three-coordinate function with a
triple. -/
private def appendixBFinThreeArrowEquiv (α : Type*) :
    (Fin 3 → α) ≃ α × (α × α) :=
  (Fin.consEquiv fun _ : Fin 3 ↦ α).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (finTwoArrowEquiv α))

@[simp] private theorem appendixBFinThreeArrowEquiv_symm_apply
    {alpha : Type*} (x : alpha × (alpha × alpha)) :
    (appendixBFinThreeArrowEquiv alpha).symm x = ![x.1, x.2.1, x.2.2] := by
  funext k
  fin_cases k <;> rfl

@[simp] private theorem axPairCfg_vecCons (a b c : Fin d) :
    axPairCfg ![a, b, c] = ![a, b] := by
  funext k
  fin_cases k <;> rfl

@[simp] private theorem xbPairCfg_vecCons (a b c : Fin d) :
    xbPairCfg ![a, b, c] = ![b, c] := by
  funext k
  fin_cases k <;> rfl

/-- Replacing the first pair gives a prescribed triple precisely when the new
pair and untouched final coordinate agree. -/
private theorem replaceAXCfg_eq_iff (sigma tau : Cfg d 3) (alpha : Cfg d 2) :
    replaceAXCfg sigma alpha = tau ↔
      alpha = axPairCfg tau ∧ sigma 2 = tau 2 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg axPairCfg h,
      by simpa [replaceAXCfg] using congrFun h (2 : Fin 3)⟩
  · rintro ⟨rfl, h⟩
    funext k
    fin_cases k <;> simp [replaceAXCfg, axPairCfg, h]

/-- Replacing the final pair gives a prescribed triple precisely when the new
pair and untouched initial coordinate agree. -/
private theorem replaceXBCfg_eq_iff (sigma tau : Cfg d 3) (beta : Cfg d 2) :
    replaceXBCfg sigma beta = tau ↔
      beta = xbPairCfg tau ∧ sigma 0 = tau 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg xbPairCfg h,
      by simpa [replaceXBCfg] using congrFun h (0 : Fin 3)⟩
  · rintro ⟨rfl, h⟩
    funext k
    fin_cases k <;> simp [replaceXBCfg, xbPairCfg, h]

/-- Reindexing the coefficient matrix of the first physical pair lift gives
the standard tensor-product matrix lift. -/
private theorem leftPairLift_toMatrix_reindex
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    Matrix.reindex (appendixBFinThreeArrowEquiv (Fin d))
        (appendixBFinThreeArrowEquiv (Fin d))
        (LinearMap.toMatrix' (leftPairLift Q)) =
      appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d)) (LinearMap.toMatrix' Q)) := by
  classical
  ext σ τ
  by_cases h : σ.2.2 = τ.2.2
  · have hslice : (fun α ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) α)) =
        (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ) :
          NSiteSpace d 2) := by
      funext α
      simp only [Pi.single_apply]
      simp only [replaceAXCfg_eq_iff]
      simp [finTwoArrowEquiv, h]
    change Q (fun α ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) α))
        (axPairCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ)) =
      Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ))
        ((finTwoArrowEquiv (Fin d)).symm (σ.1, σ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [hslice]
    simp [finTwoArrowEquiv, h]
  · have hslice : (fun α ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) α)) = 0 := by
      funext α
      simp only [Pi.single_apply, Pi.zero_apply]
      simp only [replaceAXCfg_eq_iff]
      simp [h]
    change Q (fun α ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceAXCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) α))
        (axPairCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ)) =
      Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.1, τ.2.1)) (1 : ℂ))
        ((finTwoArrowEquiv (Fin d)).symm (σ.1, σ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [hslice]
    simp [h]

/-- Reindexing the coefficient matrix of the second physical pair lift gives
the standard tensor-product matrix lift. -/
private theorem rightPairLift_toMatrix_reindex
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    Matrix.reindex (appendixBFinThreeArrowEquiv (Fin d))
        (appendixBFinThreeArrowEquiv (Fin d))
        (LinearMap.toMatrix' (rightPairLift Q)) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d)) (LinearMap.toMatrix' Q)) := by
  classical
  ext σ τ
  by_cases h : σ.1 = τ.1
  · have hslice : (fun β ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) β)) =
        (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ) :
          NSiteSpace d 2) := by
      funext β
      simp only [Pi.single_apply]
      simp only [replaceXBCfg_eq_iff]
      simp [finTwoArrowEquiv, h]
    change Q (fun β ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) β))
        (xbPairCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ)) =
      (if σ.1 = τ.1 then 1 else 0) *
        Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ))
          ((finTwoArrowEquiv (Fin d)).symm (σ.2.1, σ.2.2))
    rw [hslice]
    simp [finTwoArrowEquiv, h]
  · have hslice : (fun β ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) β)) = 0 := by
      funext β
      simp only [Pi.single_apply, Pi.zero_apply]
      simp only [replaceXBCfg_eq_iff]
      simp [h]
    change Q (fun β ↦
        (Pi.single ((appendixBFinThreeArrowEquiv (Fin d)).symm τ) (1 : ℂ) :
          NSiteSpace d 3)
          (replaceXBCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ) β))
        (xbPairCfg ((appendixBFinThreeArrowEquiv (Fin d)).symm σ)) =
      (if σ.1 = τ.1 then 1 else 0) *
        Q (Pi.single ((finTwoArrowEquiv (Fin d)).symm (τ.2.1, τ.2.2)) (1 : ℂ))
          ((finTwoArrowEquiv (Fin d)).symm (σ.2.1, σ.2.2))
    rw [hslice]
    simp [h]

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

/-- The one-site physical isometry in the pair-index basis. -/
private noncomputable def AppendixBStructuralData.physicalIsometryMatrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix (Fin d) (Fin D × Fin D) ℂ :=
  fun i p ↦ hStruct.U i p.1 p.2

/-- The reindexed two-site tensor-power matrix is the Kronecker square of the
one-site physical isometry. -/
private theorem AppendixBStructuralData.physicalIsometryTensorPower_two_matrix
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
of the conjugate transpose of the one-site physical isometry. -/
private theorem AppendixBStructuralData.physicalIsometryTensorPowerLeftInverse_two_matrix
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
sandwiched by the Kronecker square of the physical isometry. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjection_matrix
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

/-- The one-site physical matrix is an isometry on the virtual pair space. -/
private theorem AppendixBStructuralData.physicalIsometryMatrix_isometry
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.physicalIsometryMatrixᴴ * hStruct.physicalIsometryMatrix = 1 := by
  classical
  ext p q
  by_cases hpq : p = q
  · subst q
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      AppendixBStructuralData.physicalIsometryMatrix] using hStruct.hU_pair p p
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hpq,
      AppendixBStructuralData.physicalIsometryMatrix] using hStruct.hU_pair p q

/-- Reindexing the first three-site virtual bond projector gives the standard
left pair matrix of the two-site virtual projector. -/
private theorem AppendixBStructuralData.leftVirtualBondProjection_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (appendixBFinThreeArrowEquiv (Fin D × Fin D))
        (appendixBFinThreeArrowEquiv (Fin D × Fin D))
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
      appendixBFirstPairCfg, appendixBFinThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]
  · simp [appendixBLeftPairMatrix, appendixBLeftPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.leftVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond01_eq_iff,
      appendixBFirstPairCfg, appendixBFinThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]

/-- Reindexing the second three-site virtual bond projector gives the standard
right pair matrix of the two-site virtual projector. -/
private theorem AppendixBStructuralData.rightVirtualBondProjection_matrix
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (appendixBFinThreeArrowEquiv (Fin D × Fin D))
        (appendixBFinThreeArrowEquiv (Fin D × Fin D))
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
      appendixBLastPairCfg, appendixBFinThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, Matrix.one_apply, hs]
  · simp [appendixBRightPairMatrix, appendixBRightPairMatrixAux,
      Matrix.reindex_apply, LinearMap.toMatrix'_apply,
      AppendixBStructuralData.rightVirtualBondProjection,
      AppendixBStructuralData.twoSiteVirtualBondProjection,
      hStruct.replaceVirtualBond12_eq_iff,
      appendixBLastPairCfg, appendixBFinThreeArrowEquiv, finTwoArrowEquiv,
      Pi.single_apply, hs]

/-- The two standard pair matrices of the virtual bond projector commute. -/
private theorem AppendixBStructuralData.virtualPairMatrices_comm
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
  let e := appendixBFinThreeArrowEquiv (Fin D × Fin D)
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

/-- The two pair placements of the transported virtual bond matrix commute on
three physical sites. -/
private theorem AppendixBStructuralData.transportedPairMatrices_comm
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) *
        appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) *
        appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) := by
  rw [hStruct.transportedTwoSiteBondProjection_matrix]
  let B := Matrix.reindex (finTwoArrowEquiv (Fin D × Fin D))
    (finTwoArrowEquiv (Fin D × Fin D))
    (LinearMap.toMatrix' hStruct.twoSiteVirtualBondProjection)
  have hB : appendixBLeftPairMatrix B * appendixBRightPairMatrix B =
      appendixBRightPairMatrix B * appendixBLeftPairMatrix B := by
    simpa [B, appendixBLeftPairMatrix, appendixBRightPairMatrix,
      appendixBLeftPairMatrixAux,
      appendixBRightPairMatrixAux] using hStruct.virtualPairMatrices_comm
  simpa [B, appendixBLeftPairMatrix, appendixBRightPairMatrix,
    appendixBLeftPairMatrixAux,
    appendixBRightPairMatrixAux] using
    appendixB_transportedPairMatrices_comm hStruct.physicalIsometryMatrix B
      hStruct.physicalIsometryMatrix_isometry hB

/-- The two adjacent lifts of the transported virtual bond projector commute
on the three-site physical coefficient space. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjection_commute_lifts
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    leftPairLift hStruct.transportedTwoSiteBondProjection *
        rightPairLift hStruct.transportedTwoSiteBondProjection =
      rightPairLift hStruct.transportedTwoSiteBondProjection *
        leftPairLift hStruct.transportedTwoSiteBondProjection := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_mul]
  let e := appendixBFinThreeArrowEquiv (Fin d)
  apply (Matrix.reindexLinearEquiv ℂ ℂ e e).injective
  simp only [Matrix.coe_reindexLinearEquiv]
  calc
    _ = Matrix.reindex e e
          (LinearMap.toMatrix' (leftPairLift hStruct.transportedTwoSiteBondProjection)) *
        Matrix.reindex e e
          (LinearMap.toMatrix' (rightPairLift hStruct.transportedTwoSiteBondProjection)) := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' (leftPairLift hStruct.transportedTwoSiteBondProjection))
          (LinearMap.toMatrix'
            (rightPairLift hStruct.transportedTwoSiteBondProjection))).symm
    _ = appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) *
        appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' hStruct.transportedTwoSiteBondProjection)) := by
      rw [leftPairLift_toMatrix_reindex, rightPairLift_toMatrix_reindex]
    _ = _ := hStruct.transportedPairMatrices_comm
    _ = Matrix.reindex e e
          (LinearMap.toMatrix' (rightPairLift hStruct.transportedTwoSiteBondProjection)) *
        Matrix.reindex e e
          (LinearMap.toMatrix' (leftPairLift hStruct.transportedTwoSiteBondProjection)) := by
      rw [leftPairLift_toMatrix_reindex, rightPairLift_toMatrix_reindex]
    _ = _ := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' (rightPairLift hStruct.transportedTwoSiteBondProjection))
          (LinearMap.toMatrix' (leftPairLift hStruct.transportedTwoSiteBondProjection))

/-! ### Euclidean transports and adjoints -/

/-- Regard a coefficient-space linear map as a map between the corresponding
Euclidean spaces. -/
private noncomputable def coefficientEuclideanMap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ :=
  (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm.toLinearMap.comp
    (T.comp (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap)

/-- The two-site physical tensor power as a Euclidean linear map. -/
private noncomputable def AppendixBStructuralData.physicalIsometryTwoES
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    EuclideanSpace ℂ (Fin 2 → Fin D × Fin D) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d 2) :=
  coefficientEuclideanMap (hStruct.physicalIsometryTensorPower 2)

/-- The two-site conjugate coefficient map as a Euclidean linear map. -/
private noncomputable def AppendixBStructuralData.physicalIsometryTwoAdjointES
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin 2 → Fin D × Fin D) :=
  coefficientEuclideanMap (hStruct.physicalIsometryTensorPowerLeftInverse 2)

/-- The conjugate coefficient map is the Hilbert-space adjoint of the two-site
physical isometry. -/
private theorem AppendixBStructuralData.physicalIsometryTwoAdjointES_eq_adjoint
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.physicalIsometryTwoAdjointES = hStruct.physicalIsometryTwoES.adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro ψ v
  simpa [AppendixBStructuralData.physicalIsometryTwoAdjointES,
    AppendixBStructuralData.physicalIsometryTwoES, coefficientEuclideanMap] using
    (hStruct.physicalIsometryTensorPower_adjoint_inner 2
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) ψ)
      ((WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)) v)).symm

/-- The two-site virtual bond projector as a Euclidean endomorphism. -/
private noncomputable def AppendixBStructuralData.twoSiteVirtualBondProjectionES
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    EuclideanSpace ℂ (Fin 2 → Fin D × Fin D) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin 2 → Fin D × Fin D) :=
  coefficientEuclideanMap hStruct.twoSiteVirtualBondProjection

/-- The transported two-site bond operator as a Euclidean endomorphism. -/
private noncomputable def AppendixBStructuralData.transportedTwoSiteBondProjectionES
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  coefficientEuclideanMap hStruct.transportedTwoSiteBondProjection

/-- Euclidean transport respects the three factors in the definition of the
transported bond operator. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjectionES_eq
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.transportedTwoSiteBondProjectionES =
      hStruct.physicalIsometryTwoES.comp
        (hStruct.twoSiteVirtualBondProjectionES.comp
          hStruct.physicalIsometryTwoAdjointES) := by
  apply LinearMap.ext
  intro v
  rfl

/-- Bond insertion and normalized bond contraction are adjoint up to the
squared norm of the bond vector. -/
private theorem AppendixBStructuralData.twoSiteBondInsertion_adjoint_inner
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) (v : Fin D × Fin D → ℂ)
    (w : (Fin 2 → Fin D × Fin D) → ℂ) :
    ⟪(WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm
          (hStruct.twoSiteBondInsertion v),
        (WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm w⟫_ℂ =
      hStruct.virtualBondNormSq *
        ⟪(WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm v,
          (WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
            (hStruct.twoSiteVirtualBoundaryContraction w)⟫_ℂ := by
  classical
  change (∑ p : Fin 2 → Fin D × Fin D,
      w p * star (hStruct.twoSiteBondInsertion v p)) =
    hStruct.virtualBondNormSq * ∑ ac : Fin D × Fin D,
      hStruct.twoSiteVirtualBoundaryContraction w ac * star (v ac)
  have hstar (p₀ p₁ : Fin D × Fin D) :
      star (if p₀.2 = p₁.1 then
        (hStruct.Λ p₀.2 : ℂ) * v (p₀.1, p₁.2) else 0) =
        if p₀.2 = p₁.1 then
          (hStruct.Λ p₀.2 : ℂ) * star (v (p₀.1, p₁.2)) else 0 := by
    split <;> simp_all
  have hconfig (a b c : Fin D) :
      hStruct.twoSiteVirtualBondConfig a c b = ![(a, b), (b, c)] := by
    funext t
    fin_cases t <;> simp
  calc
    _ = ∑ p₀ : Fin D × Fin D, ∑ p₁ : Fin D × Fin D,
        w ((finTwoArrowEquiv (Fin D × Fin D)).symm (p₀, p₁)) *
          star (if p₀.2 = p₁.1 then
            (hStruct.Λ p₀.2 : ℂ) * v (p₀.1, p₁.2) else 0) := by
      rw [← (finTwoArrowEquiv (Fin D × Fin D)).symm.sum_comp]
      rw [Fintype.sum_prod_type]
      simp [AppendixBStructuralData.twoSiteBondInsertion,
        finTwoArrowEquiv_symm_apply]
    _ = ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D,
        w (hStruct.twoSiteVirtualBondConfig a c b) *
          (hStruct.Λ b : ℂ) * star (v (a, c)) := by
      simp_rw [hstar]
      simp [Fintype.sum_prod_type, mul_assoc]
      simp_rw [hconfig]
    _ = hStruct.virtualBondNormSq * ∑ ac : Fin D × Fin D,
        hStruct.twoSiteVirtualBoundaryContraction w ac * star (v ac) := by
      simp only [AppendixBStructuralData.twoSiteVirtualBoundaryContraction,
        Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      change (∑ x : Fin D, w (hStruct.twoSiteVirtualBondConfig a c x) *
          (hStruct.Λ x : ℂ) * star (v (a, c))) =
        hStruct.virtualBondNormSq *
          ((hStruct.virtualBondNormSq⁻¹ * ∑ k : Fin D,
            (hStruct.Λ k : ℂ) *
              w (hStruct.twoSiteVirtualBondConfig a c k)) * star (v (a, c)))
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The squared norm of the real-weight bond vector is fixed by complex
conjugation. -/
private theorem AppendixBStructuralData.star_virtualBondNormSq
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    star hStruct.virtualBondNormSq = hStruct.virtualBondNormSq := by
  simp [AppendixBStructuralData.virtualBondNormSq, star_sum, star_mul]

/-- The normalized virtual bond projector is symmetric for the Euclidean inner
product. -/
private theorem AppendixBStructuralData.twoSiteVirtualBondProjection_inner
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0)
    (v w : (Fin 2 → Fin D × Fin D) → ℂ) :
    ⟪(WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm
          (hStruct.twoSiteVirtualBondProjection v),
        (WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm w⟫_ℂ =
      ⟪(WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm v,
        (WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm
          (hStruct.twoSiteVirtualBondProjection w)⟫_ℂ := by
  rw [hStruct.twoSiteVirtualBondProjection_eq_comp]
  simp only [LinearMap.comp_apply]
  calc
    _ = hStruct.virtualBondNormSq *
        ⟪(WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
            (hStruct.twoSiteVirtualBoundaryContraction v),
          (WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
            (hStruct.twoSiteVirtualBoundaryContraction w)⟫_ℂ :=
      hStruct.twoSiteBondInsertion_adjoint_inner hφ _ _
    _ = star (⟪(WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm
          (hStruct.twoSiteBondInsertion
            (hStruct.twoSiteVirtualBoundaryContraction w)),
        (WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)).symm v⟫_ℂ) := by
      rw [hStruct.twoSiteBondInsertion_adjoint_inner hφ]
      simp only [star_mul, hStruct.star_virtualBondNormSq]
      have hi : star (⟪(WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
          (hStruct.twoSiteVirtualBoundaryContraction w),
        (WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
          (hStruct.twoSiteVirtualBoundaryContraction v)⟫_ℂ) =
          ⟪(WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
            (hStruct.twoSiteVirtualBoundaryContraction v),
          (WithLp.linearEquiv 2 ℂ (Fin D × Fin D → ℂ)).symm
            (hStruct.twoSiteVirtualBoundaryContraction w)⟫_ℂ :=
        inner_conj_symm _ _
      rw [hi]
      exact mul_comm _ _
    _ = _ := inner_conj_symm _ _

/-- The virtual bond projector is a symmetric projection on the Euclidean
coefficient space. -/
private theorem AppendixBStructuralData.twoSiteVirtualBondProjectionES_isSymmetricProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) :
    hStruct.twoSiteVirtualBondProjectionES.IsSymmetricProjection where
  isIdempotentElem := by
    apply LinearMap.ext
    intro v
    simpa [AppendixBStructuralData.twoSiteVirtualBondProjectionES,
      coefficientEuclideanMap, Module.End.mul_apply] using
      LinearMap.congr_fun (hStruct.twoSiteVirtualBondProjection_idempotent hφ)
        ((WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)) v)
  isSymmetric := by
    intro v w
    simpa [AppendixBStructuralData.twoSiteVirtualBondProjectionES,
      coefficientEuclideanMap] using
      hStruct.twoSiteVirtualBondProjection_inner hφ
        ((WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)) v)
        ((WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin D × Fin D) → ℂ)) w)

/-- The transported virtual bond operator is a symmetric projection on the
two-site physical Euclidean space. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjectionES_isSymmetricProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) :
    hStruct.transportedTwoSiteBondProjectionES.IsSymmetricProjection where
  isIdempotentElem := by
    apply LinearMap.ext
    intro v
    simpa [AppendixBStructuralData.transportedTwoSiteBondProjectionES,
      coefficientEuclideanMap, Module.End.mul_apply] using
      LinearMap.congr_fun (hStruct.transportedTwoSiteBondProjection_idempotent hφ)
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) v)
  isSymmetric := by
    rw [hStruct.transportedTwoSiteBondProjectionES_eq,
      hStruct.physicalIsometryTwoAdjointES_eq_adjoint]
    exact (hStruct.twoSiteVirtualBondProjectionES_isSymmetricProjection hφ).isSymmetric
      |>.conj_adjoint hStruct.physicalIsometryTwoES

/-- The Euclidean transported projector has the canonical two-site ground
space as its range. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjectionES_range
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) :
    LinearMap.range hStruct.transportedTwoSiteBondProjectionES =
      groundSpaceES hStruct.coreTensor 2 := by
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩
    apply (mem_groundSpaceES_iff hStruct.coreTensor 2 _).2
    change hStruct.transportedTwoSiteBondProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) v) ∈
        groundSpace hStruct.coreTensor 2
    rw [← AppendixBStructuralData.twoSiteBasicSpace]
    rw [← hStruct.twoSiteBasicEmbedding_range,
      ← hStruct.transportedTwoSiteBondProjection_range hφ]
    exact ⟨_, rfl⟩
  · intro hψ
    have hraw : (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) ψ ∈
        LinearMap.range hStruct.transportedTwoSiteBondProjection := by
      rw [hStruct.transportedTwoSiteBondProjection_range hφ,
        hStruct.twoSiteBasicEmbedding_range]
      exact (mem_groundSpaceES_iff hStruct.coreTensor 2 ψ).1 hψ
    obtain ⟨v, hv⟩ := hraw
    refine ⟨(WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v, ?_⟩
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).injective
    simpa [AppendixBStructuralData.transportedTwoSiteBondProjectionES,
      coefficientEuclideanMap] using hv

/-- For a nonzero virtual bond, its physical transport is the canonical
orthogonal support projector onto the two-site basic space. -/
private theorem AppendixBStructuralData.transportedTwoSiteBondProjection_eq_support_of_ne
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) :
    hStruct.transportedTwoSiteBondProjection =
      hStruct.twoSiteBasicSupportProjection := by
  have hEq : hStruct.transportedTwoSiteBondProjectionES =
      (groundSpaceES hStruct.coreTensor 2).starProjection.toLinearMap :=
    (hStruct.transportedTwoSiteBondProjectionES_isSymmetricProjection hφ).ext
      (Submodule.isSymmetricProjection_starProjection _)
      (by
        rw [Submodule.range_starProjection]
        exact hStruct.transportedTwoSiteBondProjectionES_range hφ)
  apply LinearMap.ext
  intro ψ
  have hψ := LinearMap.congr_fun hEq
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ)
  apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm.injective
  simpa [AppendixBStructuralData.transportedTwoSiteBondProjectionES,
    coefficientEuclideanMap,
    AppendixBStructuralData.twoSiteBasicSupportProjection] using hψ

/-- The physical transport of the rank-one virtual bond projector is the
canonical two-site basic support projector.  The statement also covers the
zero-dimensional virtual space, where both maps vanish.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578, and the
parent-space construction, lines 511--524. -/
theorem AppendixBStructuralData.transportedTwoSiteBondProjection_eq_support
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.transportedTwoSiteBondProjection =
      hStruct.twoSiteBasicSupportProjection := by
  cases isEmpty_or_nonempty (Fin D) with
  | inr hnonempty =>
      letI : Nonempty (Fin D) := hnonempty
      exact hStruct.transportedTwoSiteBondProjection_eq_support_of_ne
        hStruct.virtualBondNormSq_ne_zero
  | inl hempty =>
      letI : IsEmpty (Fin D) := hempty
      have hInsertion : hStruct.twoSiteBondInsertion = 0 := by
        apply LinearMap.ext
        intro v
        funext p
        exact isEmptyElim (p 0).1
      have hEmbedding : hStruct.twoSiteBasicEmbedding = 0 := by
        simp [AppendixBStructuralData.twoSiteBasicEmbedding, hInsertion]
      have hSupport : hStruct.twoSiteBasicSupportProjection = 0 := by
        apply LinearMap.range_eq_bot.mp
        rw [hStruct.twoSiteBasicSupportProjection_range_eq_embedding, hEmbedding]
        exact LinearMap.range_zero
      have hTransport : hStruct.transportedTwoSiteBondProjection = 0 := by
        apply LinearMap.ext
        intro ψ
        simp only [AppendixBStructuralData.transportedTwoSiteBondProjection,
          LinearMap.comp_apply]
        have hleft : hStruct.physicalIsometryTensorPowerLeftInverse 2 ψ = 0 := by
          funext p
          exact isEmptyElim (p 0).1
        rw [hleft, map_zero, map_zero, LinearMap.zero_apply]
      rw [hTransport, hSupport]

/-- The two adjacent lifts of the canonical two-site basic support projector
commute on the three-site coefficient space.

Source: arXiv:1606.00608, parent-space construction, lines 511--524, and the
Appendix B basic-vector form, equations (3.16)--(3.18), lines 543--578. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_commute_lifts
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    leftPairLift hStruct.twoSiteBasicSupportProjection *
        rightPairLift hStruct.twoSiteBasicSupportProjection =
      rightPairLift hStruct.twoSiteBasicSupportProjection *
        leftPairLift hStruct.twoSiteBasicSupportProjection := by
  rw [← hStruct.transportedTwoSiteBondProjection_eq_support]
  exact hStruct.transportedTwoSiteBondProjection_commute_lifts

/-- Commutation of the two lifted basic-support projectors implies the
overlapping two-site commutation condition for their complementary Appendix B
parent interactions.

Source: arXiv:1606.00608, parent construction, lines 511--524, equations
(3.17)--(3.18), lines 564--578, and Definition D.2, lines 2205--2218. -/
theorem AppendixBStructuralData.hasOverlappingTwoSiteCommutation_of_support_commute
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hcomm :
      leftPairLift hStruct.twoSiteBasicSupportProjection *
          rightPairLift hStruct.twoSiteBasicSupportProjection =
        rightPairLift hStruct.twoSiteBasicSupportProjection *
          leftPairLift hStruct.twoSiteBasicSupportProjection) :
    HasOverlappingTwoSiteCommutation (d := d) hStruct.appendixBQAXOnCoeffSpace
      hStruct.appendixBQXBOnCoeffSpace := by
  let hSupport : HasOverlappingTwoSiteCommutation (d := d)
      hStruct.twoSiteBasicSupportProjection hStruct.twoSiteBasicSupportProjection :=
    { left_idempotent := hStruct.twoSiteBasicSupportProjection_idempotent
      right_idempotent := hStruct.twoSiteBasicSupportProjection_idempotent
      commute_lifts := hcomm }
  have hComplement := hSupport.complement
  simpa [hStruct.twoSiteBasicSupportProjection_eq_complement,
    AppendixBStructuralData.appendixBQAXOnCoeffSpace,
    AppendixBStructuralData.appendixBQXBOnCoeffSpace] using hComplement

/-- The two overlapping Appendix B parent interactions commute on three sites.

Source: arXiv:1606.00608, parent-space construction, lines 511--524,
equations (3.16)--(3.18), lines 543--578, and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.hasOverlappingTwoSiteCommutation
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    HasOverlappingTwoSiteCommutation (d := d) hStruct.appendixBQAXOnCoeffSpace
      hStruct.appendixBQXBOnCoeffSpace :=
  hStruct.hasOverlappingTwoSiteCommutation_of_support_commute
    hStruct.twoSiteBasicSupportProjection_commute_lifts

end MPSTensor
