/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.C3CorrectionBounds

/-!
# Whole-increment finite-Gram correction bounds

This file factors and bounds the three finite-Gram correction sandwiches for an
arbitrary suffix increment. The formulas extend the one-site C3 correction
telescope to the exact C3-prime whole-increment geometry. They are reconstructed
from the boundary-map and Gram identities and assert no numerical contraction.

## Main definitions

* `wholeIncrementTailFiniteGramCorrectionES`
* `wholeIncrementFullInverseGramCorrectionES`
* `wholeIncrementLeftFiniteGramCorrectionES`
* `wholeIncrementCenteredProjectorResidualES`

## Main results

* `wholeIncrement_limitingOverlapProduct_eq`
* `reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram`
* `inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram`
* `wholeIncrementLeftFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
* `wholeIncrementTailFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
* `norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt`
* `wholeIncrement_virtualResidual_eq_centered_sub_gramErrors`
* `wholeIncrement_injectiveRangeProjector_residual_eq_centered_sub_corrections`
* `wholeIncrementTailFiniteGramCorrectionES_norm_le`
* `wholeIncrementFullInverseGramCorrectionES_norm_le`
* `wholeIncrementLeftFiniteGramCorrectionES_norm_le`
-/

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- The overlap-factor limiting product agrees with the virtual-word limiting
product for an arbitrary suffix increment. -/
theorem wholeIncrement_limitingOverlapProduct_eq [NeZero D]
    (A : MPSTensor d D) (K Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    (wholeIncrementLeftOverlapFactorES A K Q).adjoint.comp
        ((boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d Q) Kinf).comp
          (wholeIncrementRightOverlapFactorES A K Q)) =
      (boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
        ((tailVirtualMapES A K).comp
          ((Ring.inverse Kinf).comp
            ((leftVirtualMapES A Q).adjoint.comp
              (boundaryFiberwiseMap (D := D) (Cfg d Q) Kinf)))) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [inner_boundaryFiberwiseMap]
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  rw [Fintype.sum_prod_type]
  change (∑ u : Cfg d K, ∑ j : Cfg d Q,
      inner ℂ
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d Q)
            (wholeIncrementLeftOverlapFactorES A K Q x) (u, j)))
        ((Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
            (boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d Q)
              (wholeIncrementRightOverlapFactorES A K Q y) (u, j))))) = _
  simp_rw [boundaryFamilyEquiv_wholeIncrementLeftOverlapFactorES_apply,
    boundaryFamilyEquiv_wholeIncrementRightOverlapFactorES_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply]
  rw [leftVirtualMapES_adjoint_apply]
  simp_rw [boundaryFamilyEquiv_boundaryFiberwiseMap_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  rw [Matrix.inverse_gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply
    (hρ := hρ)]
  simp only [Finset.sum_mul, Finset.smul_sum, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hρ.trace_pos),
    Matrix.mul_assoc,
    Matrix.mul_nonsing_inv ρ (ρ.isUnit_iff_isUnit_det.mp hρ.isUnit),
    Matrix.mul_one, one_smul]
  rw [inner_boundaryFiberwiseMap]
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  simp_rw [Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply]
  simp_rw [boundaryFamilyEquiv_tailVirtualMapES_apply]
  simp only [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_smul, Finset.smul_sum,
    Matrix.trace_sum, Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ### Whole-increment finite-Gram corrections -/

/-- Reassociation does not change the tail boundary Gram. -/
theorem reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram
    (A : MPSTensor d D) (K L Q : ℕ) :
    (reassocTailBoundaryMapES A K L Q).adjoint.comp
        (reassocTailBoundaryMapES A K L Q) =
      boundaryFiberwiseMap (D := D) (Cfg d K) (groundSpaceGram A (L + Q)) := by
  have hreassoc :
      (physicalReassocES (d := d) K L Q).toContinuousLinearMap.adjoint.comp
        (physicalReassocES (d := d) K L Q).toContinuousLinearMap = 1 :=
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (finCongr (Nat.add_assoc K L Q).symm)
          (Equiv.refl (Fin d)))).isometry
  rw [reassocTailBoundaryMapES, ContinuousLinearMap.adjoint_comp]
  have hcomp := congrArg (fun X =>
      (tailBoundaryMapES A K (L + Q)).adjoint.comp
        (X.comp (tailBoundaryMapES A K (L + Q)))) hreassoc
  simp only [ContinuousLinearMap.comp_assoc] at hcomp
  rw [ContinuousLinearMap.comp_assoc, hcomp]
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    tailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram A K (L + Q)

/-- The inverse Gram of the reassociated tail map remains fiberwise. -/
theorem inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
        ((physicalReassocES (d := d) K L Q).injective.comp
          (tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K (L + Q) h)) =
      boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h) := by
  rw [ContinuousLinearMap.inverseGram_eq_inverse]
  apply ContinuousLinearMap.inverse_eq
  · rw [reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  · rw [reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
      groundSpaceGram, boundaryFiberwiseMap_comp,
      ContinuousLinearMap.inverseGram_comp_adjoint_comp_self,
      boundaryFiberwiseMap_id]

/-- The left finite Gram cancels its inverse for an arbitrary suffix increment. -/
theorem wholeIncrementLeftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (K + L))) :
    (leftVirtualMapES A Q).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d Q)
        (groundSpaceGram A (K + L))).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d Q)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (K + L)) h)).comp
        (leftBoundaryMapES A (K + L) Q).adjoint)) =
      (groundSpaceMapES A (K + L + Q)).adjoint := by
  simpa only using leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    A (K + L) Q h

/-- The reassociated tail finite Gram cancels its inverse. -/
theorem wholeIncrementTailFiniteGramCancellation_eq_groundSpaceMapES_adjoint
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    (tailVirtualMapES A K).adjoint.comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K)
        (groundSpaceGram A (L + Q))).comp
      ((boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)).comp
        (reassocTailBoundaryMapES A K L Q).adjoint)) =
      (groundSpaceMapES A (K + L + Q)).adjoint := by
  have hcancel : (boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)) =
      ContinuousLinearMap.id ℂ _ := by
    rw [boundaryFiberwiseMap_comp, groundSpaceGram,
      ContinuousLinearMap.adjoint_comp_self_comp_inverseGram,
      boundaryFiberwiseMap_id]
  change ((tailVirtualMapES A K).adjoint.comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))).comp
    (boundaryFiberwiseMap (D := D) (Cfg d K)
      (ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h)))).comp
      (reassocTailBoundaryMapES A K L Q).adjoint = _
  rw [hcancel, ContinuousLinearMap.comp_id, ← ContinuousLinearMap.adjoint_comp,
    reassocTailBoundaryMapES_comp_tailVirtualMapES]

/-- Tail finite-Gram correction for a suffix increment of length \(Q\). -/
noncomputable def wholeIncrementTailFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q) - Kinf)).comp
    ((tailVirtualMapES A K).comp
      (Ifull.comp (groundSpaceMapES A (K + L + Q)).adjoint)))

/-- Full inverse-Gram correction for a suffix increment of length \(Q\). -/
noncomputable def wholeIncrementFullInverseGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  let Ifull := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
    ((tailVirtualMapES A K).comp
    ((Ifull - Iinf).comp (groundSpaceMapES A (K + L + Q)).adjoint)))

/-- Left finite-Gram correction for a suffix increment of length \(Q\). -/
noncomputable def wholeIncrementLeftFiniteGramCorrectionES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
    A (K + L) Q hLocalLeft
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  ((reassocTailBoundaryMapES A K L Q).comp
      (boundaryFiberwiseMap (D := D) (Cfg d K)
        (ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail))).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Kinf).comp
    ((tailVirtualMapES A K).comp
    (Iinf.comp
    ((leftVirtualMapES A Q).adjoint.comp
    ((boundaryFiberwiseMap (D := D) (Cfg d Q)
      (groundSpaceGram A (K + L) - Kinf)).comp
    ((ContinuousLinearMap.inverseGram
      (leftBoundaryMapES A (K + L) Q) hLeft).comp
        (leftBoundaryMapES A (K + L) Q).adjoint))))))

/-- The reassociated tail pseudoinverse has the same square-root bound as the
unreassociated tail map. -/
theorem norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
    (A : MPSTensor d D) (K L Q : ℕ)
    (h : Function.Injective (groundSpaceMapES A (L + Q))) :
    let hTail := (physicalReassocES (d := d) K L Q).injective.comp
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective A K (L + Q) h)
    ‖(reassocTailBoundaryMapES A K L Q).comp
      (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q) hTail)‖ ≤
      Real.sqrt ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A (L + Q)) h‖ := by
  dsimp only
  rw [ContinuousLinearMap.norm_T_comp_inverseGram_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram A K L Q h]
  exact norm_boundaryFiberwiseMap_le _ _



/-- Exact whole-increment virtual telescope around the limiting Gram metric. -/
theorem wholeIncrement_virtualResidual_eq_centered_sub_gramErrors [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K)
      (groundSpaceGram A (L + Q))
    let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
    let Kleft := boundaryFiberwiseMap (D := D) (Cfg d Q)
      (groundSpaceGram A (K + L))
    let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d Q) Kinf
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L + Q)) hFull
    let Iinf := Ring.inverse Kinf
    let Jtail := tailVirtualMapES A K
    let JleftAdj := (leftVirtualMapES A Q).adjoint
    (reassocTailBoundaryMapES A K L Q).adjoint.comp
          (leftBoundaryMapES A (K + L) Q) -
        Ktail.comp (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) =
      wholeIncrementCenteredResidualES A K L Q ρ (ne_of_gt hρ.trace_pos) -
      (Ktail - Kinftail).comp
        (Jtail.comp (Ifull.comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp ((Ifull - Iinf).comp (JleftAdj.comp Kleft))) -
      Kinftail.comp
        (Jtail.comp (Iinf.comp (JleftAdj.comp (Kleft - Kinfleft)))) := by
  dsimp only
  rw [wholeIncrementCenteredResidualES,
    wholeIncrement_limitingOverlapProduct_eq A K Q ρ hρ]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

/-- The physical sandwich containing the centered residual for a suffix increment
of length \(Q\). -/
noncomputable def wholeIncrementCenteredProjectorResidualES [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    EuclideanSpace ℂ (Cfg d (K + L + Q)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + L + Q)) :=
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (L + Q)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L)) hLocalLeft
  (reassocTailBoundaryMapES A K L Q).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
      ((wholeIncrementCenteredResidualES A K L Q ρ
        (ne_of_gt hρ.trace_pos)).comp
        ((boundaryFiberwiseMap (D := D) (Cfg d Q) Ileft).comp
          (leftBoundaryMapES A (K + L) Q).adjoint)))


/-- Exact assembly of the arbitrary-suffix projector defect into the centered
physical sandwich and the three finite-Gram correction sandwiches. -/
theorem wholeIncrement_injectiveRangeProjector_residual_eq_centered_sub_corrections
    [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    let hTail := (physicalReassocES (d := d) K L Q).injective.comp
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
        A K (L + Q) hLocalTail)
    let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
      A (K + L) Q hLocalLeft
    (ContinuousLinearMap.injectiveRangeProjector
        (reassocTailBoundaryMapES A K L Q) hTail).comp
        (ContinuousLinearMap.injectiveRangeProjector
          (leftBoundaryMapES A (K + L) Q) hLeft) -
      ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES A (K + L + Q)) hFull =
      wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
          hLocalTail hLocalLeft -
        wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
          hLocalTail hFull -
        wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
          hLocalTail hFull -
        wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
          hLocalTail hLocalLeft := by
  dsimp only
  rw [whole_increment_injectiveRangeProjector_residual_eq]
  rw [inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
      A K L Q hLocalTail,
    inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
      A (K + L) Q hLocalLeft,
    reassocTailBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
    leftBoundaryMapES_adjoint_comp_self_eq_fiberwise_groundSpaceGram,
    wholeIncrement_virtualResidual_eq_centered_sub_gramErrors
      A K L Q ρ hρ hFull]
  ext x
  have hcancel := congrArg (fun f => f x)
    (wholeIncrementLeftFiniteGramCancellation_eq_groundSpaceMapES_adjoint
      A K L Q hLocalLeft)
  simp only [ContinuousLinearMap.comp_apply] at hcancel
  have hinv := congrArg (fun f =>
      f ((leftBoundaryMapES A (K + L) Q).adjoint x))
    (inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
      A (K + L) Q hLocalLeft)
  simp only [wholeIncrementCenteredProjectorResidualES,
    wholeIncrementTailFiniteGramCorrectionES,
    wholeIncrementFullInverseGramCorrectionES,
    wholeIncrementLeftFiniteGramCorrectionES, boundaryFiberwiseMap_sub,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_apply, sub_apply, hcancel, hinv]

/-- Raw operator-norm bound for the arbitrary-suffix tail finite-Gram correction. -/
theorem wholeIncrementTailFiniteGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (L + Q)) hLocalTail
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L + Q)) hFull
    ‖wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
      hLocalTail hFull‖ ≤
      Real.sqrt ‖Itail‖ * ‖groundSpaceGram A (L + Q) - Kinf‖ *
        ‖tailVirtualMapES A K‖ * Real.sqrt ‖Ifull‖ := by
  dsimp only
  let Ptail := (reassocTailBoundaryMapES A K L Q).comp
    (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
      ((physicalReassocES (d := d) K L Q).injective.comp
        (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
          A K (L + Q) hLocalTail)))
  let E := boundaryFiberwiseMap (D := D) (Cfg d K)
    (groundSpaceGram A (L + Q) - Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
  let J := tailVirtualMapES A K
  let Pfull := (ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull).comp
      (groundSpaceMapES A (K + L + Q)).adjoint
  simp only [wholeIncrementTailFiniteGramCorrectionES]
  rw [← inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    A K L Q hLocalTail]
  change ‖Ptail.comp (E.comp (J.comp Pfull))‖ ≤ _
  calc
    _ ≤ ‖Ptail‖ * ‖E.comp (J.comp Pfull)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖E‖ * ‖J.comp Pfull‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖E‖ * (‖J‖ * ‖Pfull‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖E‖ * ‖J‖ * ‖Pfull‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ *
        ‖groundSpaceGram A (L + Q) - Matrix.gramReshuffle
          (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ *
        ‖tailVirtualMapES A K‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L + Q)) hFull‖ := by
      dsimp only [Ptail, E, J, Pfull]
      rw [ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt]
      gcongr
      · exact norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
          A K L Q hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
    _ = _ := by ring

/-- Raw operator-norm bound for the arbitrary-suffix full inverse-Gram correction. -/
theorem wholeIncrementFullInverseGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hFull : Function.Injective (groundSpaceMapES A (K + L + Q))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (L + Q)) hLocalTail
    let Ifull := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L + Q)) hFull
    ‖wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
      hLocalTail hFull‖ ≤
      Real.sqrt ‖Itail‖ * ‖Kinf‖ * ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
        ‖groundSpaceGram A (K + L + Q) - Kinf‖ * Real.sqrt ‖Ifull‖ := by
  dsimp only
  let Ptail := (reassocTailBoundaryMapES A K L Q).comp
    (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
      ((physicalReassocES (d := d) K L Q).injective.comp
        (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
          A K (L + Q) hLocalTail)))
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let J := tailVirtualMapES A K
  let Iinf := Ring.inverse Kinf
  let Efull := Kinf - groundSpaceGram A (K + L + Q)
  let Pfull := (ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + L + Q)) hFull).comp
      (groundSpaceMapES A (K + L + Q)).adjoint
  simp only [wholeIncrementFullInverseGramCorrectionES]
  rw [← inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    A K L Q hLocalTail]
  rw [inverseGram_sub_limitingInverse_eq_resolvent
    A (K + L + Q) ρ hρ hFull]
  change ‖Ptail.comp (Ktail.comp (J.comp (Iinf.comp
    (Efull.comp Pfull))))‖ ≤ _
  calc
    _ ≤ ‖Ptail‖ * ‖Ktail.comp (J.comp (Iinf.comp
          (Efull.comp Pfull)))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * ‖J.comp (Iinf.comp
          (Efull.comp Pfull))‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * ‖Iinf.comp
          (Efull.comp Pfull)‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * (‖Iinf‖ *
          ‖Efull.comp Pfull‖))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖J‖ * (‖Iinf‖ *
          (‖Efull‖ * ‖Pfull‖)))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖Ktail‖ * ‖J‖ * ‖Iinf‖ * ‖Efull‖ * ‖Pfull‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ * ‖Kinf‖ *
        ‖tailVirtualMapES A K‖ * ‖Ring.inverse Kinf‖ *
        ‖groundSpaceGram A (K + L + Q) - Kinf‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L + Q)) hFull‖ := by
      dsimp only [Ptail, Ktail, J, Iinf, Efull, Pfull]
      rw [norm_sub_rev, ContinuousLinearMap.norm_inverseGram_comp_adjoint_eq_sqrt]
      gcongr
      · exact norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
          A K L Q hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
    _ = _ := by ring

/-- Raw operator-norm bound for the arbitrary-suffix left finite-Gram correction. -/
theorem wholeIncrementLeftFiniteGramCorrectionES_norm_le [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Iinf := Ring.inverse Kinf
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (L + Q)) hLocalTail
    let Ileft := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L)) hLocalLeft
    ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
      hLocalTail hLocalLeft‖ ≤
      Real.sqrt ‖Itail‖ * ‖Kinf‖ * ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
        ‖leftVirtualMapES A Q‖ * ‖groundSpaceGram A (K + L) - Kinf‖ *
          Real.sqrt ‖Ileft‖ := by
  dsimp only
  let Ptail := (reassocTailBoundaryMapES A K L Q).comp
    (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
      ((physicalReassocES (d := d) K L Q).injective.comp
        (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
          A K (L + Q) hLocalTail)))
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Ktail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Jtail := tailVirtualMapES A K
  let Iinf := Ring.inverse Kinf
  let JleftAdj := (leftVirtualMapES A Q).adjoint
  let Eleft := boundaryFiberwiseMap (D := D) (Cfg d Q)
    (groundSpaceGram A (K + L) - Kinf)
  let Pleft := (ContinuousLinearMap.inverseGram
    (leftBoundaryMapES A (K + L) Q)
      (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
        A (K + L) Q hLocalLeft)).comp
          (leftBoundaryMapES A (K + L) Q).adjoint
  simp only [wholeIncrementLeftFiniteGramCorrectionES]
  rw [← inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    A K L Q hLocalTail]
  change ‖Ptail.comp (Ktail.comp (Jtail.comp (Iinf.comp
    (JleftAdj.comp (Eleft.comp Pleft)))))‖ ≤ _
  calc
    _ ≤ ‖Ptail‖ * ‖Ktail.comp (Jtail.comp (Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft))))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * ‖Jtail.comp (Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft)))‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * ‖Iinf.comp
          (JleftAdj.comp (Eleft.comp Pleft))‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          ‖JleftAdj.comp (Eleft.comp Pleft)‖))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          (‖JleftAdj‖ * ‖Eleft.comp Pleft‖)))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖Ktail‖ * (‖Jtail‖ * (‖Iinf‖ *
          (‖JleftAdj‖ * (‖Eleft‖ * ‖Pleft‖))))) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Ptail‖ * ‖Ktail‖ * ‖Jtail‖ * ‖Iinf‖ * ‖JleftAdj‖ *
        ‖Eleft‖ * ‖Pleft‖ := by ring
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ * ‖Kinf‖ *
        ‖tailVirtualMapES A K‖ * ‖Ring.inverse Kinf‖ *
        ‖leftVirtualMapES A Q‖ * ‖groundSpaceGram A (K + L) - Kinf‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L)) hLocalLeft‖ := by
      dsimp only [Ptail, Ktail, Jtail, Iinf, JleftAdj, Eleft, Pleft]
      rw [LinearIsometryEquiv.norm_map
        (ContinuousLinearMap.adjoint (𝕜 := ℂ))]
      gcongr
      · exact norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
          A K L Q hLocalTail
      · exact norm_boundaryFiberwiseMap_le _ _
      · exact norm_boundaryFiberwiseMap_le _ _
      · exact norm_inverseGram_comp_leftBoundaryMapES_adjoint_le_sqrt
          A (K + L) Q hLocalLeft
    _ = _ := by ring


end MPSTensor
