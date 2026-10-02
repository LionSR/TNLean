/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowGram
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryGramInverse
import TNLean.Tactic.MatrixReciprocalSmul

/-!
# Limiting cancellation for residual window Grams

The correlated tail restricts rectangular boundaries to an exact row corner.
On this corner, the inverse right boundary metric cancels the limiting
mixed pairing. Subtracting this pairing leaves the Gram error of the common
blocked prefix, with no error involving the exterior lengths.

These are algebraic identities used in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531.
They do not yet assert convergence or a projector estimate, and require
neither injectivity nor a transfer fixed-point equation.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor
variable {d D E L : ℕ}
/-- The inverse right boundary metric cancels the limiting Gram after recombining
the correlated tail. This algebraic identity supplies the limiting cancellation
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii),
lines 2442--2531; no transfer normalization is needed. -/
theorem rectangularRightGramMetric_inverse_comp_correlatedTailMapES_adjoint [NeZero E]
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (ρ : Matrix (Fin E) (Fin E) ℂ) (hρ : ρ.PosDef) (r : ℕ) :
    (Ring.inverse (rectangularRightGramMetric D ρ)).comp
      ((correlatedTailMapES A V r).adjoint.comp
        (boundaryFiberwiseMap (Cfg d r)
          (Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))))) =
      (correlatedTailMapES A V r).adjoint := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp_rw [ContinuousLinearMap.comp_apply, correlatedTailMapES_adjoint_apply]
  rw [rectangularRightGramMetric_inverse_apply hρ]
  simp_rw [boundaryFamilyEquiv_boundaryFiberwiseMap_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simp (disch := exact ne_of_gt hρ.trace_pos) only [matrix_reciprocal_smul,
    Matrix.sum_mul, Finset.smul_sum, Matrix.mul_assoc,
    Ring.mul_inverse_cancel ρ hρ.isUnit, Matrix.mul_one]
/-- Exact limiting mixed pairing on the row support determined by the tail Gram.
This is the rectangular boundary cancellation in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531.
The supported inverse acts only on this derived corner. -/
theorem inner_residualWindow_limitingMixedGramIntertwining [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K r : ℕ) (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (y : BoundaryFamilySpace (D := E) (Cfg d r)) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Cfg d r) Kinf
    inner ℂ x (Ktail.comp ((residualWindowRightVirtualMapES (D := D) B K).comp
      (((rectangularRowProjection E Q).comp (Ring.inverse (rectangularRightGramMetric D ρ))).comp
        ((correlatedTailMapES A V r).adjoint.comp Kleft))) y) =
      ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
        inner ℂ (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
          (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x))
          (Kinf (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (boundaryFamilyEquiv (Cfg d r) y τ * Kraus.evalWord B (List.ofFn u)))) := by
  dsimp only
  have hCancel := congrArg (fun F => F y)
    (rectangularRightGramMetric_inverse_comp_correlatedTailMapES_adjoint A V ρ hρ r)
  simp only [ContinuousLinearMap.comp_apply] at hCancel ⊢
  rw [hCancel, EuclideanSpace.inner_fiberwiseMap]
  have hAdj : (rectangularRowProjection E Q).comp (correlatedTailMapES A V r).adjoint =
      (correlatedTailMapES A V r).adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint
      (correlatedTailMapES_comp_rowProjection A V r Q hQ hGram)
    simpa only [ContinuousLinearMap.adjoint_comp,
      (show (rectangularRowProjection E Q).adjoint = rectangularRowProjection E Q from
        (rectangularRowProjection_isStarProjection (E := E) hQ).isSelfAdjoint.star_eq)] using h
  have hQZ : Q * (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * V *
      boundaryFamilyEquiv (Cfg d r) y τ) =
      ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * V *
        boundaryFamilyEquiv (Cfg d r) y τ := by
    apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).injective
    simpa only [ContinuousLinearMap.comp_apply, correlatedTailMapES_adjoint_apply,
      rectangularRowProjection_apply] using congrArg (fun F => F y) hAdj
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [correlatedTailMapES_adjoint_apply, rectangularRowProjection_apply, hQZ]
  change inner ℂ (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
    (rectangularBoundaryFamilyFiberₗ u x))
    (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        ((∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * V *
          boundaryFamilyEquiv (Cfg d r) y τ) * Kraus.evalWord B (List.ofFn u)))) = _
  rw [residualBoundaryGramLimit_frobeniusEquivEuclidean_apply, hGram,
    ← Matrix.mul_assoc, hQZ]
  simp_rw [Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    Matrix.inner_frobeniusEquivEuclidean]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_smul, Finset.smul_sum,
    Matrix.trace_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
/-- Subtracting the limiting mixed pairing leaves precisely the common-prefix
Gram error. This finite identity is the algebraic step preceding the estimates
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii),
lines 2442--2531. -/
theorem inner_residualWindow_centeredMixedGram_eq_gramError [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ) (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (y : BoundaryFamilySpace (D := E) (Cfg d r)) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Cfg d r) Kinf
    let Iinf := (rectangularRowProjection E Q).comp (Ring.inverse (rectangularRightGramMetric D ρ))
    inner ℂ x (((residualWindowRightMapES A B V K M r).adjoint.comp
      (residualWindowLeftMapES B K M r) -
      Ktail.comp ((residualWindowRightVirtualMapES (D := D) B K).comp
        (Iinf.comp ((correlatedTailMapES A V r).adjoint.comp Kleft)))) y) =
      ∑ u : Cfg (blockPhysDim d L) K, ∑ τ : Cfg d r,
        inner ℂ (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
          (Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x))
          ((groundSpaceGram B M - Kinf) (Matrix.frobeniusEquivEuclidean (Fin E) (Fin E)
            (boundaryFamilyEquiv (Cfg d r) y τ * Kraus.evalWord B (List.ofFn u)))) := by
  dsimp only
  rw [sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_residualWindowRightMapES_leftMapES]
  rw [inner_residualWindow_limitingMixedGramIntertwining A B V ρ hρ Q hQ K r hGram]
  simp only [sub_apply, inner_sub_right, Finset.sum_sub_distrib]
end MPSTensor

