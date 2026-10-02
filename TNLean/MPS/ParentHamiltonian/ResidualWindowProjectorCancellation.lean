/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowMixedGramDecay
import TNLean.MPS.ParentHamiltonian.ResidualWindowRightSectorSum
import TNLean.Algebra.SupportedRangeProjectorNorm

/-!
# Supported cancellation for residual window projections

The two window boundary maps factor the full boundary map through a virtual
prefix and a correlated tail. Their Gram inverses act on the exact row support
of that tail. The resulting difference of range projections factors through
the finite mixed Gram residual.

This is the supported-boundary form of Nachtergaele,
arXiv:cond-mat/9410110, commutation (ii), equation (3.15), lines 1567--1574,
and the boundary-word estimate `A_m`, `boundAm`, lines 2394--2409.
The algebraic statement records the precise inverse identities required for
cancellation. Primitivity supplies them in the subsequent convergence result.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor

variable {d D E L : ℕ}

/-- The supported inverse identities give an exact factorization of the two
window projection product minus the full-window projection through the finite
mixed residual. Source: Nachtergaele, arXiv:cond-mat/9410110,
commutation (ii), equation (3.15), lines 1567--1574; `A_m`, `boundAm`,
lines 2394--2409. -/
theorem residualWindow_supported_projector_factorization
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ)
    (hGram : (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q)
    (hHM : IsSelfAdjoint (residualBoundaryGramInverse A B V ρ Q M r))
    (hGM : ((blockedResidualBoundaryMapES A L B V M r).adjoint.comp
      (blockedResidualBoundaryMapES A L B V M r)).comp
        (residualBoundaryGramInverse A B V ρ Q M r) = rectangularRowProjection E Q)
    (hGKM : ((blockedResidualBoundaryMapES A L B V (K + M) r).adjoint.comp
      (blockedResidualBoundaryMapES A L B V (K + M) r)).comp
        (residualBoundaryGramInverse A B V ρ Q (K + M) r) = rectangularRowProjection E Q)
    (hUnit : IsUnit (groundSpaceGram B (K + M))) :
    let T := residualWindowRightMapES A B V K M r
    let F := residualWindowLeftMapES B K M r
    let C := residualWindowMapES A B V K M r
    let HT := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramInverse A B V ρ Q M r)
    let HL := boundaryFiberwiseMap (Cfg d r) (Ring.inverse (groundSpaceGram B (K + M)))
    T.range.starProjection.comp F.range.starProjection - C.range.starProjection =
      T.comp (HT.comp ((residualWindowMixedGramResidualES A B V ρ Q K M r).comp
        (HL.comp F.adjoint))) := by
  dsimp only
  refine ContinuousLinearMap.starProjection_comp_sub_of_supportedGramFactorizations
    (residualWindowRightMapES A B V K M r) (residualWindowLeftMapES B K M r)
    (residualWindowMapES A B V K M r)
    (residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K)
    (correlatedTailMapES A V r)
    (EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramInverse A B V ρ Q M r))
    (EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K) (rectangularRowProjection E Q))
    (boundaryFiberwiseMap (Cfg d r) (Ring.inverse (groundSpaceGram B (K + M))))
    (ContinuousLinearMap.id ℂ (BoundaryFamilySpace (D := E) (Cfg d r)))
    (residualBoundaryGramInverse A B V ρ Q (K + M) r) (rectangularRowProjection E Q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [EuclideanSpace.fiberwiseMap_adjoint, ← ContinuousLinearMap.star_eq_adjoint, hHM.star_eq]
  · rw [EuclideanSpace.fiberwiseMap_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      (rectangularRowProjection_isStarProjection (E := E) hQ).isSelfAdjoint.star_eq]
  · rw [residualWindowRightMapES_eq_fiberwise, EuclideanSpace.fiberwiseMap_comp,
      ContinuousLinearMap.comp_assoc,
      blockedResidualBoundaryMapES_comp_rowProjection A B V M r Q hQ hGram]
  · rw [residualWindowRightMapES_adjoint_comp_self, EuclideanSpace.fiberwiseMap_comp, hGM]
  · exact ContinuousLinearMap.adjoint_id
  · exact ContinuousLinearMap.comp_id _
  · rw [residualWindowLeftMapES_adjoint_comp_self]
    change (EuclideanSpace.fiberwiseMap (Cfg d r) (groundSpaceGram B (K + M))).comp
      (EuclideanSpace.fiberwiseMap (Cfg d r) (Ring.inverse (groundSpaceGram B (K + M)))) = _
    rw [EuclideanSpace.fiberwiseMap_comp, ← ContinuousLinearMap.mul_def,
      Ring.mul_inverse_cancel _ hUnit, ContinuousLinearMap.one_def, EuclideanSpace.fiberwiseMap_id]
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (rectangularRowProjection_isStarProjection (E := E) hQ).isSelfAdjoint.star_eq
  · rw [residualWindowMapES_eq_reindex_blockedResidualBoundaryMapES,
      ContinuousLinearMap.comp_assoc,
      blockedResidualBoundaryMapES_comp_rowProjection A B V (K + M) r Q hQ hGram]
  · rw [residualWindowMapES_adjoint_comp_self, hGKM]
  · exact residualWindowRightMapES_comp_rightVirtualMapES A B V K M r
  · exact residualWindowLeftMapES_comp_correlatedTailMapES A B V K M r

/-- The supported window projection defect tends to zero as the common
primitive prefix grows, uniformly over arbitrary exterior lengths.
The row support and all inverse estimates are derived from the exact tail
Gram and the faithful invariant matrix. Source: Nachtergaele,
arXiv:cond-mat/9410110, commutation (ii), equation (3.15), lines 1567--1574;
`A_m`, `boundAm`, lines 2394--2409. -/
theorem IsPrimitiveMPS.residualWindow_projection_comp_sub_tendsto_zero
    [NeZero D] [NeZero E]
    {B : MPSTensor (blockPhysDim d L) E} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : IsPrimitiveMPS B ρ) (hρ : ρ.PosDef)
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r : ℕ, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q r)
    {ι : Type*} {l : Filter ι} {K M r : ι → ℕ} (hM : Filter.Tendsto M l Filter.atTop) :
    Filter.Tendsto (fun i =>
      ‖(residualWindowRightMapES A B V (K i) (M i) (r i)).range.starProjection.comp
        (residualWindowLeftMapES B (K i) (M i) (r i)).range.starProjection -
        (residualWindowMapES A B V (K i) (M i) (r i)).range.starProjection‖) l (nhds 0) := by
  have hKM : Filter.Tendsto (fun i => K i + M i) l Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_add_left (M i) (K i)) hM
  have hProp := hP.eventually_residualBoundaryGramInverse_properties hρ A V Q hQ hGram
  have hOrd := hP.eventually_groundSpaceGram_isUnit_and_inverse_bound hρ
    (a := 1 / 2) (by norm_num) (by norm_num)
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hSmall : ∀ᶠ i in l, ‖groundSpaceGram B (K i + M i) - Kinf‖ < 1 :=
    (tendsto_order.1 ((tendsto_iff_norm_sub_tendsto_zero.mp
      hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj).comp hKM)).2 1 (by norm_num)
  refine ContinuousLinearMap.tendsto_norm_starProjection_comp_sub_zero_of_supported_factorizations
    (fun i => residualWindowRightMapES A B V (K i) (M i) (r i))
    (fun i => residualWindowLeftMapES B (K i) (M i) (r i))
    (fun i => residualWindowMapES A B V (K i) (M i) (r i))
    (fun i => EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) (K i))
      (residualBoundaryGramInverse A B V ρ (Q (r i)) (M i) (r i)))
    (fun i => boundaryFiberwiseMap (Cfg d (r i))
      (Ring.inverse (groundSpaceGram B (K i + M i))))
    (fun i => residualWindowMixedGramResidualES A B V ρ (Q (r i)) (K i) (M i) (r i))
    (K := (‖rectangularRightGramMetric D ρ‖ + 2) *
      (2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖) *
      (2 * ‖Ring.inverse Kinf‖) * (‖Kinf‖ + 2)) ?_ ?_ ?_
  · filter_upwards [hM.eventually hProp, hKM.eventually hProp, hKM.eventually hOrd]
      with i hiM hiKM hiOrd
    exact residualWindow_supported_projector_factorization A B V ρ (Q (r i))
      (hQ (r i)) (K i) (M i) (r i) (hGram (r i))
      (hiM (r i)).2.1 (hiM (r i)).2.2.2.1 (hiKM (r i)).2.2.2.1 hiOrd.1
  · filter_upwards [hM.eventually hProp, hKM.eventually hOrd, hSmall]
      with i hiM hiOrd hiSmall
    have hT := (norm_residualWindowRightMapES_le A B V (K i) (M i) (r i)).trans
      (hiM (r i)).2.2.2.2.2
    have hHT := (EuclideanSpace.norm_fiberwiseMap_le (Cfg (blockPhysDim d L) (K i))
      (residualBoundaryGramInverse A B V ρ (Q (r i)) (M i) (r i))).trans
      (hiM (r i)).2.2.2.2.1
    have hInv : ‖Ring.inverse (groundSpaceGram B (K i + M i)) - Ring.inverse Kinf‖ ≤
        ‖Ring.inverse Kinf‖ := by
      simpa only [Kinf] using (show (1 - (1 / 2 : ℝ))⁻¹ * (1 / 2) *
        ‖Ring.inverse Kinf‖ = ‖Ring.inverse Kinf‖ by ring_nf) ▸ hiOrd.2
    have hHL : ‖boundaryFiberwiseMap (Cfg d (r i))
        (Ring.inverse (groundSpaceGram B (K i + M i)))‖ ≤ 2 * ‖Ring.inverse Kinf‖ :=
      (norm_boundaryFiberwiseMap_le _ _).trans ((norm_le_norm_sub_add
        (Ring.inverse (groundSpaceGram B (K i + M i))) (Ring.inverse Kinf)).trans
          (by linarith))
    have hFSq : ‖residualWindowLeftMapES (d := d) B (K i) (M i) (r i)‖ ^ 2 ≤
        ‖groundSpaceGram B (K i + M i)‖ := by
      rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self,
        residualWindowLeftMapES_adjoint_comp_self]
      exact norm_boundaryFiberwiseMap_le _ _
    have hF : ‖residualWindowLeftMapES (d := d) B (K i) (M i) (r i)‖ ≤ ‖Kinf‖ + 2 := by
      have hG := norm_le_norm_sub_add (groundSpaceGram B (K i + M i)) Kinf
      nlinarith [norm_nonneg Kinf,
        norm_nonneg (residualWindowLeftMapES (d := d) B (K i) (M i) (r i))]
    exact mul_le_mul (mul_le_mul (mul_le_mul hT hHT (norm_nonneg _)
      (by positivity)) hHL (norm_nonneg _) (by positivity)) hF
      (norm_nonneg _) (by positivity)
  · exact hP.residualWindowMixedGramResidual_tendsto_zero hρ A V Q hQ hGram hM

end MPSTensor
