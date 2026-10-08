/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowCancellation

/-!
# Direct-sum factors of residual mixed-Gram errors

The two overlap factors have fibers \(V^*A^\tau X_u\) and \(Y_\tau B^u\).
Their norms are controlled by the correlated tail map and the virtual
prefix map, respectively. The centered mixed Gram is their pairing
through the common-prefix Gram defect. Neither estimate grows with the
number of spectator fibers.

These finite-dimensional identities supply the mixed-error estimate in
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. No normalization or injectivity is assumed; obtaining
uniform numerical constants uses separate bounds for the virtual maps.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor
variable {d D E L : ℕ}
/-- Correlated tail fibers indexed also by the exterior blocked prefix.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. -/
noncomputable def residualWindowLeftOverlapFactorES
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)) →L[ℂ]
      BoundaryFamilySpace (D := E) (Cfg (blockPhysDim d L) K × Cfg d r) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodAssoc (Cfg (blockPhysDim d L) K) (Cfg d r)
      (Fin E × Fin E)).symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K) (correlatedTailMapES A V r))
/-- Prefix-word multiplication indexed also by the original tail.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. -/
noncomputable def residualWindowRightOverlapFactorES
    (B : MPSTensor (blockPhysDim d L) E) (K r : ℕ) :
    BoundaryFamilySpace (D := E) (Cfg d r) →L[ℂ]
      BoundaryFamilySpace (D := E) (Cfg (blockPhysDim d L) K × Cfg d r) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodAssoc (Cfg d r) (Cfg (blockPhysDim d L) K) (Fin E × Fin E)).symm.trans
      (Equiv.prodCongr (Equiv.prodComm (Cfg d r) (Cfg (blockPhysDim d L) K))
        (Equiv.refl (Fin E × Fin E))))).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (EuclideanSpace.fiberwiseMap (Cfg d r) (residualWindowRightVirtualMapES (D := E) B K))
/-- The left overlap factor has matrix fibers given by the correlated tail. -/
theorem boundaryFamilyEquiv_residualWindowLeftOverlapFactorES_apply
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ)
    (x : EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)))
    (u : Cfg (blockPhysDim d L) K) (τ : Cfg d r) :
    boundaryFamilyEquiv (Cfg (blockPhysDim d L) K × Cfg d r)
      (residualWindowLeftOverlapFactorES A V K r x) (u, τ) =
        Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x := by
  ext i j
  rfl
/-- The right overlap factor has matrix fibers given by prefix-word multiplication. -/
theorem boundaryFamilyEquiv_residualWindowRightOverlapFactorES_apply
    (B : MPSTensor (blockPhysDim d L) E) (K r : ℕ)
    (y : BoundaryFamilySpace (D := E) (Cfg d r))
    (u : Cfg (blockPhysDim d L) K) (τ : Cfg d r) :
    boundaryFamilyEquiv (Cfg (blockPhysDim d L) K × Cfg d r)
      (residualWindowRightOverlapFactorES B K r y) (u, τ) =
        boundaryFamilyEquiv (Cfg d r) y τ * Kraus.evalWord B (List.ofFn u) := by
  ext i j
  rfl
/-- Isometric coordinate rearrangement and a finite direct sum preserve the
correlated-tail norm bound, uniformly in the exterior prefix. -/
theorem norm_residualWindowLeftOverlapFactorES_le
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ) :
    ‖residualWindowLeftOverlapFactorES (L := L) A V K r‖ ≤ ‖correlatedTailMapES A V r‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  change ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodAssoc (Cfg (blockPhysDim d L) K) (Cfg d r)
      (Fin E × Fin E)).symm)
        (EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
          (correlatedTailMapES A V r) x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (EuclideanSpace.norm_fiberwiseMap_le _ _) (norm_nonneg x))
/-- Isometric coordinate rearrangement and a finite direct sum preserve the
prefix-word norm bound, uniformly in the original tail. -/
theorem norm_residualWindowRightOverlapFactorES_le
    (B : MPSTensor (blockPhysDim d L) E) (K r : ℕ) :
    ‖residualWindowRightOverlapFactorES B K r‖ ≤
      ‖residualWindowRightVirtualMapES (D := E) B K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  change ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodAssoc (Cfg d r) (Cfg (blockPhysDim d L) K) (Fin E × Fin E)).symm.trans
      (Equiv.prodCongr (Equiv.prodComm (Cfg d r) (Cfg (blockPhysDim d L) K))
        (Equiv.refl (Fin E × Fin E)))))
      (EuclideanSpace.fiberwiseMap (Cfg d r)
        (residualWindowRightVirtualMapES (D := E) B K) x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (EuclideanSpace.norm_fiberwiseMap_le _ _) (norm_nonneg x))
/-- The centered mixed Gram factors through the common-prefix Gram defect.
This is the direct-sum form of Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. -/
theorem residualWindow_centeredMixedGram_eq_overlapFactors [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ) (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Cfg d r) Kinf
    let Iinf := (rectangularRowProjection E Q).comp (Ring.inverse (rectangularRightGramMetric D ρ))
    (((residualWindowRightMapES A B V K M r).adjoint.comp
      (residualWindowLeftMapES B K M r) -
      Ktail.comp ((residualWindowRightVirtualMapES (D := D) B K).comp
        (Iinf.comp ((correlatedTailMapES A V r).adjoint.comp Kleft))))) =
      (residualWindowLeftOverlapFactorES A V K r).adjoint.comp
        ((boundaryFiberwiseMap (Cfg (blockPhysDim d L) K × Cfg d r)
          (groundSpaceGram B M - Kinf)).comp
            (residualWindowRightOverlapFactorES B K r)) := by
  dsimp only
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [inner_residualWindow_centeredMixedGram_eq_gramError A B V ρ hρ Q hQ K M r hGram]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, inner_boundaryFiberwiseMap]
  simp only [Fintype.sum_prod_type, boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyEquiv_residualWindowLeftOverlapFactorES_apply,
    boundaryFamilyEquiv_residualWindowRightOverlapFactorES_apply]
/-- The common-prefix Gram defect controls the centered mixed Gram, with
constants given only by the tail and prefix virtual maps.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. -/
theorem norm_residualWindow_centeredMixedGram_le [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ) (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Cfg d r) Kinf
    let Iinf := (rectangularRowProjection E Q).comp (Ring.inverse (rectangularRightGramMetric D ρ))
    ‖(((residualWindowRightMapES A B V K M r).adjoint.comp
      (residualWindowLeftMapES B K M r) -
      Ktail.comp ((residualWindowRightVirtualMapES (D := D) B K).comp
        (Iinf.comp ((correlatedTailMapES A V r).adjoint.comp Kleft)))))‖ ≤
      ‖correlatedTailMapES A V r‖ * ‖residualWindowRightVirtualMapES (D := E) B K‖ *
        ‖groundSpaceGram B M - Kinf‖ := by
  dsimp only
  rw [residualWindow_centeredMixedGram_eq_overlapFactors A B V ρ hρ Q hQ K M r hGram]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖correlatedTailMapES A V r‖ *
        (‖groundSpaceGram B M - Matrix.gramReshuffle
          (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ *
          ‖residualWindowRightVirtualMapES (D := E) B K‖) := by
      gcongr
      · exact norm_residualWindowLeftOverlapFactorES_le A V K r
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (norm_boundaryFiberwiseMap_le _ _)
            (norm_residualWindowRightOverlapFactorES_le B K r)
            (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring
end MPSTensor
