/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowCancellation

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
variable {α : Type*} [Fintype α] [DecidableEq α] {D E L : ℕ}
/-- Correlated tail fibers indexed also by the exterior blocked prefix.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. -/
noncomputable def residualWindowLeftOverlapFactorES
    (A : MPTensor α (Fin D)) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ) :
    EuclideanSpace ℂ ((Fin E × Fin D) × (Fin K → Fin L → α)) →L[ℂ]
      BoundaryFamilySpace (D := E) ((Fin K → Fin L → α) × (Fin r → α)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodComm ((Fin r → α) × (Fin E × Fin E)) ((Fin K → Fin L → α))).trans
      (Equiv.prodAssoc ((Fin K → Fin L → α)) (Fin r → α)
        (Fin E × Fin E)).symm)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
        (correlatedTailMapES A V r))
/-- Prefix-word multiplication indexed also by the original tail.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. -/
noncomputable def residualWindowRightOverlapFactorES
    (B : MPTensor (Fin L → α) (Fin E)) (K r : ℕ) :
    BoundaryFamilySpace (D := E) (Fin r → α) →L[ℂ]
      BoundaryFamilySpace (D := E) ((Fin K → Fin L → α) × (Fin r → α)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodAssoc (Fin E × Fin E) ((Fin K → Fin L → α)) (Fin r → α)).trans
      (Equiv.prodComm (Fin E × Fin E)
        ((Fin K → Fin L → α) × (Fin r → α))))).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.rightFiberwiseMap (S := (Fin r → α))
      (residualWindowRightVirtualMapES (D := E) B K)).comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodComm (Fin r → α) (Fin E × Fin E))).toContinuousLinearMap)
/-- The left overlap factor has matrix fibers given by the correlated tail. -/
theorem boundaryFamilyEquiv_residualWindowLeftOverlapFactorES_apply
    (A : MPTensor α (Fin D)) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ)
    (x : EuclideanSpace ℂ ((Fin E × Fin D) × (Fin K → Fin L → α)))
    (u : (Fin K → Fin L → α)) (τ : Fin r → α) :
    boundaryFamilyEquiv ((Fin K → Fin L → α) × (Fin r → α))
      (residualWindowLeftOverlapFactorES A V K r x) (u, τ) =
        Vᴴ * Kraus.evalWord A (List.ofFn τ) * rectangularBoundaryFamilyFiberₗ u x := by
  ext i j
  rfl
/-- The right overlap factor has matrix fibers given by prefix-word multiplication. -/
theorem boundaryFamilyEquiv_residualWindowRightOverlapFactorES_apply
    (B : MPTensor (Fin L → α) (Fin E)) (K r : ℕ)
    (y : BoundaryFamilySpace (D := E) (Fin r → α))
    (u : (Fin K → Fin L → α)) (τ : Fin r → α) :
    boundaryFamilyEquiv ((Fin K → Fin L → α) × (Fin r → α))
      (residualWindowRightOverlapFactorES B K r y) (u, τ) =
        boundaryFamilyEquiv (Fin r → α) y τ * Kraus.evalWord B (List.ofFn u) := by
  ext i j
  rfl
/-- Isometric coordinate rearrangement and a finite direct sum preserve the
correlated-tail norm bound, uniformly in the exterior prefix. -/
theorem norm_residualWindowLeftOverlapFactorES_le
    (A : MPTensor α (Fin D)) (V : Matrix (Fin D) (Fin E) ℂ) (K r : ℕ) :
    ‖residualWindowLeftOverlapFactorES (L := L) A V K r‖ ≤ ‖correlatedTailMapES A V r‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  change ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodComm ((Fin r → α) × (Fin E × Fin E)) ((Fin K → Fin L → α))).trans
      (Equiv.prodAssoc ((Fin K → Fin L → α)) (Fin r → α)
        (Fin E × Fin E)).symm))
        (ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
          (correlatedTailMapES A V r) x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_rightFiberwiseMap_le _)
      (norm_nonneg x))
/-- Isometric coordinate rearrangement and a finite direct sum preserve the
prefix-word norm bound, uniformly in the original tail. -/
theorem norm_residualWindowRightOverlapFactorES_le
    (B : MPTensor (Fin L → α) (Fin E)) (K r : ℕ) :
    ‖residualWindowRightOverlapFactorES B K r‖ ≤
      ‖residualWindowRightVirtualMapES (D := E) B K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodComm (Fin r → α) (Fin E × Fin E))
  change ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodAssoc (Fin E × Fin E) ((Fin K → Fin L → α)) (Fin r → α)).trans
      (Equiv.prodComm (Fin E × Fin E) ((Fin K → Fin L → α) × (Fin r → α)))))
      (ContinuousLinearMap.rightFiberwiseMap (S := (Fin r → α))
        (residualWindowRightVirtualMapES (D := E) B K) (R x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, ← R.norm_map x]
  exact (ContinuousLinearMap.le_opNorm _ (R x)).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_rightFiberwiseMap_le _)
      (norm_nonneg (R x)))
/-- The centered mixed Gram factors through the common-prefix Gram defect.
This is the direct-sum form of Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. -/
theorem residualWindow_centeredMixedGram_eq_overlapFactors [NeZero E]
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ) (hGram : ∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Fin r → α) Kinf
    let Iinf := (rectangularRowProjection E Q).comp (Ring.inverse (rectangularRightGramMetric D ρ))
    (((residualWindowRightMapES A B V K M r).adjoint.comp
      (residualWindowLeftMapES B K M r) -
      Ktail.comp ((residualWindowRightVirtualMapES (D := D) B K).comp
        (Iinf.comp ((correlatedTailMapES A V r).adjoint.comp Kleft))))) =
      (residualWindowLeftOverlapFactorES A V K r).adjoint.comp
        ((boundaryFiberwiseMap ((Fin K → Fin L → α) × (Fin r → α))
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
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ) (hGram : ∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V * Vᴴ) * Kraus.evalWord A (List.ofFn τ) = Q) :
    let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    let Ktail := ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
      (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) r)
    let Kleft := boundaryFiberwiseMap (Fin r → α) Kinf
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
