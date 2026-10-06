/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ThreeOperatorPerturbation
import TNLean.MPS.ParentHamiltonian.ResidualWindowOverlapFactors
import TNLean.MPS.ParentHamiltonian.ResidualWindowVirtualNorm
import TNLean.MPS.ParentHamiltonian.GramInverseConvergence

/-!
# Decay of the residual mixed Gram

For a primitive blocked tensor, the common-prefix Gram converges to its
faithful fixed-point metric. The correlated tail has an exact row support.
The supported full-boundary inverse converges uniformly over all tails, and
the virtual prefix map has a bound independent of its length. Telescoping
these three factors shows that the finite mixed residual tends to zero as
the common blocked interval grows, even when both exterior lengths vary.

This is the same-sector mixed-Gram step in Nachtergaele,
arXiv:cond-mat/9410110, commutation (ii), equation (3.15), lines 1567--1574,
and the boundary-word estimate `A_m`, `boundAm`, lines 2394--2409.
The statement retains explicit algebraic row-support data and proves only
the residual limit. Its derivation from periodic-sector data and the physical
projection comparison are separate steps.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor
variable {d D E L : ℕ}
/-- The finite mixed residual from the two window Grams and the supported
full-boundary inverse. Source: Nachtergaele, arXiv:cond-mat/9410110,
commutation (ii), equation (3.15), lines 1567--1574; the boundary-word
estimate is `A_m` and `boundAm`, lines 2394--2409. -/
noncomputable def residualWindowMixedGramResidualES
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (K M r : ℕ) :
    BoundaryFamilySpace (D := E) (Cfg d r) →L[ℂ]
      EuclideanSpace ℂ (Cfg (blockPhysDim d L) K × (Fin E × Fin D)) :=
  let T := residualWindowRightMapES A B V K M r
  let F := residualWindowLeftMapES B K M r
  T.adjoint.comp F - (T.adjoint.comp T).comp
    ((residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B K).comp
      ((residualBoundaryGramInverse A B V ρ Q (K + M) r).comp
        ((correlatedTailMapES A V r).adjoint.comp (F.adjoint.comp F))))
/-- A growing common primitive prefix makes the mixed Gram residual vanish,
with arbitrary exterior lengths. The exact tail Gram projection determines
the supported corner; no invertibility outside that corner is assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, commutation (ii),
equation (3.15), lines 1567--1574; `A_m` and `boundAm`, lines 2394--2409. -/
theorem IsPrimitiveMPS.residualWindowMixedGramResidual_tendsto_zero
    [NeZero D] [NeZero E]
    {B : MPSTensor (blockPhysDim d L) E} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : IsPrimitiveMPS B ρ) (hρ : ρ.PosDef)
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r : ℕ, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q r)
    {ι : Type*} {l : Filter ι} {K M r : ι → ℕ} (hM : Filter.Tendsto M l Filter.atTop) :
    Filter.Tendsto (fun i =>
      ‖(residualWindowMixedGramResidualES A B V ρ (Q (r i)) (K i) (M i) (r i) :
        BoundaryFamilySpace (D := E) (Cfg d (r i)) →L[ℂ]
          EuclideanSpace ℂ (Cfg (blockPhysDim d L) (K i) × (Fin E × Fin D)))‖)
      l (nhds 0) := by
  have hKM : Filter.Tendsto (fun i => K i + M i) l Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_add_left (M i) (K i)) hM
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hconv : Filter.Tendsto (fun n => groundSpaceGram B n) Filter.atTop (nhds Kinf) :=
    hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  let GT i := (residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
    (residualWindowRightMapES A B V (K i) (M i) (r i))
  let KT i := EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) (K i))
    (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) (r i))
  let GLeft i := boundaryFiberwiseMap (Cfg d (r i)) (groundSpaceGram B (K i + M i))
  let KL i := boundaryFiberwiseMap (Cfg d (r i)) Kinf
  let J i := residualWindowRightVirtualMapES (d := d) (L := L) (D := D) B (K i)
  let C i := correlatedTailMapES A V (r i)
  let H i := residualBoundaryGramInverse A B V ρ (Q (r i)) (K i + M i) (r i)
  let I i := (rectangularRowProjection E (Q (r i))).comp
    (Ring.inverse (rectangularRightGramMetric D ρ))
  have hC : ∀ i, ‖C i‖ ≤ 1 := fun i =>
    norm_correlatedTailMapES_le_one_of_wordGram_eq_projection A V (r i)
      (Q (r i)) (hQ (r i)) (hGram (r i))
  have hJ : ∀ i, ‖J i‖ ≤ Real.sqrt E := fun i =>
    norm_residualWindowRightVirtualMapES_le_sqrt (d := d) (L := L) (D := D) B hP.norm (K i)
  have hδ := tendsto_iff_norm_sub_tendsto_zero.mp hconv
  have hδM := hδ.comp hM
  have hδKM := hδ.comp hKM
  have hGT : Filter.Tendsto (fun i => ‖GT i - KT i‖) l (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      (Filter.Eventually.of_forall fun i => ?_) hδM
    exact norm_residualWindowRightMapES_gram_sub_limit_le A B V ρ
      (ne_of_gt hρ.trace_pos) (K i) (M i) (r i) (hC i)
  have hGLeft : Filter.Tendsto (fun i => ‖GLeft i - KL i‖) l (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      (Filter.Eventually.of_forall fun i => ?_) hδKM
    change ‖EuclideanSpace.fiberwiseMap (Cfg d (r i)) (groundSpaceGram B (K i + M i)) -
      EuclideanSpace.fiberwiseMap (Cfg d (r i)) Kinf‖ ≤ _
    rw [← EuclideanSpace.fiberwiseMap_sub]
    exact EuclideanSpace.norm_fiberwiseMap_le _ _
  have hH : Filter.Tendsto (fun i => ‖H i - I i‖) l (nhds 0) :=
    hP.residualBoundaryGramInverse_sub_limit_tendsto_zero hρ A V Q hQ hGram hKM
  have hKT : ∀ i, ‖KT i‖ ≤ ‖Kinf‖ := by
    intro i
    refine (EuclideanSpace.norm_fiberwiseMap_le _ _).trans ?_
    change ‖(C i).adjoint.comp ((KL i).comp (C i))‖ ≤ _
    calc
      _ ≤ ‖(C i).adjoint‖ * (‖KL i‖ * ‖C i‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖Kinf‖ * 1) := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr
        · exact hC i
        · exact norm_boundaryFiberwiseMap_le _ _
        · exact hC i
      _ = _ := by ring
  let u := ‖Ring.inverse (rectangularRightGramMetric D ρ)‖
  have hI : ∀ i, ‖I i‖ ≤ u := by
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right
        (IsStarProjection.norm_le _ (rectangularRowProjection_isStarProjection (hQ (r i))))
        (norm_nonneg _)).trans_eq (one_mul _))
  have hAerr : Filter.Tendsto (fun i => ‖(GT i).comp (J i) - (KT i).comp (J i)‖)
      l (nhds 0) := by
    have hUpper : Filter.Tendsto (fun i => ‖GT i - KT i‖ * Real.sqrt E) l (nhds 0) := by
      simpa only [zero_mul] using hGT.mul_const (Real.sqrt E)
    refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      (Filter.Eventually.of_forall fun i => ?_) hUpper
    rw [← ContinuousLinearMap.sub_comp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hJ i) (norm_nonneg _))
  have hCerr : Filter.Tendsto (fun i =>
      ‖(C i).adjoint.comp (GLeft i) - (C i).adjoint.comp (KL i)‖) l (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      (Filter.Eventually.of_forall fun i => ?_) hGLeft
    rw [← ContinuousLinearMap.comp_sub]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)).trans_eq (one_mul _)
  have hHbound : ∀ᶠ i in l, ‖H i‖ ≤ 2 * u := by
    filter_upwards [hKM.eventually
      (hP.eventually_residualBoundaryGramInverse_properties hρ A V Q hQ hGram)] with i hi
    exact (hi (r i)).2.2.2.2.1
  have hGLeftBound : ∀ᶠ i in l, ‖GLeft i‖ ≤ ‖Kinf‖ + 1 := by
    filter_upwards [(tendsto_order.1 hδKM).2 1 (by norm_num)] with i hi
    refine (norm_boundaryFiberwiseMap_le _ _).trans ?_
    exact (norm_le_norm_sub_add (groundSpaceGram B (K i + M i)) Kinf).trans
      (by dsimp only [Function.comp_def] at hi; linarith)
  have haBound : ∀ i, ‖(KT i).comp (J i)‖ ≤ ‖Kinf‖ * Real.sqrt E := by
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hKT i) (hJ i) (norm_nonneg _) (norm_nonneg _))
  have hCBound : ∀ᶠ i in l, ‖(C i).adjoint.comp (GLeft i)‖ ≤ ‖Kinf‖ + 1 := by
    filter_upwards [hGLeftBound] with i hi
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (mul_le_mul (hC i) hi (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  let p := (2 * u + ‖Kinf‖ * Real.sqrt E) * (‖Kinf‖ + 1 + u)
  have hBound : ∀ᶠ i in l,
      ‖H i‖ * ‖(C i).adjoint.comp (GLeft i)‖ ≤ p ∧
      ‖(KT i).comp (J i)‖ * ‖(C i).adjoint.comp (GLeft i)‖ ≤ p ∧
      ‖(KT i).comp (J i)‖ * ‖I i‖ ≤ p := by
    filter_upwards [hHbound, hCBound] with i hiH hiC
    have hu : 0 ≤ u := norm_nonneg _
    have hg := norm_nonneg Kinf
    have hj := Real.sqrt_nonneg (E : ℝ)
    refine ⟨(mul_le_mul hiH hiC (norm_nonneg _) (by positivity)).trans ?_,
      (mul_le_mul (haBound i) hiC (norm_nonneg _) (by positivity)).trans ?_,
      (mul_le_mul (haBound i) (hI i) (norm_nonneg _) (by positivity)).trans ?_⟩
    all_goals
      apply le_of_sub_nonneg
      dsimp only [p]
      ring_nf
      positivity
  have hProd := ContinuousLinearMap.tendsto_norm_comp_three_sub_zero_of_bounds
    (fun i => (GT i).comp (J i)) (fun i => (KT i).comp (J i)) H I
    (fun i => (C i).adjoint.comp (GLeft i)) (fun i => (C i).adjoint.comp (KL i))
    hBound hAerr hH hCerr
  let Pfin i := (GT i).comp ((J i).comp ((H i).comp ((C i).adjoint.comp (GLeft i))))
  let Plim i := (KT i).comp ((J i).comp ((I i).comp ((C i).adjoint.comp (KL i))))
  have hPerr : Filter.Tendsto (fun i => ‖Pfin i - Plim i‖) l (nhds 0) := by
    simpa only [Pfin, Plim, ContinuousLinearMap.comp_assoc] using hProd
  let Z i := (residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
    (residualWindowLeftMapES B (K i) (M i) (r i)) - Plim i
  have hZ : Filter.Tendsto (fun i => ‖Z i‖) l (nhds 0) := by
    have hUpper : Filter.Tendsto (fun i => Real.sqrt E * ‖groundSpaceGram B (M i) - Kinf‖)
        l (nhds 0) := by
      simpa only [mul_zero, Function.comp_def] using hδM.const_mul (Real.sqrt E)
    refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      (Filter.Eventually.of_forall fun i => ?_) hUpper
    refine (norm_residualWindow_centeredMixedGram_le A B V ρ hρ
      (Q (r i)) (hQ (r i)) (K i) (M i) (r i) (hGram (r i))).trans ?_
    calc
      _ ≤ 1 * Real.sqrt E * ‖groundSpaceGram B (M i) - Kinf‖ := by
        gcongr
        · exact hC i
        · exact norm_residualWindowRightVirtualMapES_le_sqrt
            (d := d) (L := L) (D := E) B hP.norm (K i)
      _ = _ := by ring
  have hUpper : Filter.Tendsto (fun i => ‖Z i‖ + ‖Pfin i - Plim i‖) l (nhds 0) := by
    simpa only [add_zero] using hZ.add hPerr
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
    (Filter.Eventually.of_forall fun i => ?_) hUpper
  change ‖(residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
    (residualWindowLeftMapES B (K i) (M i) (r i)) -
    (GT i).comp ((J i).comp ((H i).comp ((C i).adjoint.comp
      ((residualWindowLeftMapES B (K i) (M i) (r i)).adjoint.comp
        (residualWindowLeftMapES B (K i) (M i) (r i))))))‖ ≤ _
  rw [residualWindowLeftMapES_adjoint_comp_self]
  change ‖(residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
    (residualWindowLeftMapES B (K i) (M i) (r i)) - Pfin i‖ ≤
    ‖(residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
      (residualWindowLeftMapES B (K i) (M i) (r i)) - Plim i‖ + ‖Pfin i - Plim i‖
  have hTriangle := norm_sub_le_norm_sub_add_norm_sub
    ((residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
      (residualWindowLeftMapES B (K i) (M i) (r i))) (Plim i) (Pfin i)
  rw [norm_sub_rev (Plim i) (Pfin i)] at hTriangle
  exact hTriangle

end MPSTensor
