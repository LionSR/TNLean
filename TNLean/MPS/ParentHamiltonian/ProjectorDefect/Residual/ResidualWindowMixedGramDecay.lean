/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowCoordinates
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Analysis.Norm.NormedRingTelescoping
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowOverlapFactors
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GramInverseConvergence
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowRightSectorSum
import QICLean.Analysis.Projection.SupportedRangeProjector

/-!
# A uniform bound for the virtual prefix map

Left-canonical normalization implies that the sum of the squared Frobenius
norms of all words of a fixed length equals the bond dimension. Consequently,
the virtual map which sends a rectangular boundary to its right products
with the prefix words has norm at most the square root of that dimension.
The bound is independent of the prefix length, including length zero.

This is the elementary boundary estimate used in the residual form of
Nachtergaele's overlapping-window argument, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. It requires neither primitivity
nor a fixed-point hypothesis.

## Decay of the residual mixed Gram

For a primitive blocked tensor, the common-prefix Gram converges to its
faithful fixed-point metric. The correlated tail has an exact row support.
The supported full-boundary inverse converges uniformly over all tails, and
the virtual prefix map has a bound independent of its length. Telescoping
these three factors shows that the finite mixed residual tends to zero as
the common blocked interval grows, even when both exterior lengths vary.

This is the same-sector mixed-Gram step in Nachtergaele,
arXiv:cond-mat/9410110, commutation (ii), equation (3.15), lines 1567--1574,
and the boundary-word estimate A_m, boundAm, lines 2394--2409.
The statement retains explicit algebraic row-support data and proves only
the residual limit. Its derivation from periodic-sector data and the physical
projection comparison are separate steps.

It also contains the following results.

* `MPSTensor.residualWindow_supported_projector_factorization`,
  `Kraus.HasComplementaryFixedPointGap.residualWindow_projection_comp_sub_tendsto_zero`: supported
  cancellation for residual window projections.
-/

section ResidualWindowMixedGramDecay

section

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace BigOperators
namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D E L : ℕ}

/-- Taking the trace of left-canonical word normalization gives the total
squared Frobenius norm at every word length. This includes zero bond
dimension and zero length. -/
theorem sum_evalWord_frobenius_norm_sq_of_leftCanonical
    (B : MPTensor α (Fin E)) (hLeft : ∑ i, (B i)ᴴ * B i = 1) (K : ℕ) :
    (∑ u : (Fin K → α), ‖Kraus.evalWord B (List.ofFn u)‖ ^ 2) = (E : ℝ) := by
  have h := congrArg (fun X : Matrix (Fin E) (Fin E) ℂ => (Matrix.trace X).re)
    (Kraus.sum_evalWord_conjTranspose_mul_evalWord B hLeft K)
  simpa only [Matrix.trace_sum, Complex.re_sum,
    Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    Matrix.trace_one, Fintype.card_fin, Complex.natCast_re] using h

/-- The right virtual prefix map has a bound independent of the prefix length.
Source: the boundary-word factorization in Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem norm_residualWindowRightVirtualMapES_le_sqrt
    (B : MPTensor (Fin L → α) (Fin E)) (hLeft : ∑ i, (B i)ᴴ * B i = 1) (K : ℕ) :
    ‖residualWindowRightVirtualMapES (L := L) (D := D) B K‖ ≤ Real.sqrt E := by
  refine (residualWindowRightVirtualMapES (L := L) (D := D) B K).opNorm_le_bound
    (Real.sqrt_nonneg _) ?_
  intro x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  have hnorm : ‖residualWindowRightVirtualMapES (L := L) (D := D) B K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)‖ ^ 2 =
      ∑ u : (Fin K → Fin L → α), ‖Y * Kraus.evalWord B (List.ofFn u)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
    change (∑ u : (Fin K → Fin L → α), ∑ p : Fin E × Fin D,
      ‖(Y * Kraus.evalWord B (List.ofFn u)) p.2 p.1‖ ^ 2) = _
    apply Finset.sum_congr rfl
    intro u _
    rw [← (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).norm_map
      (Y * Kraus.evalWord B (List.ofFn u)), EuclideanSpace.norm_sq_eq]
    rfl
  have hbound : ‖residualWindowRightVirtualMapES (L := L) (D := D) B K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)‖ ^ 2 ≤ (E : ℝ) * ‖Y‖ ^ 2 := by
    rw [hnorm]
    calc
      (∑ u : (Fin K → Fin L → α), ‖Y * Kraus.evalWord B (List.ofFn u)‖ ^ 2) ≤
          ∑ u : (Fin K → Fin L → α), (‖Y‖ * ‖Kraus.evalWord B (List.ofFn u)‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (Matrix.frobenius_norm_mul Y (Kraus.evalWord B (List.ofFn u))) 2
      _ = ‖Y‖ ^ 2 * ∑ u : (Fin K → Fin L → α),
          ‖Kraus.evalWord B (List.ofFn u)‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = (E : ℝ) * ‖Y‖ ^ 2 := by
        rw [sum_evalWord_frobenius_norm_sq_of_leftCanonical B hLeft K, mul_comm]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg E),
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).norm_map]
  exact hbound
end MPSTensor

end

section

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D E L : ℕ}
/-- The finite mixed residual from the two window Grams and the supported
full-boundary inverse. Source: Nachtergaele, arXiv:cond-mat/9410110,
commutation (ii), equation (3.15), lines 1567--1574; the boundary-word
estimate is A_m and boundAm, lines 2394--2409. -/
noncomputable def residualWindowMixedGramResidualES
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (K M r : ℕ) :
    BoundaryFamilySpace (D := E) (Fin r → α) →L[ℂ]
      EuclideanSpace ℂ ((Fin E × Fin D) × (Fin K → Fin L → α)) :=
  let T := residualWindowRightMapES A B V K M r
  let F := residualWindowLeftMapES B K M r
  T.adjoint.comp F - (T.adjoint.comp T).comp
    ((residualWindowRightVirtualMapES (L := L) (D := D) B K).comp
      ((residualBoundaryGramInverse A B V ρ Q (K + M) r).comp
        ((correlatedTailMapES A V r).adjoint.comp (F.adjoint.comp F))))
/-- A growing common primitive prefix makes the mixed Gram residual vanish,
with arbitrary exterior lengths. The exact tail Gram projection determines
the supported corner; no invertibility outside that corner is assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, commutation (ii),
equation (3.15), lines 1567--1574; A_m and boundAm, lines 2394--2409. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.residualWindowMixedGramResidual_tendsto_zero
    [NeZero D] [NeZero E]
    {B : MPTensor (Fin L → α) (Fin E)} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap B ρ) (hρ : ρ.PosDef)
    (A : MPTensor α (Fin D)) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r : ℕ, (∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q r)
    {ι : Type*} {l : Filter ι} {K M r : ι → ℕ} (hM : Filter.Tendsto M l Filter.atTop) :
    Filter.Tendsto (fun i =>
      ‖(residualWindowMixedGramResidualES A B V ρ (Q (r i)) (K i) (M i) (r i) :
        BoundaryFamilySpace (D := E) (Fin (r i) → α) →L[ℂ]
          EuclideanSpace ℂ ((Fin E × Fin D) × (Fin (K i) → Fin L → α)))‖)
      l (nhds 0) := by
  have hKM : Filter.Tendsto (fun i => K i + M i) l Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_add_left (M i) (K i)) hM
  let Kinf := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hconv : Filter.Tendsto (fun n => groundSpaceGram B n) Filter.atTop (nhds Kinf) :=
    hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  let GT i := (residualWindowRightMapES A B V (K i) (M i) (r i)).adjoint.comp
    (residualWindowRightMapES A B V (K i) (M i) (r i))
  let KT i := ContinuousLinearMap.rightFiberwiseMap (S := (Fin (K i) → Fin L → α))
    (residualBoundaryGramLimit A V ρ (ne_of_gt hρ.trace_pos) (r i))
  let GLeft i := boundaryFiberwiseMap (Fin (r i) → α) (groundSpaceGram B (K i + M i))
  let KL i := boundaryFiberwiseMap (Fin (r i) → α) Kinf
  let J i := residualWindowRightVirtualMapES (L := L) (D := D) B (K i)
  let C i := correlatedTailMapES A V (r i)
  let H i := residualBoundaryGramInverse A B V ρ (Q (r i)) (K i + M i) (r i)
  let I i := (rectangularRowProjection E (Q (r i))).comp
    (Ring.inverse (rectangularRightGramMetric D ρ))
  have hC : ∀ i, ‖C i‖ ≤ 1 := fun i =>
    norm_correlatedTailMapES_le_one_of_wordGram_eq_projection A V (r i)
      (Q (r i)) (hQ (r i)) (hGram (r i))
  have hJ : ∀ i, ‖J i‖ ≤ Real.sqrt E := fun i =>
    norm_residualWindowRightVirtualMapES_le_sqrt (L := L) (D := D) B hP.norm (K i)
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
    change ‖boundaryFiberwiseMap (Fin (r i) → α) (groundSpaceGram B (K i + M i)) -
      boundaryFiberwiseMap (Fin (r i) → α) Kinf‖ ≤ _
    rw [← boundaryFiberwiseMap_sub]
    exact norm_boundaryFiberwiseMap_le _ _
  have hH : Filter.Tendsto (fun i => ‖H i - I i‖) l (nhds 0) :=
    hP.residualBoundaryGramInverse_sub_limit_tendsto_zero hρ A V Q hQ hGram hKM
  have hKT : ∀ i, ‖KT i‖ ≤ ‖Kinf‖ := by
    intro i
    refine (ContinuousLinearMap.norm_rightFiberwiseMap_le _).trans ?_
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
            (L := L) (D := E) B hP.norm (K i)
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

end

end ResidualWindowMixedGramDecay

section ResidualWindowProjectorCancellation

/-!
## Supported cancellation for residual window projections

The two window boundary maps factor the full boundary map through a virtual
prefix and a correlated tail. Their Gram inverses act on the exact row support
of that tail. The resulting difference of range projections factors through
the finite mixed Gram residual.

This is the supported-boundary form of Nachtergaele,
arXiv:cond-mat/9410110, commutation (ii), equation (3.15), lines 1567--1574,
and the boundary-word estimate A_m, boundAm, lines 2394--2409.
The algebraic statement records the precise inverse identities required for
cancellation. Primitivity supplies them in the subsequent convergence result.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D E L : ℕ}

/-- The supported inverse identities give an exact factorization of the two
window projection product minus the full-window projection through the finite
mixed residual. Source: Nachtergaele, arXiv:cond-mat/9410110,
commutation (ii), equation (3.15), lines 1567--1574; A_m, boundAm,
lines 2394--2409. -/
theorem residualWindow_supported_projector_factorization
    (A : MPTensor α (Fin D)) (B : MPTensor (Fin L → α) (Fin E))
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (K M r : ℕ)
    (hGram : (∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ *
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
    let HT := ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
      (residualBoundaryGramInverse A B V ρ Q M r)
    let HL := boundaryFiberwiseMap (Fin r → α) (Ring.inverse (groundSpaceGram B (K + M)))
    T.range.starProjection.comp F.range.starProjection - C.range.starProjection =
      T.comp (HT.comp ((residualWindowMixedGramResidualES A B V ρ Q K M r).comp
        (HL.comp F.adjoint))) := by
  dsimp only
  refine ContinuousLinearMap.starProjection_comp_sub_of_supportedGramFactorizations
    (residualWindowRightMapES A B V K M r) (residualWindowLeftMapES B K M r)
    (residualWindowMapES A B V K M r)
    (residualWindowRightVirtualMapES (L := L) (D := D) B K)
    (correlatedTailMapES A V r)
    (ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
      (residualBoundaryGramInverse A B V ρ Q M r))
    (ContinuousLinearMap.rightFiberwiseMap (S := (Fin K → Fin L → α))
      (rectangularRowProjection E Q))
    (boundaryFiberwiseMap (Fin r → α) (Ring.inverse (groundSpaceGram B (K + M))))
    (ContinuousLinearMap.id ℂ (BoundaryFamilySpace (D := E) (Fin r → α)))
    (residualBoundaryGramInverse A B V ρ Q (K + M) r) (rectangularRowProjection E Q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [ContinuousLinearMap.rightFiberwiseMap_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hHM.star_eq]
  · rw [ContinuousLinearMap.rightFiberwiseMap_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      (rectangularRowProjection_isStarProjection (E := E) hQ).isSelfAdjoint.star_eq]
  · rw [residualWindowRightMapES_eq_fiberwise, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.rightFiberwiseMap_comp, ContinuousLinearMap.comp_assoc,
      blockedResidualBoundaryMapES_comp_rowProjection A B V M r Q hQ hGram]
  · rw [residualWindowRightMapES_adjoint_comp_self, ContinuousLinearMap.rightFiberwiseMap_comp,
      hGM]
  · exact ContinuousLinearMap.adjoint_id
  · exact ContinuousLinearMap.comp_id _
  · rw [residualWindowLeftMapES_adjoint_comp_self]
    rw [boundaryFiberwiseMap_comp, ← ContinuousLinearMap.mul_def,
      Ring.mul_inverse_cancel _ hUnit, ContinuousLinearMap.one_def, boundaryFiberwiseMap_id]
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
A_m, boundAm, lines 2394--2409. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.residualWindow_projection_comp_sub_tendsto_zero
    [NeZero D] [NeZero E]
    {B : MPTensor (Fin L → α) (Fin E)} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap B ρ) (hρ : ρ.PosDef)
    (A : MPTensor α (Fin D)) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r : ℕ, (∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
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
    (fun i => ContinuousLinearMap.rightFiberwiseMap (S := (Fin (K i) → Fin L → α))
      (residualBoundaryGramInverse A B V ρ (Q (r i)) (M i) (r i)))
    (fun i => boundaryFiberwiseMap (Fin (r i) → α)
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
    have hHT := (ContinuousLinearMap.norm_rightFiberwiseMap_le
      (S := (Fin (K i) → Fin L → α))
      (residualBoundaryGramInverse A B V ρ (Q (r i)) (M i) (r i))).trans
      (hiM (r i)).2.2.2.2.1
    have hInv : ‖Ring.inverse (groundSpaceGram B (K i + M i)) - Ring.inverse Kinf‖ ≤
        ‖Ring.inverse Kinf‖ := by
      simpa only [Kinf] using (show (1 - (1 / 2 : ℝ))⁻¹ * (1 / 2) *
        ‖Ring.inverse Kinf‖ = ‖Ring.inverse Kinf‖ by ring_nf) ▸ hiOrd.2
    have hHL : ‖boundaryFiberwiseMap (Fin (r i) → α)
        (Ring.inverse (groundSpaceGram B (K i + M i)))‖ ≤ 2 * ‖Ring.inverse Kinf‖ :=
      (norm_boundaryFiberwiseMap_le _ _).trans ((norm_le_norm_sub_add
        (Ring.inverse (groundSpaceGram B (K i + M i))) (Ring.inverse Kinf)).trans
          (by linarith))
    have hFSq : ‖residualWindowLeftMapES B (K i) (M i) (r i)‖ ^ 2 ≤
        ‖groundSpaceGram B (K i + M i)‖ := by
      rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self,
        residualWindowLeftMapES_adjoint_comp_self]
      exact norm_boundaryFiberwiseMap_le _ _
    have hF : ‖residualWindowLeftMapES B (K i) (M i) (r i)‖ ≤ ‖Kinf‖ + 2 := by
      have hG := norm_le_norm_sub_add (groundSpaceGram B (K i + M i)) Kinf
      nlinarith [norm_nonneg Kinf,
        norm_nonneg (residualWindowLeftMapES B (K i) (M i) (r i))]
    exact mul_le_mul (mul_le_mul (mul_le_mul hT hHT (norm_nonneg _)
      (by positivity)) hHL (norm_nonneg _) (by positivity)) hF
      (norm_nonneg _) (by positivity)
  · exact hP.residualWindowMixedGramResidual_tendsto_zero hρ A V Q hQ hGram hM

end MPSTensor

end ResidualWindowProjectorCancellation
