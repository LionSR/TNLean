/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryGram
import QICLean.Analysis.NeumannInverse
/-!
# Supported inverses of correlated residual Gram operators

On rectangular boundaries, let \(R_\rho Y=Y\rho/\operatorname{tr}\rho\)
and let \(\mathcal Q_rY=Q_rY\), where
\(Q_r=\sum_\tau A^{\tau\dagger}VV^\dagger A^\tau\) is an orthogonal projection.
The residual boundary map \(\Gamma_{N,r}\) vanishes outside this row corner.
Its limiting Gram operator is \(R_\rho\mathcal Q_r\).

For faithful \(\rho\), extend the residual Gram operator to the full
rectangular boundary space by
\(F_{N,r}=\Gamma_{N,r}^\dagger\Gamma_{N,r}+R_\rho(I-\mathcal Q_r)\).
The difference \(F_{N,r}-R_\rho\) is exactly the residual Gram error.
The fixed invertible metric \(R_\rho\) therefore gives Neumann inverse
bounds uniform in the tail length. The supported inverse
\(H_{N,r}=\mathcal Q_rF_{N,r}^{-1}\) is self-adjoint and satisfies
\(\Gamma_{N,r}^\dagger\Gamma_{N,r}H_{N,r}=\mathcal Q_r\).

For cyclic sectors the projection is \(Q_r=P_{a+r}\), as derived in
`ResidualBoundaryGram`. No injectivity outside that corner, independent
tail condition, or bound on the tail length is required. These are
finite-dimensional intermediate estimates for Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531;
they do not assert the three-interval projection defect or a spectral gap.
-/

open scoped Kronecker Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D E L : ℕ}

/-- Right multiplication by the invariant matrix, divided by its trace, on rectangular Frobenius
coordinates. -/
noncomputable def rectangularRightGramMetric (D : ℕ)
    (ρ : Matrix (Fin E) (Fin E) ℂ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D) :=
  (Matrix.toEuclideanCLM (n := Fin E × Fin D) (𝕜 := ℂ)) ((Matrix.trace ρ)⁻¹ •
    (ρ.transpose ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))

/-- The fixed rectangular metric acts by right multiplication. -/
theorem rectangularRightGramMetric_apply
    (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Y : Matrix (Fin D) (Fin E) ℂ) :
    rectangularRightGramMetric D ρ
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        ((Matrix.trace ρ)⁻¹ • (Y * ρ)) := by
  rw [rectangularRightGramMetric, Matrix.frobeniusEquivEuclidean_apply,
    Matrix.toEuclideanCLM_toLp]
  simp only [Matrix.frobeniusEquivEuclidean_apply, Matrix.smul_mulVec,
    Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, Matrix.one_mul, Matrix.vec_smul]

/-- A faithful invariant matrix gives an invertible fixed metric on rectangular boundaries. -/
theorem rectangularRightGramMetric_isUnit [NeZero E]
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hρ : ρ.PosDef) :
    IsUnit (rectangularRightGramMetric D ρ) := by
  exact ((hρ.transpose.kronecker Matrix.PosDef.one).smul (inv_pos.mpr hρ.trace_pos)).isUnit.map
    (Matrix.toEuclideanCLM (n := Fin E × Fin D) (𝕜 := ℂ))

/-- Left multiplication by a row-support matrix on rectangular Frobenius coordinates. -/
noncomputable def rectangularRowProjection (E : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D) :=
  (Matrix.toEuclideanCLM (n := Fin E × Fin D) (𝕜 := ℂ))
    ((1 : Matrix (Fin E) (Fin E) ℂ) ⊗ₖ Q)

/-- The row-support operator acts by left multiplication. -/
theorem rectangularRowProjection_apply
    (Q : Matrix (Fin D) (Fin D) ℂ) (Y : Matrix (Fin D) (Fin E) ℂ) :
    rectangularRowProjection E Q (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) (Q * Y) := by
  simp only [rectangularRowProjection, Matrix.frobeniusEquivEuclidean_apply,
    Matrix.toEuclideanCLM_toLp, Matrix.kronecker_mulVec_vec, Matrix.transpose_one,
    Matrix.mul_one]

/-- An orthogonal matrix projection induces an orthogonal projection on rectangular boundaries. -/
theorem rectangularRowProjection_isStarProjection
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : IsOrthogonalProjection Q) :
    IsStarProjection (rectangularRowProjection E Q) := by
  suffices h : IsStarProjection ((1 : Matrix (Fin E) (Fin E) ℂ) ⊗ₖ Q) from
    h.map (Matrix.toEuclideanCLM (n := Fin E × Fin D) (𝕜 := ℂ))
  rw [isStarProjection_iff']
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, hQ.2,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, hQ.1.eq, and_self]

/-- The Gram operator of the correlated tail acts by its exact row-support matrix. -/
theorem correlatedTailMapES_adjoint_comp_apply
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Y : Matrix (Fin D) (Fin E) ℂ) :
    (correlatedTailMapES A V r).adjoint.comp (correlatedTailMapES A V r)
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        ((∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
          Kraus.evalWord A (List.ofFn τ)) * Y) := by
  rw [ContinuousLinearMap.comp_apply, correlatedTailMapES_adjoint_apply]
  simp only [boundaryFamilyEquiv_correlatedTailMapES_apply, Matrix.sum_mul, Matrix.mul_assoc]

/-- The inverse fixed metric acts by right multiplication by the inverse invariant matrix,
multiplied by its trace. -/
theorem rectangularRightGramMetric_inverse_apply [NeZero E]
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hρ : ρ.PosDef)
    (Y : Matrix (Fin D) (Fin E) ℂ) :
    Ring.inverse (rectangularRightGramMetric D ρ)
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        (Matrix.trace ρ • (Y * Ring.inverse ρ)) := by
  have hMap : rectangularRightGramMetric D ρ
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        (Matrix.trace ρ • (Y * Ring.inverse ρ))) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y := by
    rw [rectangularRightGramMetric_apply]
    simp only [Matrix.smul_mul, Matrix.mul_assoc, Ring.inverse_mul_cancel ρ hρ.isUnit,
      Matrix.mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt hρ.trace_pos), one_smul]
  rw [← hMap, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
    Ring.inverse_mul_cancel _ (rectangularRightGramMetric_isUnit (D := D) hρ)]
  rfl

/-- An exact projected tail Gram matrix identifies the tail Gram operator with the row
projection. -/
theorem correlatedTailMapES_adjoint_comp_eq_rowProjection
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    (correlatedTailMapES A V r).adjoint.comp (correlatedTailMapES A V r) =
      rectangularRowProjection E Q := by
  ext x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  rw [correlatedTailMapES_adjoint_comp_apply, hGram, rectangularRowProjection_apply]

private theorem comp_support_of_gram_comp_eq
    {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (T : F →L[ℂ] G) (Q : F →L[ℂ] F)
    (hGQ : (T.adjoint.comp T).comp Q = T.adjoint.comp T) :
    T.comp Q = T := by
  ext x
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_sub, ← T.adjoint_inner_right]
  suffices T.adjoint (T (Q x - x)) = 0 by rw [this, inner_zero_right]
  change (T.adjoint.comp T) (Q x - x) = 0
  rw [map_sub]
  change ((T.adjoint.comp T).comp Q) x - (T.adjoint.comp T) x = 0
  rw [hGQ, sub_self]

/-- Right multiplication by the invariant matrix commutes with every row-support operator. -/
theorem rectangularRightGramMetric_commute_rowProjection
    (ρ : Matrix (Fin E) (Fin E) ℂ) (Q : Matrix (Fin D) (Fin D) ℂ) :
    Commute (rectangularRightGramMetric D ρ) (rectangularRowProjection E Q) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  simp only [mul_apply_eq_comp, rectangularRightGramMetric_apply,
    rectangularRowProjection_apply, Matrix.mul_smul, Matrix.mul_assoc]

/-- The fixed rectangular metric is self-adjoint for a faithful positive invariant matrix. -/
theorem rectangularRightGramMetric_isSelfAdjoint [NeZero E]
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hρ : ρ.PosDef) :
    IsSelfAdjoint (rectangularRightGramMetric D ρ) := by
  exact (((hρ.transpose.kronecker Matrix.PosDef.one).smul
    (inv_pos.mpr hρ.trace_pos)).1.isSelfAdjoint).map
      (Matrix.toEuclideanCLM (n := Fin E × Fin D) (𝕜 := ℂ))

/-- The correlated tail vanishes outside its exact projected row corner. -/
theorem correlatedTailMapES_comp_rowProjection
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    (correlatedTailMapES A V r).comp (rectangularRowProjection E Q) =
      correlatedTailMapES A V r := by
  apply comp_support_of_gram_comp_eq
  rw [correlatedTailMapES_adjoint_comp_eq_rowProjection A V r Q hGram]
  exact (rectangularRowProjection_isStarProjection (E := E) hQ).isIdempotentElem.eq


/-- The residual boundary map vanishes outside the row corner determined by the correlated tail. -/
theorem blockedResidualBoundaryMapES_comp_rowProjection
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    (blockedResidualBoundaryMapES A L B V N r).comp (rectangularRowProjection E Q) =
      blockedResidualBoundaryMapES A L B V N r := by
  apply comp_support_of_gram_comp_eq
  rw [blockedResidualBoundaryMapES_adjoint_comp_self, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, correlatedTailMapES_comp_rowProjection A V r Q hQ hGram]

/-- The residual limiting Gram metric is the fixed right metric restricted to the exact row
corner. -/
theorem residualBoundaryGramLimit_eq_rightMetric_comp_rowProjection
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (ρ : Matrix (Fin E) (Fin E) ℂ) (htr : Matrix.trace ρ ≠ 0) (r : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    residualBoundaryGramLimit A V ρ htr r =
      (rectangularRightGramMetric D ρ).comp (rectangularRowProjection E Q) := by
  ext x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  rw [residualBoundaryGramLimit_frobeniusEquivEuclidean_apply, hGram,
    ContinuousLinearMap.comp_apply, rectangularRowProjection_apply,
    rectangularRightGramMetric_apply]

private theorem supported_inverse_algebra
    {𝔄 : Type*} [Ring 𝔄] [StarRing 𝔄]
    (G R Q : 𝔄) (hQ : IsStarProjection Q) (hG : IsSelfAdjoint G)
    (hR : IsSelfAdjoint R) (hGQ : G * Q = G) (hRQ : Commute R Q)
    (hF : IsUnit (G + R * (1 - Q))) :
    G * (Q * Ring.inverse (G + R * (1 - Q))) = Q ∧
      IsSelfAdjoint (Q * Ring.inverse (G + R * (1 - Q))) := by
  have hQG : Q * G = G := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hG.star_eq] using congrArg star hGQ
  have hFQ : (G + R * (1 - Q)) * Q = G := by
    simp only [add_mul, mul_assoc, sub_mul, one_mul, hQ.isIdempotentElem.eq,
      sub_self, mul_zero, add_zero, hGQ]
  have hQF : Q * (G + R * (1 - Q)) = G := by
    rw [mul_add, hQG, ← mul_assoc, ← hRQ.eq, mul_assoc]
    simp only [mul_sub, mul_one, hQ.isIdempotentElem.eq, sub_self, mul_zero, add_zero]
  have hComm : Commute Q (G + R * (1 - Q)) := hQF.trans hFQ.symm
  have hCommInv : Commute Q (Ring.inverse (G + R * (1 - Q))) := by
    rw [← hF.unit_spec, Ring.inverse_unit]
    exact (show Commute Q (hF.unit : 𝔄) by
      simpa only [hF.unit_spec] using hComm).units_inv_right
  have hSA : IsSelfAdjoint (G + R * (1 - Q)) := by
    change star (G + R * (1 - Q)) = G + R * (1 - Q)
    simp only [star_add, star_mul, star_sub, star_one, hG.star_eq, hR.star_eq,
      hQ.isSelfAdjoint.star_eq]
    rw [sub_mul, mul_sub, one_mul, mul_one, hRQ.eq]
  constructor
  · rw [← mul_assoc, hGQ]
    calc
      G * Ring.inverse (G + R * (1 - Q)) =
          (Q * (G + R * (1 - Q))) * Ring.inverse (G + R * (1 - Q)) :=
        congrArg (fun x => x * Ring.inverse (G + R * (1 - Q))) hQF.symm
      _ = Q := by rw [mul_assoc, Ring.mul_inverse_cancel _ hF, mul_one]
  · change star (Q * Ring.inverse (G + R * (1 - Q))) = _
    rw [star_mul, hSA.ringInverse.star_eq, hQ.isSelfAdjoint.star_eq, hCommInv.eq]

/-- The residual Gram operator extended by the fixed metric on the complementary row corner. -/
noncomputable def residualBoundaryGramExtension
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (N r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D) :=
  (blockedResidualBoundaryMapES A L B V N r).adjoint.comp
      (blockedResidualBoundaryMapES A L B V N r) +
    rectangularRightGramMetric D ρ * (1 - rectangularRowProjection E Q)

/-- The inverse of the extended Gram operator restricted to the row corner. The inverse
equations require the small-error hypotheses below. -/
noncomputable def residualBoundaryGramInverse
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (N r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D) :=
  rectangularRowProjection E Q * Ring.inverse
    (residualBoundaryGramExtension A B V ρ Q N r)

/-- The extended Gram error equals the original supported residual Gram error exactly. -/
theorem residualBoundaryGramExtension_sub_rightMetric
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (Q : Matrix (Fin D) (Fin D) ℂ) (N r : ℕ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    residualBoundaryGramExtension A B V ρ Q N r - rectangularRightGramMetric D ρ =
      (blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r) -
      residualBoundaryGramLimit A V ρ htr r := by
  rw [residualBoundaryGramExtension,
    residualBoundaryGramLimit_eq_rightMetric_comp_rowProjection A V ρ htr r Q hGram]
  simp only [← ContinuousLinearMap.mul_def]
  noncomm_ring

local instance : HasSummableGeomSeries
    (EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D)) :=
  have : CompleteSpace
      (EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D)) :=
    FiniteDimensional.complete ℂ _
  inferInstance

/-- A sufficiently small primitive-prefix Gram error makes the extension invertible and gives a
self-adjoint supported inverse, its exact inverse equation, and a quantitative norm bound.
This is an intermediate estimate for Nachtergaele, arXiv:cond-mat/9410110, Lemma
`commutation` (ii). -/
theorem residualBoundaryGramInverse_properties_of_small_error [NeZero D] [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (N r : ℕ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q)
    {a : ℝ} (ha : a < 1)
    (hsmall : ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ *
      ‖groundSpaceGram B N - Matrix.gramReshuffle
        (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ ≤ a) :
    IsUnit (residualBoundaryGramExtension A B V ρ Q N r) ∧
      IsSelfAdjoint (residualBoundaryGramInverse A B V ρ Q N r) ∧
      (blockedResidualBoundaryMapES A L B V N r).comp (rectangularRowProjection E Q) =
        blockedResidualBoundaryMapES A L B V N r ∧
      ((blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r)).comp
        (residualBoundaryGramInverse A B V ρ Q N r) = rectangularRowProjection E Q ∧
      ‖residualBoundaryGramInverse A B V ρ Q N r‖ ≤
        (1 - a)⁻¹ * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ := by
  have hC := norm_correlatedTailMapES_le_one_of_wordGram_eq_projection A V r Q hQ hGram
  have hError : ‖residualBoundaryGramExtension A B V ρ Q N r -
      rectangularRightGramMetric D ρ‖ ≤ ‖groundSpaceGram B N - Matrix.gramReshuffle
        (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ := by
    rw [residualBoundaryGramExtension_sub_rightMetric A B V ρ
      (ne_of_gt hρ.trace_pos) Q N r hGram]
    exact norm_blockedResidualBoundaryMapES_gram_sub_limit_le A B V ρ
      (ne_of_gt hρ.trace_pos) N r hC
  have hUnit := NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le
    (rectangularRightGramMetric D ρ) (residualBoundaryGramExtension A B V ρ Q N r)
    (rectangularRightGramMetric_isUnit hρ)
    ((mul_le_mul_of_nonneg_left hError (norm_nonneg _)).trans hsmall) ha
  have hSupport := blockedResidualBoundaryMapES_comp_rowProjection A B V N r Q hQ hGram
  have hAlg := supported_inverse_algebra
    ((blockedResidualBoundaryMapES A L B V N r).adjoint.comp
      (blockedResidualBoundaryMapES A L B V N r))
    (rectangularRightGramMetric D ρ) (rectangularRowProjection E Q)
    (rectangularRowProjection_isStarProjection hQ)
    (by rw [ContinuousLinearMap.isSelfAdjoint_iff']; simp only
      [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint])
    (rectangularRightGramMetric_isSelfAdjoint hρ)
    (by rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, hSupport])
    (rectangularRightGramMetric_commute_rowProjection ρ Q) hUnit.1
  refine ⟨hUnit.1, hAlg.2, hSupport, hAlg.1, ?_⟩
  calc
    ‖residualBoundaryGramInverse A B V ρ Q N r‖ ≤
        ‖rectangularRowProjection E Q‖ *
          ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r)‖ := norm_mul_le _ _
    _ ≤ 1 * ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r)‖ :=
      mul_le_mul_of_nonneg_right
        (IsStarProjection.norm_le _ (rectangularRowProjection_isStarProjection hQ))
        (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hUnit.2

/-- The squared residual boundary-map norm is bounded by the fixed metric norm and the
primitive-prefix Gram error. -/
theorem norm_blockedResidualBoundaryMapES_sq_le_rightMetric_add_gram_error
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (Q : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsOrthogonalProjection Q) (N r : ℕ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q) :
    ‖blockedResidualBoundaryMapES A L B V N r‖ ^ 2 ≤
      ‖rectangularRightGramMetric D ρ‖ +
        ‖groundSpaceGram B N - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ := by
  have hC := norm_correlatedTailMapES_le_one_of_wordGram_eq_projection A V r Q hQ hGram
  have hError := norm_blockedResidualBoundaryMapES_gram_sub_limit_le A B V ρ htr N r hC
  have hLimit : ‖residualBoundaryGramLimit A V ρ htr r‖ ≤
      ‖rectangularRightGramMetric D ρ‖ := by
    rw [residualBoundaryGramLimit_eq_rightMetric_comp_rowProjection A V ρ htr r Q hGram]
    calc
      _ ≤ ‖rectangularRightGramMetric D ρ‖ * ‖rectangularRowProjection E Q‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖rectangularRightGramMetric D ρ‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (IsStarProjection.norm_le _ (rectangularRowProjection_isStarProjection hQ))
          (norm_nonneg _)
      _ = _ := mul_one _
  rw [pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self]
  calc
    _ ≤ ‖(blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r) -
        residualBoundaryGramLimit A V ρ htr r‖ +
        ‖residualBoundaryGramLimit A V ρ htr r‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        ((blockedResidualBoundaryMapES A L B V N r).adjoint.comp
          (blockedResidualBoundaryMapES A L B V N r) -
          residualBoundaryGramLimit A V ρ htr r) (residualBoundaryGramLimit A V ρ htr r)
    _ ≤ _ := by linarith

/-- A primitive prefix with a faithful invariant matrix supplies supported inverse equations and
uniform bounds for all tail lengths once the prefix is sufficiently long. This is an
intermediate estimate for Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem IsPrimitiveMPS.eventually_residualBoundaryGramInverse_properties
    [NeZero D] [NeZero E]
    {B : MPSTensor (blockPhysDim d L) E} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : IsPrimitiveMPS B ρ) (hρ : ρ.PosDef)
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r, ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q r) :
    ∀ᶠ N in Filter.atTop, ∀ r : ℕ,
      IsUnit (residualBoundaryGramExtension A B V ρ (Q r) N r) ∧
      IsSelfAdjoint (residualBoundaryGramInverse A B V ρ (Q r) N r) ∧
      (blockedResidualBoundaryMapES A L B V N r).comp (rectangularRowProjection E (Q r)) =
        blockedResidualBoundaryMapES A L B V N r ∧
      ((blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r)).comp
        (residualBoundaryGramInverse A B V ρ (Q r) N r) = rectangularRowProjection E (Q r) ∧
      ‖residualBoundaryGramInverse A B V ρ (Q r) N r‖ ≤
        2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ ∧
      ‖blockedResidualBoundaryMapES A L B V N r‖ ≤
        ‖rectangularRightGramMetric D ρ‖ + 2 := by
  let K := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hconv : Filter.Tendsto (fun N => groundSpaceGram B N) Filter.atTop (nhds K) := by
    simpa only [K] using hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hconv
  have hrelative : Filter.Tendsto
      (fun N => ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ *
        ‖groundSpaceGram B N - K‖) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hnorm
  filter_upwards [(tendsto_order.1 hrelative).2 (1 / 2) (by norm_num),
    (tendsto_order.1 hnorm).2 1 (by norm_num)] with N hrel hnormN
  intro r
  have h := residualBoundaryGramInverse_properties_of_small_error A B V hρ (Q r)
    (hQ r) N r (hGram r) (a := 1 / 2) (by norm_num) hrel.le
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_⟩
  · convert h.2.2.2.2 using 1; norm_num
  · have hsq := norm_blockedResidualBoundaryMapES_sq_le_rightMetric_add_gram_error
      A B V ρ (ne_of_gt hρ.trace_pos) (Q r) (hQ r) N r (hGram r)
    have hR := norm_nonneg (rectangularRightGramMetric D ρ)
    change ‖groundSpaceGram B N - Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ < 1 at hnormN
    nlinarith [norm_nonneg (blockedResidualBoundaryMapES A L B V N r)]

private theorem norm_inverse_sub_le
    {𝔄 : Type*} [NormedRing 𝔄] (F R : 𝔄) (hF : IsUnit F) (hR : IsUnit R) :
    ‖Ring.inverse F - Ring.inverse R‖ ≤
      ‖Ring.inverse F‖ * ‖F - R‖ * ‖Ring.inverse R‖ := by
  have hId : Ring.inverse F - Ring.inverse R =
      (Ring.inverse F * (R - F)) * Ring.inverse R := by
    rw [mul_sub, sub_mul, mul_assoc, Ring.mul_inverse_cancel R hR, mul_one,
      Ring.inverse_mul_cancel F hF, one_mul]
  rw [hId]
  calc
    _ ≤ ‖Ring.inverse F * (R - F)‖ * ‖Ring.inverse R‖ := norm_mul_le _ _
    _ ≤ (‖Ring.inverse F‖ * ‖R - F‖) * ‖Ring.inverse R‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev]

/-- The supported inverse error is at most twice the squared fixed-inverse norm times the
primitive-prefix Gram error. -/
theorem norm_residualBoundaryGramInverse_sub_limit_le [NeZero D] [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hρ : ρ.PosDef) (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (N r : ℕ)
    (hGram : ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q)
    (hsmall : ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ *
      ‖groundSpaceGram B N - Matrix.gramReshuffle
        (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ ≤ 1 / 2) :
    ‖residualBoundaryGramInverse A B V ρ Q N r -
      rectangularRowProjection E Q * Ring.inverse (rectangularRightGramMetric D ρ)‖ ≤
      2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ ^ 2 *
        ‖groundSpaceGram B N - Matrix.gramReshuffle
          (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ := by
  have hC := norm_correlatedTailMapES_le_one_of_wordGram_eq_projection A V r Q hQ hGram
  have hError : ‖residualBoundaryGramExtension A B V ρ Q N r -
      rectangularRightGramMetric D ρ‖ ≤ ‖groundSpaceGram B N - Matrix.gramReshuffle
        (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ := by
    rw [residualBoundaryGramExtension_sub_rightMetric A B V ρ
      (ne_of_gt hρ.trace_pos) Q N r hGram]
    exact norm_blockedResidualBoundaryMapES_gram_sub_limit_le A B V ρ
      (ne_of_gt hρ.trace_pos) N r hC
  have hUnit := NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le
    (rectangularRightGramMetric D ρ) (residualBoundaryGramExtension A B V ρ Q N r)
    (rectangularRightGramMetric_isUnit hρ)
    ((mul_le_mul_of_nonneg_left hError (norm_nonneg _)).trans hsmall)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hInvBound : ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r)‖ ≤
      2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ := by
    convert hUnit.2 using 1; norm_num
  rw [residualBoundaryGramInverse, ← mul_sub]
  calc
    _ ≤ ‖rectangularRowProjection E Q‖ *
        ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r) -
          Ring.inverse (rectangularRightGramMetric D ρ)‖ := norm_mul_le _ _
    _ ≤ ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r) -
          Ring.inverse (rectangularRightGramMetric D ρ)‖ := by
      exact (mul_le_mul_of_nonneg_right
        (IsStarProjection.norm_le _ (rectangularRowProjection_isStarProjection hQ))
        (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖Ring.inverse (residualBoundaryGramExtension A B V ρ Q N r)‖ *
        ‖residualBoundaryGramExtension A B V ρ Q N r - rectangularRightGramMetric D ρ‖ *
        ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ :=
      norm_inverse_sub_le _ _ hUnit.1 (rectangularRightGramMetric_isUnit hρ)
    _ ≤ (2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖) *
        ‖groundSpaceGram B N - Matrix.gramReshuffle
          (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ *
        ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hInvBound hError (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

/-- The supported inverse converges to the fixed inverse restricted to the row corner along
every diverging prefix length, with arbitrary tail lengths. This is an intermediate estimate
for Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem IsPrimitiveMPS.residualBoundaryGramInverse_sub_limit_tendsto_zero
    [NeZero D] [NeZero E]
    {B : MPSTensor (blockPhysDim d L) E} {ρ : Matrix (Fin E) (Fin E) ℂ}
    (hP : IsPrimitiveMPS B ρ) (hρ : ρ.PosDef)
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (Q : ℕ → Matrix (Fin D) (Fin D) ℂ) (hQ : ∀ r, IsOrthogonalProjection (Q r))
    (hGram : ∀ r, ∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
      Kraus.evalWord A (List.ofFn τ) = Q r)
    {κ : Type*} {f : Filter κ} {N r : κ → ℕ} (hN : Filter.Tendsto N f Filter.atTop) :
    Filter.Tendsto (fun i =>
      ‖residualBoundaryGramInverse A B V ρ (Q (r i)) (N i) (r i) -
        rectangularRowProjection E (Q (r i)) *
          Ring.inverse (rectangularRightGramMetric D ρ)‖) f (nhds 0) := by
  let K := Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hconv : Filter.Tendsto (fun N => groundSpaceGram B N) Filter.atTop (nhds K) := by
    simpa only [K] using hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp hconv).comp hN
  have hrelative : Filter.Tendsto
      (fun i => ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ *
        ‖groundSpaceGram B (N i) - K‖) f (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul hnorm
  have hUpper : Filter.Tendsto (fun i =>
      2 * ‖Ring.inverse (rectangularRightGramMetric D ρ)‖ ^ 2 *
        ‖groundSpaceGram B (N i) - K‖) f (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul hnorm
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [(tendsto_order.1 hrelative).2 (1 / 2) (by norm_num)] with i hi
  exact norm_residualBoundaryGramInverse_sub_limit_le A B V hρ (Q (r i)) (hQ (r i))
    (N i) (r i) (hGram (r i)) hi.le

end MPSTensor
