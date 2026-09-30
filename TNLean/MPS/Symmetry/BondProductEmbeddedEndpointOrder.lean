/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductEndpointGroundSpace
import TNLean.MPS.Symmetry.BondProductEndpointPeriodicGroundSpace
import TNLean.MPS.Symmetry.PhysicalIsometricEmbedding

/-!
# The first embedded bond-product endpoint

The first matrix-unit summand is placed in the common physical alphabet by
the canonical rectangular isometry. Its open-boundary ground space is the
image of the unembedded ground space, and the independent-bond interaction
is bounded above by its canonical parent interaction.

Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2,
equation `eq:sym:omega-gamma`.
-/

open scoped Matrix Kronecker InnerProductSpace

namespace MPSTensor

/-- The local ground space of the first endpoint is the image of the
matrix-unit ground space under the physical inclusion. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem leftEmbeddedMatrixUnitFixedPoint_groundSpaceES
    (D₀ D₁ : ℕ) [NeZero D₀] :
    groundSpaceES (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 =
      (groundSpaceES (matrixUnitFixedPoint D₀) 2).map
        (Matrix.toEuclideanLin
          (physicalEmbeddingTensorPow 2 (leftPhysicalIsometry D₀ D₁))) := by
  rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding,
    groundSpaceES_physicalEmbedding]
  have hc : (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos D₀))
  change (groundSpaceES (fun q : Fin (D₀ * D₀) =>
    (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀ q) 2).map _ = _
  unfold groundSpaceES
  have hs := groundSpace_smul_eq (matrixUnitFixedPoint D₀)
    (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ hc 2
  change groundSpace (fun q : Fin (D₀ * D₀) =>
    (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀ q) 2 =
      groundSpace (matrixUnitFixedPoint D₀) 2 at hs
  rw [hs]

private theorem groundSpaceMap_scaledMatrixUnit_two_apply
    (D : ℕ) (c : ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (s : Fin 2 → Fin (D * D)) :
    groundSpaceMap (c • matrixUnitFixedPoint D) 2 X s =
      c ^ 2 * groundSpaceMap (matrixUnitFixedPoint D) 2 X s := by
  rw [groundSpaceMap_apply, groundSpaceMap_apply]
  change (Kraus.evalWord (fun i => c • matrixUnitFixedPoint D i) (List.ofFn s) * X).trace = _
  rw [Kraus.evalWord_smul]
  simp

/-- The embedded two-site boundary vector is the physical tensor square
of the matrix-unit boundary vector, multiplied by the square of the bond
normalization. Source: arXiv:1010.3732, Section II.F.2. -/
theorem groundSpaceMap_leftEmbeddedMatrixUnitFixedPoint_two_apply
    (D₀ D₁ : ℕ) [NeZero D₀]
    (X : Matrix (Fin D₀) (Fin D₀) ℂ)
    (s : Fin 2 → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    groundSpaceMap (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 X s =
      (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ ^ 2 *
        ∑ t : Fin 2 → Fin (D₀ * D₀),
          (∏ k : Fin 2, leftPhysicalIsometry D₀ D₁ (s k) (t k)) *
            (if (finProdFinEquiv.symm (t 0)).2 =
                (finProdFinEquiv.symm (t 1)).1 then
              X (finProdFinEquiv.symm (t 1)).2
                (finProdFinEquiv.symm (t 0)).1 else 0) := by
  rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding,
    groundSpaceMap_physicalEmbedding]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    physicalEmbeddingTensorPow_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hscaled : groundSpaceMap (fun q : Fin (D₀ * D₀) =>
      (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀ q) 2 X t =
      (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ ^ 2 *
        groundSpaceMap (matrixUnitFixedPoint D₀) 2 X t := by
    exact groundSpaceMap_scaledMatrixUnit_two_apply D₀ _ X t
  rw [hscaled, groundSpaceMap_matrixUnitFixedPoint_two_apply]
  ring

/-- The rank-one bond penalties intertwine the first-summand physical
inclusion. Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondPenalty_leftPhysicalIsometry
    (D₀ D₁ : ℕ) :
    bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0) *
      leftPhysicalIsometry D₀ D₁ =
    leftPhysicalIsometry D₀ D₁ * bondPenalty (matrixUnitBondVector D₀) := by
  let V := leftPhysicalIsometry D₀ D₁
  let η := matrixUnitBondVector D₀
  have hη : V *ᵥ η = normalizedBondInterpolationVector D₀ D₁ 0 :=
    leftPhysicalIsometry_mulVec_matrixUnitBondVector D₀ D₁
  have hV : Vᴴ * V = 1 :=
    leftPhysicalIsometry_conjTranspose_mul_self D₀ D₁
  rw [← hη]
  change (1 - Matrix.vecMulVec (V *ᵥ η) (star (V *ᵥ η))) * V =
    V * (1 - Matrix.vecMulVec η (star η))
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  congr 1
  rw [Matrix.vecMulVec_mul, Matrix.mul_vecMulVec]
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, hV]
  simp

private def leftVirtualIsometry (D₀ D₁ : ℕ) :
    Matrix (Fin (D₀ + D₁)) (Fin D₀) ℂ :=
  fun a b => if a = finSumFinEquiv (Sum.inl b) then 1 else 0

private theorem leftPhysicalIsometry_eq_kronecker
    (D₀ D₁ : ℕ) :
    Matrix.reindex
      (finProdFinEquiv.symm : Fin ((D₀ + D₁) * (D₀ + D₁)) ≃
        Fin (D₀ + D₁) × Fin (D₀ + D₁))
      (finProdFinEquiv.symm : Fin (D₀ * D₀) ≃ Fin D₀ × Fin D₀)
      (leftPhysicalIsometry D₀ D₁) =
      leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.reindex_apply, leftPhysicalIsometry_apply_pair,
    leftVirtualIsometry, Matrix.kroneckerMap_apply, Prod.mk.injEq,
    ite_and]
  split_ifs <;> simp_all

private theorem physicalEmbeddingTensorPow_two_reindex
    (D₀ D₁ : ℕ) :
    Matrix.reindex (twoSiteBondEquiv (D₀ + D₁)) (twoSiteBondEquiv D₀)
      (physicalEmbeddingTensorPow 2 (leftPhysicalIsometry D₀ D₁)) =
      ((leftVirtualIsometry D₀ D₁ ⊗ₖ
          (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁)) ⊗ₖ
        leftVirtualIsometry D₀ D₁) := by
  ext ⟨⟨a, ⟨b, c⟩⟩, d⟩ ⟨⟨a', ⟨b', c'⟩⟩, d'⟩
  simp [Matrix.reindex_apply, physicalEmbeddingTensorPow_apply,
    twoSiteBondEquiv, leftPhysicalIsometry_apply_pair,
    leftVirtualIsometry, Matrix.kroneckerMap_apply]
  by_cases ha : a = finSumFinEquiv (Sum.inl a')
  <;> by_cases hb : b = finSumFinEquiv (Sum.inl b')
  <;> by_cases hc : c = finSumFinEquiv (Sum.inl c')
  <;> by_cases hd : d = finSumFinEquiv (Sum.inl d')
  <;> simp only [finSumFinEquiv_apply_left] at ha hb hc hd
  <;> simp [ha, hb, hc, hd]

private theorem bondPenalty_leftVirtualIsometry_kronecker
    (D₀ D₁ : ℕ) :
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0))) *
      (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁) =
    (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁) *
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D₀))) := by
  let eb : Fin ((D₀ + D₁) * (D₀ + D₁)) ≃
      Fin (D₀ + D₁) × Fin (D₀ + D₁) := finProdFinEquiv.symm
  let es : Fin (D₀ * D₀) ≃ Fin D₀ × Fin D₀ := finProdFinEquiv.symm
  have h := congrArg (Matrix.reindex eb es)
    (bondPenalty_leftPhysicalIsometry D₀ D₁)
  change Matrix.reindexLinearEquiv ℂ ℂ eb es
      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0) *
        leftPhysicalIsometry D₀ D₁) =
    Matrix.reindexLinearEquiv ℂ ℂ eb es
      (leftPhysicalIsometry D₀ D₁ * bondPenalty (matrixUnitBondVector D₀)) at h
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ eb eb es,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ eb es es] at h
  change (Matrix.reindex eb eb
      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0))) *
      (Matrix.reindex eb es (leftPhysicalIsometry D₀ D₁)) =
    (Matrix.reindex eb es (leftPhysicalIsometry D₀ D₁)) *
      (Matrix.reindex es es (bondPenalty (matrixUnitBondVector D₀))) at h
  rw [leftPhysicalIsometry_eq_kronecker] at h
  exact h

private theorem twoSiteBondInteraction_leftPhysicalIsometry_intertwines
    (D₀ D₁ : ℕ) :
    twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0))) *
      physicalEmbeddingTensorPow 2 (leftPhysicalIsometry D₀ D₁) =
    physicalEmbeddingTensorPow 2 (leftPhysicalIsometry D₀ D₁) *
      twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (matrixUnitBondVector D₀))) := by
  let eb := twoSiteBondEquiv (D₀ + D₁)
  let es := twoSiteBondEquiv D₀
  apply (Matrix.reindex eb es).injective
  let H := twoSiteBondInteraction
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0)))
  let E := physicalEmbeddingTensorPow 2 (leftPhysicalIsometry D₀ D₁)
  let h := twoSiteBondInteraction
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty (matrixUnitBondVector D₀)))
  change (Matrix.reindexLinearEquiv ℂ ℂ eb es) (H * E) =
    (Matrix.reindexLinearEquiv ℂ ℂ eb es) (E * h)
  calc
    (Matrix.reindexLinearEquiv ℂ ℂ eb es) (H * E) =
        (Matrix.reindexLinearEquiv ℂ ℂ eb eb) H *
          (Matrix.reindexLinearEquiv ℂ ℂ eb es) E :=
      (Matrix.reindexLinearEquiv_mul ℂ ℂ eb eb es H E).symm
    _ = (Matrix.reindexLinearEquiv ℂ ℂ eb es) E *
          (Matrix.reindexLinearEquiv ℂ ℂ es es) h := by
            have hH : (Matrix.reindexLinearEquiv ℂ ℂ eb eb) H =
                (((1 : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) ⊗ₖ
                    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
                      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0)))) ⊗ₖ
                  (1 : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)) := by
              simp [H, eb, twoSiteBondInteraction]
            have hE : (Matrix.reindexLinearEquiv ℂ ℂ eb es) E =
                ((leftVirtualIsometry D₀ D₁ ⊗ₖ
                    (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁)) ⊗ₖ
                  leftVirtualIsometry D₀ D₁) := by
              simpa [E, eb, es] using physicalEmbeddingTensorPow_two_reindex D₀ D₁
            have hh : (Matrix.reindexLinearEquiv ℂ ℂ es es) h =
                (((1 : Matrix (Fin D₀) (Fin D₀) ℂ) ⊗ₖ
                    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
                      (bondPenalty (matrixUnitBondVector D₀)))) ⊗ₖ
                  (1 : Matrix (Fin D₀) (Fin D₀) ℂ)) := by
              simp [h, es, twoSiteBondInteraction]
            rw [hH, hE, hh]
            change
              (((1 : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) ⊗ₖ
                  (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
                    (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0)))) ⊗ₖ
                (1 : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)) *
                ((leftVirtualIsometry D₀ D₁ ⊗ₖ
                    (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁)) ⊗ₖ
                  leftVirtualIsometry D₀ D₁) =
              ((leftVirtualIsometry D₀ D₁ ⊗ₖ
                  (leftVirtualIsometry D₀ D₁ ⊗ₖ leftVirtualIsometry D₀ D₁)) ⊗ₖ
                leftVirtualIsometry D₀ D₁) *
                (((1 : Matrix (Fin D₀) (Fin D₀) ℂ) ⊗ₖ
                    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
                      (bondPenalty (matrixUnitBondVector D₀)))) ⊗ₖ
                  (1 : Matrix (Fin D₀) (Fin D₀) ℂ))
            rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
            conv_rhs => rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
            simp only [Matrix.one_mul, Matrix.mul_one]
            rw [bondPenalty_leftVirtualIsometry_kronecker]
    _ = (Matrix.reindexLinearEquiv ℂ ℂ eb es) (E * h) :=
      Matrix.reindexLinearEquiv_mul ℂ ℂ eb es es E h

/-- At the first endpoint, the independent-bond interaction is bounded
above by the canonical parent interaction in the common physical space.
Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem leftEmbeddedMatrixUnitFixedPoint_bondInteraction_le_parentInteractionES
    (D₀ D₁ : ℕ) [NeZero D₀] (h₁ : 0 < D₁) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0)))) ≤
      parentInteractionES (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 := by
  apply twoSiteBondInteraction_le_parentInteractionES_of_groundSpaceMap
    (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)
    (normalizedBondInterpolationVector D₀ D₁ 0)
    (normalizedBondInterpolationVector_sum_normSq (NeZero.pos D₀) h₁ 0)
  intro X
  let V := leftPhysicalIsometry D₀ D₁
  let T := physicalEmbeddingTensorPow 2 V
  let M := twoSiteBondInteraction
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty (normalizedBondInterpolationVector D₀ D₁ 0)))
  let m := twoSiteBondInteraction
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty (matrixUnitBondVector D₀)))
  have hmap : groundSpaceMap (leftEmbeddedMatrixUnitFixedPoint D₀ D₁) 2 X =
      T *ᵥ groundSpaceMap
        ((↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀) 2 X := by
    rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding,
      groundSpaceMap_physicalEmbedding]
    rfl
  have hscaled : groundSpaceMap
      ((↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀) 2 X =
      (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ ^ 2 •
        groundSpaceMap (matrixUnitFixedPoint D₀) 2 X := by
    funext s
    simpa only [Pi.smul_apply, smul_eq_mul] using
      groundSpaceMap_scaledMatrixUnit_two_apply D₀ _ X s
  rw [hmap]
  change M *ᵥ (T *ᵥ groundSpaceMap
    ((↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹ • matrixUnitFixedPoint D₀) 2 X) = 0
  rw [Matrix.mulVec_mulVec,
    twoSiteBondInteraction_leftPhysicalIsometry_intertwines D₀ D₁,
    ← Matrix.mulVec_mulVec, hscaled, Matrix.mulVec_smul,
    twoSiteBondInteraction_groundSpaceMap_matrixUnitFixedPoint D₀
      (NeZero.pos D₀) X]
  simp

end MPSTensor
