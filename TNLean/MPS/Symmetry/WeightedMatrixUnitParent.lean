/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPointGappedPath
import TNLean.MPS.Symmetry.WeightedMatrixUnitInterpolation
import TNLean.MPS.Symmetry.BondProductEndpointGroundSpace
import TNLean.MPS.Symmetry.TwoSiteBondContraction
import TNLean.MPS.ParentHamiltonian.MatrixRepresentation

/-!
# Canonical parents of the weighted matrix-unit interpolation

The open-boundary two-site vectors have the normalized interpolating bond
on their internal registers. Its bond penalty therefore annihilates these
vectors and is bounded above by the canonical parent projection.

Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
The argument includes the endpoints, where some bond coefficients vanish.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- The two-site boundary vector factors into the internal bond coefficient
and an external boundary coefficient. Source: arXiv:1010.3732,
Section II.F.2, the matrix-unit form of `eq:sym:omega-gamma`. -/
theorem groundSpaceMap_weightedMatrixUnitInterpolation_two_apply (D₀ D₁ : ℕ) (γ : ℝ)
    (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)
    (s : Fin 2 → Fin ((D₀ + D₁) * (D₀ + D₁))) :
    groundSpaceMap (weightedMatrixUnitInterpolation D₀ D₁ γ) 2 X s =
      normalizedBondInterpolationMatrix D₀ D₁ γ (sptPair (s 0)).1 (sptPair (s 0)).1 *
      normalizedBondInterpolationMatrix D₀ D₁ γ (sptPair (s 0)).2 (sptPair (s 1)).1 *
      X (sptPair (s 1)).2 (sptPair (s 0)).1 := by
  simp only [groundSpaceMap_apply, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    List.ofFn_zero, Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one,
    finProdFinEquiv_symm_apply, weightedMatrixUnitInterpolation, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  by_cases h : (s 0).modNat = (s 1).divNat
  · simp [h, Matrix.single_mul_single_same, Matrix.trace_single_mul,
      normalizedBondInterpolationMatrix, bondInterpolationMatrix, mul_assoc]
  · simp [h, Matrix.single_mul_single_of_ne, normalizedBondInterpolationMatrix,
      bondInterpolationMatrix]

/-- The independent-bond penalty annihilates every two-site boundary
vector of the weighted interpolation, including its endpoints.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem twoSiteBondInteraction_groundSpaceMap_weightedMatrixUnitInterpolation
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)))).mulVec
      (groundSpaceMap (weightedMatrixUnitInterpolation D₀ D₁ γ) 2 X) = 0 := by
  have hform : groundSpaceMap (weightedMatrixUnitInterpolation D₀ D₁ γ) 2 X =
      fun s => normalizedBondInterpolationVector D₀ D₁ γ
        (finProdFinEquiv ((sptPair (s 0)).2, (sptPair (s 1)).1)) *
        (normalizedBondInterpolationMatrix D₀ D₁ γ
          (sptPair (s 0)).1 (sptPair (s 0)).1 *
          X (sptPair (s 1)).2 (sptPair (s 0)).1) := by
    funext s
    rw [groundSpaceMap_weightedMatrixUnitInterpolation_two_apply]
    simp [normalizedBondInterpolationVector, sptPair, mul_assoc, mul_left_comm]
  simpa only [hform] using twoSiteBondPenalty_mulVec_separable
    (normalizedBondInterpolationVector D₀ D₁ γ)
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)
    (fun a d => normalizedBondInterpolationMatrix D₀ D₁ γ a a * X d a)

/-- The bond interaction is bounded above by the canonical two-site parent
of the weighted matrix-unit tensor. No injectivity of the endpoint tensor
is required. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, canonical parent comparison. -/
theorem twoSiteBondInteraction_le_parentInteractionES_weightedMatrixUnitInterpolation
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)))) ≤
      parentInteractionES (weightedMatrixUnitInterpolation D₀ D₁ γ) 2 :=
  twoSiteBondInteraction_le_parentInteractionES_of_groundSpaceMap
    (weightedMatrixUnitInterpolation D₀ D₁ γ)
    (normalizedBondInterpolationVector D₀ D₁ γ)
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)
    (twoSiteBondInteraction_groundSpaceMap_weightedMatrixUnitInterpolation h₀ h₁ γ)

/-- Matrix form of the canonical-parent comparison for the weighted
interpolation. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, canonical parent comparison. -/
theorem twoSiteBondInteraction_le_parentInteraction_weightedMatrixUnitInterpolation
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ))) ≤
      LinearMap.toMatrix' (parentInteraction (weightedMatrixUnitInterpolation D₀ D₁ γ) 2) := by
  rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff, map_sub,
    ← parentInteractionES_eq_toEuclideanLin_parentMatrix]
  exact LinearMap.le_def.mp
    (twoSiteBondInteraction_le_parentInteractionES_weightedMatrixUnitInterpolation h₀ h₁ γ)

/-- The weighted periodic MPS is the unit product of its interpolating
bonds after regrouping the physical registers. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem incomingBondUnitaryLin_normalizedBondInterpolation_state
    (D₀ D₁ : ℕ) (γ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    incomingBondUnitaryLin (D₀ + D₁) N
      (bondProductState (normalizedBondInterpolationVector D₀ D₁ γ) N) =
      WithLp.toLp 2 (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  ext σ
  simp only [incomingBondUnitaryLin, bondMatrixEquiv_symm_eq_toEuclideanLin,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, bondProductState, WithLp.ofLp_toLp,
    Matrix.permMatrix_mulVec, Function.comp_apply]
  simpa only [bondProductVector, normalizedBondInterpolationVector, incomingBondPerm,
    Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply] using
    (mpv_weightedMatrixUnitInterpolation_eq_incomingBondProduct D₀ D₁ L γ σ).symm

/-- The periodic bond Hamiltonian has exactly the weighted MPS ground line.
This holds for every real interpolation parameter, including both
endpoints. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem interactionHamiltonian_normalizedBondInteraction_groundSpace
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) =
      Submodule.span ℂ
        ({WithLp.toLp 2 (mpv (N := N) (weightedMatrixUnitInterpolation D₀ D₁ γ))} :
          Set (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))) := by
  have : NeZero N := ⟨by omega⟩
  rw [normalizedBondInteraction, interactionHamiltonian_twoSiteBondPenalty,
    ← bondMatrixEquiv_symm_eq_toEuclideanLin,
    ← physicalBondProductParentHamiltonianLin_eq_matrix,
    physicalBondProductParentHamiltonian_groundSpace _
      (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) (by omega),
    incomingBondUnitaryLin_normalizedBondInterpolation_state D₀ D₁ γ (by omega)]

/-- Every periodic zero mode of the bond interaction is a zero mode of
its canonical parent. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, comparison with the canonical parent. -/
theorem ker_interactionHamiltonian_normalizedBondInteraction_le_parent
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) ≤
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (LinearMap.toMatrix' (parentInteraction
        (weightedMatrixUnitInterpolation D₀ D₁ γ) 2)) hN)) := by
  rw [interactionHamiltonian_normalizedBondInteraction_groundSpace h₀ h₁ γ hN]
  apply Submodule.span_le.mpr
  rintro x (rfl : x = WithLp.toLp 2 (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ)))
  change Matrix.toEuclideanLin (∑ i : Fin N, MPOTensor.embedLocalOperator 2 N hN i
    (LinearMap.toMatrix' (parentInteraction (weightedMatrixUnitInterpolation D₀ D₁ γ) 2)))
    (WithLp.toLp 2 (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ))) = 0
  rw [← parentHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator]
  change WithLp.toLp 2 (parentHamiltonian (weightedMatrixUnitInterpolation D₀ D₁ γ)
    2 N (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ))) = 0
  rw [parentHamiltonian_annihilates _ 2 N hN, WithLp.toLp_zero]

/-- Function-coordinate form of the periodic kernel inclusion. Source:
arXiv:1010.3732, Section II.F.2, canonical parent comparison. -/
theorem interactionHamiltonian_parent_mulVec_eq_zero_of_normalizedBondInteraction
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N)
    (x : Cfg ((D₀ + D₁) * (D₀ + D₁)) N → ℂ)
    (hx : (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN).mulVec x = 0) :
    (interactionHamiltonian (LinearMap.toMatrix' (parentInteraction
      (weightedMatrixUnitInterpolation D₀ D₁ γ) 2)) hN).mulVec x = 0 := by
  have hxES : WithLp.toLp 2 x ∈ LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) := by
    change WithLp.toLp 2 ((interactionHamiltonian
      (normalizedBondInteraction D₀ D₁ γ) hN).mulVec x) = 0
    rw [hx, WithLp.toLp_zero]
  have hparent := (ker_interactionHamiltonian_normalizedBondInteraction_le_parent
    h₀ h₁ γ hN) hxES
  simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero] using hparent

end MPSTensor
