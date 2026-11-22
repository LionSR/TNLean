/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPoint.FixedPointGappedPath
import TNLean.MPS.Symmetry.FixedPoint.WeightedMatrixUnitInterpolation
import TNLean.MPS.Symmetry.FixedPoint.BondProductEndpointGroundSpace
import TNLean.MPS.Symmetry.FixedPoint.TwoSiteBondContraction
import TNLean.MPS.ParentHamiltonian.ParentInteraction.MatrixRepresentation

/-!
# Canonical parents of the weighted matrix-unit interpolation

The open-boundary two-site vectors have the normalized interpolating bond
on their internal registers. Its bond penalty therefore annihilates these
vectors and is bounded above by the canonical parent projection.

Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
The argument includes the endpoints, where some bond coefficients vanish.
-/

open scoped Matrix MatrixOrder ComplexOrder

open ManyBody

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

/-- Matrix form of the canonical-parent comparison for the weighted
interpolation. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, canonical parent comparison. -/
theorem twoSiteBondInteraction_le_parentInteraction_weightedMatrixUnitInterpolation
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ))) ≤
      LinearMap.toMatrix' (parentInteraction (weightedMatrixUnitInterpolation D₀ D₁ γ) 2) :=
  twoSiteBondInteraction_le_parentInteraction_of_groundSpaceMap _ _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)
    (twoSiteBondInteraction_groundSpaceMap_weightedMatrixUnitInterpolation h₀ h₁ γ)

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
theorem hamiltonian_translationInvariant_normalizedBondInteraction_groundSpace
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (normalizedBondInteraction D₀ D₁ γ)).hamiltonian) =
      Submodule.span ℂ
        ({WithLp.toLp 2 (mpv (N := N) (weightedMatrixUnitInterpolation D₀ D₁ γ))} :
          Set (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))) := by
  have : NeZero N := ⟨by omega⟩
  rw [normalizedBondInteraction, hamiltonian_translationInvariant_twoSiteBondPenalty hN,
    ← bondMatrixEquiv_symm_eq_toEuclideanLin,
    ← physicalBondProductParentHamiltonianLin_eq_matrix,
    physicalBondProductParentHamiltonian_groundSpace _
      (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) (by omega),
    incomingBondUnitaryLin_normalizedBondInterpolation_state D₀ D₁ γ (by omega)]

/-- A canonical parent annihilates every periodic bond zero mode when
its periodic vector equals the weighted bond vector. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, comparison with the canonical parent. -/
theorem ker_hamiltonian_translationInvariant_normalizedBondInteraction_le_parent_of_mpv_eq
    {D₀ D₁ E N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) E)
    (hmpv : ∀ σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N,
      mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) σ = mpv B σ) :
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (normalizedBondInteraction D₀ D₁ γ)).hamiltonian) ≤
    LinearMap.ker (Matrix.toEuclideanLin (Interaction.translationInvariant N
      (LinearMap.toMatrix' (parentInteraction B 2))).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  rw [hamiltonian_translationInvariant_normalizedBondInteraction_groundSpace h₀ h₁ γ hN,
    show mpv (N := N) (weightedMatrixUnitInterpolation D₀ D₁ γ) = mpv B from funext hmpv]
  apply Submodule.span_le.mpr
  rintro x (rfl : x = WithLp.toLp 2 (mpv B))
  change WithLp.toLp 2 (Matrix.toLin' (parentRingInteraction B 2 N).hamiltonian (mpv B)) = 0
  rw [← parentHamiltonian_eq_toLin'_hamiltonian B 2, parentHamiltonian_annihilates _ 2 N hN,
    WithLp.toLp_zero]

/-- Every periodic zero mode of the bond interaction is a zero mode of
its canonical parent. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, comparison with the canonical parent. -/
theorem ker_hamiltonian_translationInvariant_normalizedBondInteraction_le_parent
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (normalizedBondInteraction D₀ D₁ γ)).hamiltonian) ≤
    LinearMap.ker (Matrix.toEuclideanLin (Interaction.translationInvariant N
      (LinearMap.toMatrix' (parentInteraction
        (weightedMatrixUnitInterpolation D₀ D₁ γ) 2))).hamiltonian) :=
  haveI : NeZero N := ⟨by omega⟩;
  ker_hamiltonian_translationInvariant_normalizedBondInteraction_le_parent_of_mpv_eq
    h₀ h₁ γ hN _ (fun _ => rfl)

/-- Function-coordinate form of the periodic kernel inclusion. Source:
arXiv:1010.3732, Section II.F.2, canonical parent comparison. -/
theorem
    hamiltonian_translationInvariant_parent_mulVec_eq_zero_of_normalizedBondInteraction_of_mpv_eq
    {D₀ D₁ E N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) E)
    (hmpv : ∀ σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N,
      mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) σ = mpv B σ)
    (x : Cfg ((D₀ + D₁) * (D₀ + D₁)) N → ℂ)
    (hx : haveI : NeZero N := ⟨by omega⟩; (Interaction.translationInvariant N
      (normalizedBondInteraction D₀ D₁ γ)).hamiltonian.mulVec x = 0) :
    haveI : NeZero N := ⟨by omega⟩; (Interaction.translationInvariant N
      (LinearMap.toMatrix' (parentInteraction B 2))).hamiltonian.mulVec x = 0 := by
  have : NeZero N := ⟨by omega⟩
  have hxES : WithLp.toLp 2 x ∈ LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (normalizedBondInteraction D₀ D₁ γ)).hamiltonian) := by
    change WithLp.toLp 2 ((Interaction.translationInvariant N
      (normalizedBondInteraction D₀ D₁ γ)).hamiltonian.mulVec x) = 0
    rw [hx, WithLp.toLp_zero]
  have hparent :=
    (ker_hamiltonian_translationInvariant_normalizedBondInteraction_le_parent_of_mpv_eq
      h₀ h₁ γ hN B hmpv) hxES
  simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero] using hparent

/-- Function-coordinate form of the periodic kernel inclusion. Source:
arXiv:1010.3732, Section II.F.2, canonical parent comparison. -/
theorem hamiltonian_translationInvariant_parent_mulVec_eq_zero_of_normalizedBondInteraction
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N)
    (x : Cfg ((D₀ + D₁) * (D₀ + D₁)) N → ℂ)
    (hx : haveI : NeZero N := ⟨by omega⟩; (Interaction.translationInvariant N
      (normalizedBondInteraction D₀ D₁ γ)).hamiltonian.mulVec x = 0) :
    haveI : NeZero N := ⟨by omega⟩;
    (Interaction.translationInvariant N (LinearMap.toMatrix' (parentInteraction
      (weightedMatrixUnitInterpolation D₀ D₁ γ) 2))).hamiltonian.mulVec x = 0 :=
  haveI : NeZero N := ⟨by omega⟩;
  hamiltonian_translationInvariant_parent_mulVec_eq_zero_of_normalizedBondInteraction_of_mpv_eq
    h₀ h₁ γ hN _ (fun _ => rfl) x hx

end MPSTensor
