/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CommonPhysicalFixedPointPath
import TNLean.MPS.Symmetry.ExactMPSGappedPhase

/-!
# Exact MPS ground states of the common-space bond interpolation

The bond dimension of the injective representative is the occupied endpoint
summand at the endpoints and the full direct sum in the open interval.
Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
-/

open scoped Matrix

namespace MPSTensor

/-- Every diagonal bond coefficient is nonzero in the open interpolation
interval. Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem normalizedBondInterpolationMatrix_diagonal_ne_zero
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) {γ : ℝ}
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (a : Fin (D₀ + D₁)) :
    normalizedBondInterpolationMatrix D₀ D₁ γ a a ≠ 0 := by
  have hc : (Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (bondInterpolationSquaredNorm_pos h₀ h₁ γ)))
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  rcases a with a | a
  · simpa [normalizedBondInterpolationMatrix, bondInterpolationMatrix,
      bondInterpolationWeight] using
      mul_ne_zero (inv_ne_zero hc)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hγ₁)))
  · simpa [normalizedBondInterpolationMatrix, bondInterpolationMatrix,
      bondInterpolationWeight] using
      mul_ne_zero (inv_ne_zero hc) (Complex.ofReal_ne_zero.mpr (ne_of_gt hγ₀))

/-- In the open interval the weighted matrix units span the full bond
matrix algebra. Source: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`. -/
theorem weightedMatrixUnitInterpolation_isInjective
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) {γ : ℝ}
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    Kraus.IsInjective (weightedMatrixUnitInterpolation D₀ D₁ γ) := by
  classical
  refine Submodule.eq_top_of_forall_single_mem _ fun a b => ?_
  have hmem := Submodule.subset_span (R := ℂ)
    (s := Set.range (weightedMatrixUnitInterpolation D₀ D₁ γ))
    (show weightedMatrixUnitInterpolation D₀ D₁ γ (finProdFinEquiv (a, b)) ∈
      Set.range (weightedMatrixUnitInterpolation D₀ D₁ γ) from ⟨_, rfl⟩)
  have h := Submodule.smul_mem _
    (normalizedBondInterpolationMatrix D₀ D₁ γ a a)⁻¹ hmem
  simpa only [weightedMatrixUnitInterpolation_apply, smul_smul,
    inv_mul_cancel₀ (normalizedBondInterpolationMatrix_diagonal_ne_zero
      h₀ h₁ hγ₀ hγ₁ a), one_smul] using h

/-- The interpolating MPS is nonzero at every positive ring length.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem mpv_weightedMatrixUnitInterpolation_ne_zero
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) (hN : 0 < N) :
    (mpv (weightedMatrixUnitInterpolation D₀ D₁ γ) :
      (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁))) → ℂ) ≠ 0 := by
  let U := incomingBondUnitaryLin (D₀ + D₁) N
  let ψ := bondProductState (normalizedBondInterpolationVector D₀ D₁ γ) N
  have hψ : ψ ≠ 0 := bondProductState_ne_zero _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) N
  intro hzero
  have hz : U ψ = 0 := by
    rw [incomingBondUnitaryLin_normalizedBondInterpolation_state D₀ D₁ γ hN, hzero]
    rfl
  have h := congrArg (fun v => star U v) hz
  apply hψ
  rw [← Module.End.mul_apply, incomingBondUnitaryLin_star_mul_self] at h
  simpa using h

/-- An isometric physical inclusion preserves nonvanishing of every periodic
MPS vector. Source context: arXiv:1010.3732, Section II.F.2. -/
theorem mpv_rotatePhysical_isometry_ne_zero {d m D N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (hA : (mpv A : (Fin N → Fin d) → ℂ) ≠ 0) :
    (mpv (rotatePhysical E A) : (Fin N → Fin m) → ℂ) ≠ 0 := by
  intro hzero
  have h := toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical
    (N := N) Eᴴ (rotatePhysical E A)
  rw [rotatePhysical_rotatePhysical, hE, rotatePhysical_one, hzero] at h
  apply hA
  simpa using h.symm

/-- The endpoints admit the smaller occupied fixed-point bond space; in
the open interval the full direct sum is injective. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
theorem commonPhysicalWeightedMatrixUnitInterpolation_injective_representative
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (d₀ d₁ : ℕ)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ D : ℕ, 0 < D ∧ D ≤ D₀ + D₁ ∧ ∃ A :
      MPSTensor (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) D,
      Kraus.IsInjective A ∧ SamePositiveMpvRay
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (weightedMatrixUnitInterpolation D₀ D₁ γ)) A := by
  let Q := commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁
  have hQ := commonFixedPointInclusion_isometry ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁
  let : NeZero D₀ := ⟨ne_of_gt h₀⟩
  let : NeZero D₁ := ⟨ne_of_gt h₁⟩
  by_cases hzero : γ = 0
  · subst γ
    refine ⟨D₀, h₀, Nat.le_add_right _ _, rotatePhysical Q
      (embeddedSptFixedPointLeft D₀ D₁),
      isInjective_kraus_isometry _ Q hQ (embeddedSptFixedPointLeft_isInjective _ _), ?_⟩
    intro N hN
    apply congrArg (fun v => Submodule.span ℂ {v})
    apply WithLp.toLp_injective 2
    rw [← toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical,
      ← toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical]
    exact congrArg _ (congrArg (WithLp.toLp 2)
      (funext (mpv_embeddedSptFixedPointLeft hN)))
  · by_cases hone : γ = 1
    · subst γ
      refine ⟨D₁, h₁, Nat.le_add_left _ _, rotatePhysical Q
        (embeddedSptFixedPointRight D₀ D₁),
        isInjective_kraus_isometry _ Q hQ (embeddedSptFixedPointRight_isInjective _ _), ?_⟩
      intro N hN
      apply congrArg (fun v => Submodule.span ℂ {v})
      apply WithLp.toLp_injective 2
      rw [← toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical,
        ← toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical]
      exact congrArg _ (congrArg (WithLp.toLp 2)
        (funext (mpv_embeddedSptFixedPointRight hN)))
    · refine ⟨D₀ + D₁, by omega, le_rfl, _, ?_, SamePositiveMpvRay.refl _⟩
      exact isInjective_kraus_isometry _ Q hQ
        (weightedMatrixUnitInterpolation_isInjective h₀ h₁
          (lt_of_le_of_ne hγ.1 (Ne.symm hzero)) (lt_of_le_of_ne hγ.2 hone))

/-- The common-space bond path has continuous exact MPS ground states,
with injective bond dimension equal to the occupied dimension at each
endpoint and the full direct sum in the open interval. The ground-state
certificate uses only the explicit physical inclusion and bond coefficients.
Source: arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def exactMPSGroundPath_commonPhysicalNormalizedBondInteraction
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    {U : G →* Matrix.unitaryGroup
      (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁)) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (hP : ∀ γ, P.interaction γ =
      commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) :
    ExactMPSGroundPath P where
  bondDimension := D₀ + D₁
  bondDimension_pos := by omega
  tensor γ := rotatePhysical
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (weightedMatrixUnitInterpolation D₀ D₁ γ)
  continuous := ((continuous_rotatePhysical _).comp
    (continuous_weightedMatrixUnitInterpolation hD₀ hD₁)).continuousOn
  injective_representative γ hγ :=
    commonPhysicalWeightedMatrixUnitInterpolation_injective_representative hD₀ hD₁ d₀ d₁ hγ
  nonzero γ _ N hN := mpv_rotatePhysical_isometry_ne_zero _
    (commonFixedPointInclusion_isometry _ _ _) _
    (mpv_weightedMatrixUnitInterpolation_ne_zero hD₀ hD₁ γ hN)
  ground_line := by
    intro γ _ N hN
    simp only [hP γ]
    refine ⟨0, commonPhysicalNormalizedBondInteraction_zero_mem_spectrum
      hD₀ hD₁ d₀ d₁ γ hN, ?_, ?_⟩
    · exact fun z hz => (commonPhysicalNormalizedBondInteraction_spectrum_gap_one
        hD₀ hD₁ d₀ d₁ γ hN z hz).1
    · simpa only [Complex.ofReal_zero,
        zero_smul, sub_zero, WithLp.coe_symm_linearEquiv] using
        commonPhysicalNormalizedBondInteraction_groundSpace_eq_span_mpv hD₀ hD₁ d₀ d₁ γ hN

/-- The symmetric common-space normalized bond path carries its explicit
continuous exact MPS ground-state realization. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def commonPhysicalNormalizedBondExactMPSGroundPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    ExactMPSGroundPath
      (commonPhysicalNormalizedBondGappedPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁) :=
  exactMPSGroundPath_commonPhysicalNormalizedBondInteraction hD₀ hD₁
    (commonPhysicalNormalizedBondGappedPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁)
    (fun _ => rfl)

end MPSTensor
