/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveBoundaryTransport
import TNLean.MPS.ParentHamiltonian.Martingale.LocalEquivalenceBounds

/-!
# Volume-independent bounds for the actual endpoint boundary changes

The normalization of the first and last active physical sites is an
invertible change on two fixed coordinate spaces, extended by identity on
all remaining coordinates. Consequently its forward and inverse norms are
bounded independently of the number of bulk sites. The equivalence below
is exactly the one used to normalize the actual extended boundary map.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

namespace MPSTensor
namespace MPOSymmetry

open ContinuousLinearMap

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- Separate the first physical coordinate from its exterior coordinates. -/
def activeFirstBoundaryConfigEquiv (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N ≃
      ((Fin D₀ ⊕ Fin D₁) × Fin D₀) ×
        ((Cfg (D₀ * D₀) N × Fin D₀) × (Fin D₀ ⊕ Fin D₁)) where
  toFun := fun (a, (b, σ, c), e) => ((a, b), ((σ, c), e))
  invFun := fun ((a, b), ((σ, c), e)) => (a, (b, σ, c), e)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Separate the last physical coordinate from its exterior coordinates. -/
def activeLastBoundaryConfigEquiv (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N ≃
      (Fin D₀ × (Fin D₀ ⊕ Fin D₁)) ×
        ((Fin D₀ ⊕ Fin D₁) × Fin D₀ × Cfg (D₀ * D₀) N) where
  toFun := fun (a, (b, σ, c), e) => ((c, e), (a, b, σ))
  invFun := fun ((c, e), (a, b, σ)) => (a, (b, σ, c), e)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Extend the first fixed boundary normalization to the active chain. -/
def activeFirstBoundaryNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) ≃ₗ[ℂ]
      EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :=
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeFirstBoundaryConfigEquiv D₀ D₁ N)
  U.toLinearEquiv.trans ((rightFiberwiseLinearEquiv
    (firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀)).trans U.symm.toLinearEquiv)

/-- Extend the last fixed boundary normalization to the active chain. -/
def activeLastBoundaryNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) ≃ₗ[ℂ]
      EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :=
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeLastBoundaryConfigEquiv D₀ D₁ N)
  U.toLinearEquiv.trans ((rightFiberwiseLinearEquiv
    (lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀)).trans U.symm.toLinearEquiv)

/-- The actual two-boundary normalization in Euclidean coordinates. -/
def activeBoundaryNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) ≃ₗ[ℂ]
      EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :=
  let U := WithLp.linearEquiv 2 ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ)
  U.trans ((activeBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀ N).trans U.symm)

/-- The actual normalization is the composition of two exterior extensions,
with no operation on the bulk physical letters. -/
theorem activeBoundaryNormalizationEquivES_eq_trans
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    activeBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀ N =
      (activeLastBoundaryNormalizationEquivES A₀ hA₀ N).trans
        (activeFirstBoundaryNormalizationEquivES A₀ hA₀ N) := by
  apply LinearEquiv.ext
  intro v
  apply PiLp.ext
  rintro ⟨a, ⟨b, σ, c⟩, e⟩
  rfl

/-- The first boundary change has its fixed local forward norm bound. -/
theorem norm_activeFirstBoundaryNormalizationEquivES_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖activeFirstBoundaryNormalizationEquivES A₀ hA₀ N v‖ ≤
      ‖(firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap.toContinuousLinearMap‖ *
        ‖v‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeFirstBoundaryConfigEquiv D₀ D₁ N)
  let e := firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  change ‖U.symm (rightFiberwiseLinearEquiv e (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_apply_le e (U v)

/-- The first boundary change has its fixed local inverse norm bound. -/
theorem norm_activeFirstBoundaryNormalizationEquivES_symm_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖(activeFirstBoundaryNormalizationEquivES A₀ hA₀ N).symm v‖ ≤
      ‖LinearMap.toContinuousLinearMap
        (firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖ * ‖v‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeFirstBoundaryConfigEquiv D₀ D₁ N)
  let e := firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  change ‖U.symm ((rightFiberwiseLinearEquiv e).symm (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_symm_apply_le e (U v)

/-- The last boundary change has its fixed local forward norm bound. -/
theorem norm_activeLastBoundaryNormalizationEquivES_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖activeLastBoundaryNormalizationEquivES A₀ hA₀ N v‖ ≤
      ‖(lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap.toContinuousLinearMap‖ *
        ‖v‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeLastBoundaryConfigEquiv D₀ D₁ N)
  let e := lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  change ‖U.symm (rightFiberwiseLinearEquiv e (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_apply_le e (U v)

/-- The last boundary change has its fixed local inverse norm bound. -/
theorem norm_activeLastBoundaryNormalizationEquivES_symm_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖(activeLastBoundaryNormalizationEquivES A₀ hA₀ N).symm v‖ ≤
      ‖LinearMap.toContinuousLinearMap
        (lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖ * ‖v‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (activeLastBoundaryConfigEquiv D₀ D₁ N)
  let e := lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  change ‖U.symm ((rightFiberwiseLinearEquiv e).symm (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_symm_apply_le e (U v)

/-- A positive forward bound determined by only the two boundary spaces. -/
def mixedEndpointBoundaryForwardBound
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) : ℝ :=
  max 1 ‖(firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap.toContinuousLinearMap‖ *
  max 1 ‖(lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).toLinearMap.toContinuousLinearMap‖

/-- A positive inverse bound determined by only the two boundary spaces. -/
def mixedEndpointBoundaryInverseBound
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) : ℝ :=
  max 1 ‖LinearMap.toContinuousLinearMap
    (firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖ *
  max 1 ‖LinearMap.toContinuousLinearMap
    (lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖

/-- The forward boundary bound is positive even for zero-dimensional spaces. -/
theorem mixedEndpointBoundaryForwardBound_pos
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) :
    0 < mixedEndpointBoundaryForwardBound A₀ hA₀ D₁ := by
  unfold mixedEndpointBoundaryForwardBound
  exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The inverse boundary bound is likewise positive. -/
theorem mixedEndpointBoundaryInverseBound_pos
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (D₁ : ℕ) :
    0 < mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ := by
  unfold mixedEndpointBoundaryInverseBound
  exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The actual forward boundary normalization is uniformly bounded in volume. -/
theorem norm_activeBoundaryNormalizationEquivES_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖activeBoundaryNormalizationEquivES A₀ hA₀ N v‖ ≤
      mixedEndpointBoundaryForwardBound A₀ hA₀ D₁ * ‖v‖ := by
  rw [activeBoundaryNormalizationEquivES_eq_trans]
  let f := firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  let g := lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀
  have hf := norm_activeFirstBoundaryNormalizationEquivES_apply_le A₀ hA₀
    (activeLastBoundaryNormalizationEquivES A₀ hA₀ N v)
  have hg := norm_activeLastBoundaryNormalizationEquivES_apply_le A₀ hA₀ v
  have hproduct : ‖f.toLinearMap.toContinuousLinearMap‖ *
      ‖g.toLinearMap.toContinuousLinearMap‖ ≤
        mixedEndpointBoundaryForwardBound A₀ hA₀ D₁ :=
    mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _)
      (le_trans (norm_nonneg _) (le_max_right _ _))
  exact hf.trans ((mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hproduct (norm_nonneg v)))

/-- The actual inverse boundary normalization is uniformly bounded in volume. -/
theorem norm_activeBoundaryNormalizationEquivES_symm_apply_le
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    ‖(activeBoundaryNormalizationEquivES A₀ hA₀ N).symm v‖ ≤
      mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ * ‖v‖ := by
  rw [activeBoundaryNormalizationEquivES_eq_trans]
  let f : ℝ := ‖LinearMap.toContinuousLinearMap
    (firstBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖
  let g : ℝ := ‖LinearMap.toContinuousLinearMap
    (lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap‖
  have hg0 : 0 ≤ g := norm_nonneg
    (lastBoundaryNormalizationEquivES (D₁ := D₁) A₀ hA₀).symm.toLinearMap.toContinuousLinearMap
  have hg : ‖(activeLastBoundaryNormalizationEquivES A₀ hA₀ N).symm
      ((activeFirstBoundaryNormalizationEquivES A₀ hA₀ N).symm v)‖ ≤
        g * ‖(activeFirstBoundaryNormalizationEquivES A₀ hA₀ N).symm v‖ :=
    norm_activeLastBoundaryNormalizationEquivES_symm_apply_le A₀ hA₀ _
  have hf : ‖(activeFirstBoundaryNormalizationEquivES A₀ hA₀ N).symm v‖ ≤ f * ‖v‖ :=
    norm_activeFirstBoundaryNormalizationEquivES_symm_apply_le A₀ hA₀ v
  have hproduct : f * g ≤ mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ := by
    change f * g ≤ max 1 f * max 1 g
    exact mul_le_mul (le_max_right 1 f) (le_max_right 1 g) hg0
      (le_trans zero_le_one (le_max_left 1 f))
  have hscale : g * (f * ‖v‖) ≤ mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ * ‖v‖ := calc
    g * (f * ‖v‖) = (f * g) * ‖v‖ :=
      (mul_left_comm g f ‖v‖).trans (mul_assoc f g ‖v‖).symm
    _ ≤ mixedEndpointBoundaryInverseBound A₀ hA₀ D₁ * ‖v‖ :=
      mul_le_mul_of_nonneg_right hproduct (norm_nonneg v)
  exact hg.trans ((mul_le_mul_of_nonneg_left hf hg0).trans hscale)

end
end MPOSymmetry
end MPSTensor
