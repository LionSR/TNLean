/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedInterpolation
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointUniformPathGap
import TNLean.MPS.ParentHamiltonian.InteractionMatrixRepresentation
import TNLean.MPS.Symmetry.PhysicalIsometricGapTransport
import TNLean.MPS.Symmetry.CommonPhysicalEndpointOrthogonality

/-!
# The mixed path for arbitrary physical alphabets

Polar decomposition restricts each one-site injective tensor to its occupied
physical support without changing its periodic state after the polar inclusion.
The mixed interpolation of these support tensors is included in one common
physical space, retaining the full original alphabets in orthogonal embeddings.
The unused physical directions receive a unit local penalty.

The actual extended interactions are continuous through the endpoints. Their
periodic kernels are exactly the lines of the included mixed periodic vectors,
and one positive gap works for every parameter and every ring of length at
least two. No gap, kernel identification, or continuity conclusion is assumed.
The endpoint interactions use the extended supports; they are not asserted to
be the canonical endpoint projections. Attaching canonical endpoint comparison
paths and constructing a common MPO symmetry are separate questions.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
lines 1584–1601 and 1687–1692.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ}

/-- The configuration matrix of the actual extended mixed interaction.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointInteractionMatrix
    (B₀ : MPSTensor (D₀ * D₀) D₀) (B₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    MPOTensor.ChainOperator ((D₀ + D₁) * (D₀ + D₁)) 2 :=
  Matrix.toEuclideanLin.symm (mixedEndpointParentInteraction B₀ B₁ γ).toLinearMap

/-- The matrix interaction represents the same Euclidean operator.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem toEuclideanLin_mixedEndpointInteractionMatrix
    (B₀ : MPSTensor (D₀ * D₀) D₀) (B₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    Matrix.toEuclideanLin (mixedEndpointInteractionMatrix B₀ B₁ γ) =
      (mixedEndpointParentInteraction B₀ B₁ γ).toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

/-- Every actual mixed interaction is positive, including at the endpoints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointInteractionMatrix_posSemidef
    (B₀ : MPSTensor (D₀ * D₀) D₀) (B₁ : MPSTensor (D₁ * D₁) D₁) (γ : ℝ) :
    (mixedEndpointInteractionMatrix B₀ B₁ γ).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [toEuclideanLin_mixedEndpointInteractionMatrix]
  exact mixedEndpointParentInteraction_isPositive B₀ B₁ γ

/-- Matrix coordinates preserve continuity of the actual extended interaction.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_mixedEndpointInteractionMatrix [NeZero D₀] [NeZero D₁]
    (B₀ : MPSTensor (D₀ * D₀) D₀) (B₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective B₀) (h₁ : Kraus.IsInjective B₁) :
    Continuous (mixedEndpointInteractionMatrix B₀ B₁) := by
  have hMat : Continuous fun T :
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →L[ℂ]
        EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) =>
      Matrix.toEuclideanLin.symm T.toLinearMap :=
    by
      let F :
          (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →L[ℂ]
            EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)) →ₗ[ℂ]
          MPOTensor.ChainOperator ((D₀ + D₁) * (D₀ + D₁)) 2 :=
        Matrix.toEuclideanLin.symm.toLinearMap.comp (ContinuousLinearMap.coeLM ℂ)
      exact F.continuous_of_finiteDimensional
  exact hMat.comp (continuous_mixedEndpointParentInteraction B₀ B₁ h₀ h₁
    (NeZero.pos D₀) (NeZero.pos D₁))

/-- The actual mixed local interaction in the common enlarged physical space.
It is the support-coordinate interaction conjugated by the common inclusion,
with energy one on its unused two-site complement.
Source: arXiv:2203.12563, Section 5, lines 1584–1601 and 1690–1692. -/
noncomputable def arbitraryPhysicalMixedInteraction
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (γ : ℝ) :
    MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2 :=
  isometricInteractionExtension
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (mixedEndpointInteractionMatrix (polarPosTensor A₀) (polarPosTensor A₁) γ)

/-- The enlarged mixed interaction is positive at every parameter.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_posSemidef
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (γ : ℝ) :
    (arbitraryPhysicalMixedInteraction A₀ A₁ γ).PosSemidef :=
  isometricInteractionExtension_posSemidef _
    (commonFixedPointInclusion_isometry _ d₀ d₁)
    (mixedEndpointInteractionMatrix_posSemidef _ _ γ)

/-- For arbitrary injective physical alphabets, the actual enlarged local
interactions vary continuously through both rank-changing endpoints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_arbitraryPhysicalMixedInteraction [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    Continuous (arbitraryPhysicalMixedInteraction A₀ A₁) := by
  let T := MPOTensor.sitewisePhysicalMatrix
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) 2
  change Continuous (fun γ => 1 - T *
    (1 - mixedEndpointInteractionMatrix (polarPosTensor A₀) (polarPosTensor A₁) γ) * Tᴴ)
  exact continuous_const.sub
    ((continuous_const.matrix_mul (continuous_const.sub
      (continuous_mixedEndpointInteractionMatrix _ _
        (isInjective_polarPosTensor h₀) (isInjective_polarPosTensor h₁)))).matrix_mul
      continuous_const)

/-- In the open interval the enlarged interaction is the canonical two-site
parent of the actual enlarged mixed tensor. This equality is not claimed
at either endpoint. Source: arXiv:2203.12563, Section 5, line 1692. -/
theorem arbitraryPhysicalMixedInteraction_eq_parent_of_mem_Ioo
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    arbitraryPhysicalMixedInteraction A₀ A₁ γ =
      LinearMap.toMatrix'
        (parentInteraction (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) 2) := by
  rw [arbitraryPhysicalMixedInterpolation,
    parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension _
      (commonFixedPointInclusion_isometry _ d₀ d₁)]
  unfold arbitraryPhysicalMixedInteraction mixedEndpointInteractionMatrix
  rw [mixedEndpointParentInteraction_eq_parentInteractionES _ _ hγ]
  simp only [LinearMap.coe_toContinuousLinearMap,
    parentInteractionES_eq_toEuclideanLin_parentMatrix, LinearEquiv.symm_apply_apply]

/-- The enlarged periodic kernel is exactly the line of the actual mixed
periodic vector, including both endpoints. Neither kernel equality nor a
limiting-state hypothesis is supplied.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2
        (mpv (N := N) (arbitraryPhysicalMixedInterpolation A₀ A₁ γ)))} := by
  rw [arbitraryPhysicalMixedInteraction,
    isometricInteractionExtension_ker_eq_map_of_posSemidef _
      (commonFixedPointInclusion_isometry _ d₀ d₁)
      (mixedEndpointInteractionMatrix_posSemidef _ _ γ) hN,
    ← periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian,
    toEuclideanLin_mixedEndpointInteractionMatrix,
    mixedEndpoint_periodic_ker_eq_range_periodicMpvLineMap _ _
      (isInjective_polarPosTensor h₀) (isInjective_polarPosTensor h₁) γ hN]
  have hline := ContinuousLinearMap.range_smulRight_apply
    (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0)
    (WithLp.toLp 2 (mpv (N := N)
      (mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ)))
  simp only [show (periodicMpvLineMap
      (mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ) N).range =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := N)
        (mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ)))}
      from hline,
    Submodule.map_span, Set.image_singleton,
    toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical,
    arbitraryPhysicalMixedInterpolation]

/-- The ground space of the actual enlarged path is one-dimensional on the
whole closed interval, including the two-site ring and both endpoints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_groundSpace_finrank
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN))) = 1 := by
  rw [arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv A₀ A₁ h₀ h₁ γ hN]
  apply finrank_span_singleton
  intro hzero
  apply mpv_arbitraryPhysicalMixedInterpolation_ne_zero A₀ A₁ h₀ h₁ γ hN
  exact congrArg WithLp.ofLp hzero

/-- One positive gap works for the actual enlarged mixed path on the entire
closed interval and all periodic lengths at least two. Polar support
injectivity, local positivity, and the support-path gap are all derived
from the original endpoint tensors. The chosen lower bound is the minimum of the support-path gap
and the unit unused-space penalty.
Source: arXiv:2203.12563, Section 5, lines 1584–1601 and 1687–1692. -/
theorem exists_uniform_arbitraryPhysicalMixed_periodic_path_gap
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ γ : unitInterval, ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN) v‖ := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_mixedEndpoint_periodic_path_gap
    (polarPosTensor A₀) (polarPosTensor A₁)
    (isInjective_polarPosTensor h₀) (isInjective_polarPosTensor h₁)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro γ N hN
  apply isometricInteractionExtension_norm_gap _
    (commonFixedPointInclusion_isometry _ d₀ d₁)
    (mixedEndpointInteractionMatrix_posSemidef _ _ γ) hN hδ.le
  rw [← periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian,
    toEuclideanLin_mixedEndpointInteractionMatrix]
  exact hgap γ N hN

end MPOSymmetry
end MPSTensor
