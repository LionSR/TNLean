/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedPathGap
import TNLean.MPS.Symmetry.CommonPhysicalCanonicalGroundPath
import TNLean.MPS.Symmetry.CanonicalInjectiveGroundPath

/-!
# Canonical parents at the ends of the arbitrary-physical mixed path

The canonical two-site support of each embedded original tensor lies in the
extended limiting support. Consequently its canonical parent dominates the
actual limiting interaction. Their periodic kernels agree with the original
embedded MPS line. Affine interpolation therefore attaches each limiting
interaction to its canonical parent without reducing the uniform gap.

The original physical dimensions are arbitrary. The only tensor hypotheses
are one-site injectivity and positive bond dimensions. No symmetry is asserted:
the fixed MPO representation required for the symmetric phase relation is a
separate construction.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
`defphase`, the parent-Hamiltonian restriction (lines 1328–1331), and the
limiting parent interactions (lines 1690–1692).
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- An ordered affine interpolation with the same periodic kernel preserves
a uniform norm gap of the smaller interaction. This comparison supplies the
parent-Hamiltonian attachment used in arXiv:2203.12563, Section 5,
lines 1328–1331. -/
theorem interactionHamiltonian_affine_norm_gap_of_order {d N : ℕ}
    (A B : MPOTensor.ChainOperator d 2) (hA : A.PosSemidef) (hAB : A ≤ B)
    (hN : 2 ≤ N)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian B hN)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (interactionHamiltonian A hN)))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (interactionHamiltonian A hN) v‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (A + t • (B - A)) hN)))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
        (interactionHamiltonian (A + t • (B - A)) hN) v‖ := by
  have hAC : A ≤ A + t • (B - A) := by
    rw [Matrix.le_iff]
    simpa using (Matrix.le_iff.mp hAB).smul ht
  have hHC := interactionHamiltonian_mono hAC hN
  have hHC' : Matrix.toEuclideanLin (interactionHamiltonian A hN) ≤
      Matrix.toEuclideanLin (interactionHamiltonian (A + t • (B - A)) hN) := by
    change (Matrix.toEuclideanLin (interactionHamiltonian (A + t • (B - A)) hN) -
      Matrix.toEuclideanLin (interactionHamiltonian A hN)).IsPositive
    rw [← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hHC
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (interactionHamiltonian_posSemidef hA hN)).norm_gap_of_le_of_ker_eq hδ hHC'
      (interactionHamiltonian_affine_ker_eq_of_order A B hA hAB hN hker t ht).symm hgap

namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ}

/-- The actual first limiting interaction is no larger than the canonical
parent of the fully embedded original first tensor. Source:
arXiv:2203.12563, Section 5, lines 1584–1601 and 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_zero_le_parent
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) :
    arbitraryPhysicalMixedInteraction A₀ A₁ 0 ≤
      LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2) := by
  rw [← rotatePhysical_mixedEndpointLeftTensor_polarPosTensor d₁ D₁ h₀,
    parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension _
      (commonFixedPointInclusion_isometry _ d₀ d₁)]
  apply isometricInteractionExtension_mono
  rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff, map_sub,
    ← parentInteractionES_eq_toEuclideanLin_parentMatrix,
    toEuclideanLin_mixedEndpointInteractionMatrix]
  exact mixedEndpointParentInteraction_zero_le_parentInteractionES _ _

/-- The corresponding local order at the second limiting interaction uses
the fully embedded original second tensor. Source: arXiv:2203.12563,
Section 5, lines 1584–1601 and 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_one_le_parent
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₁ : Kraus.IsInjective A₁) :
    arbitraryPhysicalMixedInteraction A₀ A₁ 1 ≤
      LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2) := by
  rw [← rotatePhysical_mixedEndpointRightTensor_polarPosTensor d₀ D₀ h₁,
    parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension _
      (commonFixedPointInclusion_isometry _ d₀ d₁)]
  apply isometricInteractionExtension_mono
  rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff, map_sub,
    ← parentInteractionES_eq_toEuclideanLin_parentMatrix,
    toEuclideanLin_mixedEndpointInteractionMatrix]
  exact mixedEndpointParentInteraction_one_le_parentInteractionES _ _

/-- The canonical parent of either embedded original tensor. The Boolean
selects the first tensor at `false` and the second at `true`.
Source: arXiv:2203.12563, Section 5, `defphase` and lines 1584–1601. -/
noncomputable def arbitraryPhysicalEndpointParentInteraction
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (right : Bool) :
    MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2 :=
  if right then LinearMap.toMatrix' (parentInteraction
    (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2)
  else LinearMap.toMatrix' (parentInteraction
    (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2)

/-- The affine attachment from either actual limiting interaction to the
canonical parent of the corresponding embedded original tensor. Source:
arXiv:2203.12563, Section 5, lines 1328–1331 and 1690–1692. -/
noncomputable def arbitraryPhysicalEndpointAttachment
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (right : Bool) (t : ℝ) :
    MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2 :=
  let h := arbitraryPhysicalMixedInteraction A₀ A₁ (if right then 1 else 0)
  h + t • (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right - h)

/-- At parameter zero the attachment is the actual limiting interaction.
Source: arXiv:2203.12563, Section 5, lines 1328–1331. -/
@[simp] theorem arbitraryPhysicalEndpointAttachment_zero
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (right : Bool) :
    arbitraryPhysicalEndpointAttachment A₀ A₁ right 0 =
      arbitraryPhysicalMixedInteraction A₀ A₁ (if right then 1 else 0) := by
  simp [arbitraryPhysicalEndpointAttachment]

/-- At parameter one the attachment is exactly the prescribed canonical
parent. Source: arXiv:2203.12563, Section 5, lines 1328–1331. -/
@[simp] theorem arbitraryPhysicalEndpointAttachment_one
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (right : Bool) :
    arbitraryPhysicalEndpointAttachment A₀ A₁ right 1 =
      arbitraryPhysicalEndpointParentInteraction A₀ A₁ right := by
  simp [arbitraryPhysicalEndpointAttachment]

/-- The attachment is continuous as a function of its local interaction.
Source: arXiv:2203.12563, Section 5, lines 1328–1331. -/
theorem continuous_arbitraryPhysicalEndpointAttachment
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (right : Bool) :
    Continuous (arbitraryPhysicalEndpointAttachment A₀ A₁ right) := by
  unfold arbitraryPhysicalEndpointAttachment
  fun_prop

private theorem arbitraryPhysicalMixedInteraction_endpoint_le_parent
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) (right : Bool) :
    arbitraryPhysicalMixedInteraction A₀ A₁ (if right then 1 else 0) ≤
      arbitraryPhysicalEndpointParentInteraction A₀ A₁ right := by
  cases right
  · exact arbitraryPhysicalMixedInteraction_zero_le_parent A₀ A₁ h₀
  · exact arbitraryPhysicalMixedInteraction_one_le_parent A₀ A₁ h₁

/-- Every local interaction in the attachment is positive. Source:
arXiv:2203.12563, Section 5, lines 1328–1331. -/
theorem arbitraryPhysicalEndpointAttachment_posSemidef
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (arbitraryPhysicalEndpointAttachment A₀ A₁ right t).PosSemidef :=
  (arbitraryPhysicalMixedInteraction_posSemidef A₀ A₁ _).add
    ((Matrix.le_iff.mp
      (arbitraryPhysicalMixedInteraction_endpoint_le_parent A₀ A₁ h₀ h₁ right)).smul ht)

/-- The affine attachment has interaction strength at most one throughout
the unit interval. Source: arXiv:2203.12563, Section 5, the local gapped
Hamiltonian path in `defphase`. -/
theorem arbitraryPhysicalEndpointAttachment_norm_le_one
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖arbitraryPhysicalEndpointAttachment A₀ A₁ right t‖ ≤ 1 := by
  have hle : arbitraryPhysicalEndpointAttachment A₀ A₁ right t ≤
      arbitraryPhysicalEndpointParentInteraction A₀ A₁ right := by
    rw [Matrix.le_iff]
    convert (Matrix.le_iff.mp
      (arbitraryPhysicalMixedInteraction_endpoint_le_parent A₀ A₁ h₀ h₁ right)).smul
        (sub_nonneg.mpr ht.2) using 1 <;>
      dsimp only [arbitraryPhysicalEndpointAttachment] <;> module
  have hnorm := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
    (arbitraryPhysicalEndpointAttachment_posSemidef A₀ A₁ h₀ h₁ right ht.1).nonneg
  apply hnorm.trans
  cases right <;> exact parentInteraction_toMatrix'_norm_le_one _ 2

/-- The periodic kernels of the actual limiting interaction and the
canonical parent of the embedded original tensor agree. The equality is
derived from their exact MPS lines. Source: arXiv:2203.12563, Section 5,
lines 1328–1331 and 1690–1692. -/
theorem arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalMixedInteraction A₀ A₁ (if right then 1 else 0)) hN)) =
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right) hN)) := by
  have hline := arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv
    A₀ A₁ h₀ h₁ (if right then (1 : unitInterval) else 0) hN
  cases right
  · rw [arbitraryPhysicalEndpointParentInteraction, Bool.false_eq_true, if_false,
      interactionHamiltonian_parent_groundSpace_eq_span_mpv _
        (isInjective_kraus_isometry _ _
          (commonPhysicalEmbeddingLeft_isometry d₁ D₁ h₀) h₀) hN]
    simpa only [Bool.false_eq_true, if_false, Set.Icc.coe_zero,
      mpv_arbitraryPhysicalMixedInterpolation_zero A₀ A₁ h₀ (by omega)] using hline
  · rw [arbitraryPhysicalEndpointParentInteraction, if_true,
      interactionHamiltonian_parent_groundSpace_eq_span_mpv _
        (isInjective_kraus_isometry _ _
          (commonPhysicalEmbeddingRight_isometry d₀ D₀ h₁) h₁) hN]
    simpa only [if_true, Set.Icc.coe_one,
      mpv_arbitraryPhysicalMixedInterpolation_one A₀ A₁ h₁ (by omega)] using hline

/-- Each affine attachment has precisely the periodic ground line of its
embedded original tensor, expressed as the kernel of that canonical parent.
Source: arXiv:2203.12563, Section 5, lines 1328–1331 and 1690–1692. -/
theorem arbitraryPhysicalEndpointAttachment_ker_eq_parent
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : 0 ≤ t) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN)) =
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointParentInteraction A₀ A₁ right) hN)) := by
  have hker := arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent A₀ A₁ h₀ h₁ right hN
  exact (interactionHamiltonian_affine_ker_eq_of_order _ _
    (arbitraryPhysicalMixedInteraction_posSemidef A₀ A₁ _)
    (arbitraryPhysicalMixedInteraction_endpoint_le_parent A₀ A₁ h₀ h₁ right)
    hN hker.le t ht).trans hker

/-- The exact ground line along either attachment is the periodic vector
of the corresponding embedded original tensor. Source: arXiv:2203.12563,
Section 5, lines 1328–1331 and 1690–1692. -/
theorem arbitraryPhysicalEndpointAttachment_groundSpace_eq_span_mpv
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : 0 ≤ t) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2
        (if right then mpv (N := N)
          (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁)
        else mpv (N := N)
          (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀)))} := by
  rw [arbitraryPhysicalEndpointAttachment_ker_eq_parent A₀ A₁ h₀ h₁ right ht hN]
  cases right
  · exact interactionHamiltonian_parent_groundSpace_eq_span_mpv _
      (isInjective_kraus_isometry _ _
        (commonPhysicalEmbeddingLeft_isometry d₁ D₁ h₀) h₀) hN
  · exact interactionHamiltonian_parent_groundSpace_eq_span_mpv _
      (isInjective_kraus_isometry _ _
        (commonPhysicalEmbeddingRight_isometry d₀ D₀ h₁) h₁) hN

/-- The periodic ground space of each attachment is one-dimensional,
including the smallest two-site ring. Source: arXiv:2203.12563,
Section 5, lines 1328–1331 and 1690–1692. -/
theorem arbitraryPhysicalEndpointAttachment_groundSpace_finrank
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (right : Bool) {t : ℝ} (ht : 0 ≤ t) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN))) = 1 := by
  rw [arbitraryPhysicalEndpointAttachment_ker_eq_parent A₀ A₁ h₀ h₁ right ht hN,
    ← arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent A₀ A₁ h₀ h₁ right hN]
  simpa only [apply_ite, Set.Icc.coe_zero, Set.Icc.coe_one] using
    arbitraryPhysicalMixedInteraction_groundSpace_finrank A₀ A₁ h₀ h₁
      (if right then (1 : unitInterval) else 0) hN

/-- One positive gap works for both canonical-parent attachments, all
parameters in the unit interval, and all rings of length at least two.
Neither an endpoint gap nor a kernel equality is a premise. Source:
arXiv:2203.12563, Section 5, lines 1328–1331 and 1690–1692. -/
theorem exists_uniform_arbitraryPhysicalEndpointAttachment_gap
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ right : Bool, ∀ t : unitInterval,
      ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (interactionHamiltonian
          (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN) v‖ := by
  obtain ⟨δ, hδ, hδone, hgap⟩ :=
    exists_uniform_arbitraryPhysicalMixed_periodic_path_gap A₀ A₁ h₀ h₁
  refine ⟨δ, hδ, hδone, ?_⟩
  intro right t N hN
  apply interactionHamiltonian_affine_norm_gap_of_order _ _
    (arbitraryPhysicalMixedInteraction_posSemidef A₀ A₁ _)
    (arbitraryPhysicalMixedInteraction_endpoint_le_parent A₀ A₁ h₀ h₁ right) hN
    (arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent A₀ A₁ h₀ h₁ right hN).le
    hδ.le _ t t.property.1
  simpa only [apply_ite, Set.Icc.coe_zero, Set.Icc.coe_one] using
    hgap (if right then (1 : unitInterval) else 0) N hN

end MPOSymmetry
end MPSTensor
