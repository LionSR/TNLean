/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CommonPhysicalFixedPointGroundPath
import TNLean.MPS.Symmetry.ExactMPSGroundPathComposition
import TNLean.Algebra.CommonKernelGapInterpolation

/-!
# Exact MPS ground states along the canonical fixed-point path

The ordered affine comparisons preserve the endpoint ground lines. Their
constant tensor representatives therefore join the weighted bond family
without changing its endpoint tensors. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma` and `eq:1d-sym:jointsym`.

**Scope restriction (fixed-point constructors):** The common physical
fixed-point constructors below use trivial endpoint characters, as recorded
in `docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- Ordered affine interaction comparison preserves the smaller kernel
when that kernel annihilates the larger interaction. Source context:
arXiv:1010.3732, Section II.F.2, the parent-interaction comparison. -/
theorem interactionHamiltonian_affine_ker_eq_of_order {d N : ℕ}
    (A B : MPOTensor.ChainOperator d 2) (hA : A.PosSemidef) (hAB : A ≤ B)
    (hN : 2 ≤ N)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian B hN)))
    (t : ℝ) (ht : 0 ≤ t) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (A + t • (B - A)) hN)) =
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) := by
  have hHA := interactionHamiltonian_posSemidef hA hN
  have hAB' := interactionHamiltonian_mono hAB hN
  have hker' : ∀ x, (interactionHamiltonian A hN).mulVec x = 0 →
      (interactionHamiltonian B hN).mulVec x = 0 := by
    intro x hx
    have hxES : WithLp.toLp 2 x ∈ LinearMap.ker
        (Matrix.toEuclideanLin (interactionHamiltonian A hN)) := by
      change WithLp.toLp 2 ((interactionHamiltonian A hN).mulVec x) = 0
      simp [hx]
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, WithLp.toLp_eq_zero] using hker hxES
  have h := Matrix.gap_interpolation_of_le
    (interactionHamiltonian A hN) (interactionHamiltonian B hN)
    hHA hAB' hker' 0 t ht
    (fun x _ => by simpa only [zero_mul, RCLike.re_eq_complex_re] using
      (RCLike.nonneg_iff.mp (hHA.dotProduct_mulVec_nonneg x.ofLp)).1)
  rw [interactionHamiltonian_add_smul_sub]
  exact h.2.1

/-- A constant MPS representative realizes an ordered affine comparison
whose kernel is the prescribed zero-energy MPS line. Source context:
arXiv:1010.3732, Section II.F.2, the parent-interaction comparison. -/
noncomputable def ExactMPSGroundPath.of_ordered_affine
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ A B : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    (Q : ExactMPSGroundPath P) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (R : SymmetricGappedInteractionPath U A B)
    (hR : ∀ t, R.interaction t = A + t • (B - A))
    (hA : A.PosSemidef) (hAB : A ≤ B)
    (hker : ∀ (N : ℕ) (hN : 2 ≤ N),
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian B hN)))
    (hzero : ∀ (N : ℕ) (hN : 2 ≤ N),
      (0 : ℂ) ∈ spectrum ℂ (interactionHamiltonian A hN))
    (hline : ∀ (N : ℕ) (hN : 2 ≤ N),
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := N) (Q.tensor γ)))}) :
    ExactMPSGroundPath R where
  bondDimension := Q.bondDimension
  bondDimension_pos := Q.bondDimension_pos
  tensor _ := Q.tensor γ
  continuous := continuous_const.continuousOn
  injective_representative _ _ := Q.injective_representative γ hγ
  nonzero _ _ := Q.nonzero γ hγ
  ground_line := by
    intro t ht N hN
    rw [hR t]
    have hkerEq := interactionHamiltonian_affine_ker_eq_of_order
      A B hA hAB hN (hker N hN) t ht.1
    have hz : (0 : ℂ) ∈ spectrum ℂ
        (interactionHamiltonian (A + t • (B - A)) hN) := by
      have hzA := hzero N hN
      rw [← Matrix.spectrum_toLpLin (p := 2),
        ← Module.End.hasEigenvalue_iff_mem_spectrum,
        Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero] at hzA ⊢
      change LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (A + t • (B - A)) hN)) ≠ ⊥
      rw [hkerEq]
      exact hzA
    refine ⟨0, hz, ?_, ?_⟩
    · have hpos := interactionHamiltonian_posSemidef
        (hA.add ((Matrix.le_iff.mp hAB).smul ht.1)) hN
      intro z hz
      have hznonneg : (0 : ℂ) ≤ z :=
        (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpos).2 hz
      simpa only [RCLike.re_eq_complex_re] using (RCLike.nonneg_iff.mp hznonneg).1
    · simpa only [Complex.ofReal_zero, zero_smul, sub_zero,
        WithLp.coe_symm_linearEquiv] using hkerEq.trans (hline N hN)

/-- The ordered comparison with an embedded canonical parent has the
constant weighted MPS ground line of its initial bond interaction.
Source: arXiv:1010.3732, Section II.F.2, the parent-interaction comparison. -/
noncomputable def commonPhysicalBondCanonicalParentComparisonExactMPSGroundPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ R : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) (γ : ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) R)
    (horder : normalizedBondInteraction D₀ D₁ γ ≤
      LinearMap.toMatrix' (parentInteraction B 2))
    (hker : ∀ (N : ℕ) (hN : 2 ≤ N),
      LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) ≤
        LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
          (LinearMap.toMatrix' (parentInteraction B 2)) hN)))
    (hCov : ∀ g, GaugeEquiv B
      (rotatePhysical (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g) B)) :
    ExactMPSGroundPath (commonPhysicalBondCanonicalParentComparisonPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ γ B horder hker hCov) :=
  ExactMPSGroundPath.of_ordered_affine
    (commonPhysicalNormalizedBondExactMPSGroundPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁) γ hγ
    (commonPhysicalBondCanonicalParentComparisonPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ γ B horder hker hCov)
    (fun _ => rfl)
    (Matrix.nonneg_iff_posSemidef.mp
      (commonPhysicalNormalizedBondInteraction_isStarProjection hD₀ hD₁ d₀ d₁ γ).nonneg)
    (commonPhysicalNormalizedBondInteraction_le_parent d₀ d₁ γ B horder)
    (fun N hN => commonPhysicalNormalizedBondInteraction_ker_le_parent
      hD₀ hD₁ d₀ d₁ γ hN B (hker N hN))
    (fun _N hN => commonPhysicalNormalizedBondInteraction_zero_mem_spectrum hD₀ hD₁ d₀ d₁ γ hN)
    (fun _N hN => commonPhysicalNormalizedBondInteraction_groundSpace_eq_span_mpv
      hD₀ hD₁ d₀ d₁ γ hN)

/-- The affine comparison at the first endpoint has the constant included
weighted tensor as its exact ground-state representative. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def commonPhysicalLeftParentComparisonExactMPSGroundPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    ExactMPSGroundPath (commonPhysicalLeftParentComparisonPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁) :=
  commonPhysicalBondCanonicalParentComparisonExactMPSGroundPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ 0
    ⟨le_rfl, zero_le_one⟩
    (embeddedSptFixedPointLeft D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 0 _
      (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
      (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
      (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁))
    (fun N hN => ker_interactionHamiltonian_normalizedBondInteraction_le_parent_of_mpv_eq
      hD₀ hD₁ 0 hN _ (mpv_embeddedSptFixedPointLeft (by omega)))
    (fun g => ⟨sptGauge ρ₀ g, twistedTensor_embeddedSptFixedPointLeft ρ₀ ρ₁ g⟩)

/-- The affine comparison at the second endpoint has the constant included
weighted tensor as its exact ground-state representative. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def commonPhysicalRightParentComparisonExactMPSGroundPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    ExactMPSGroundPath (commonPhysicalRightParentComparisonPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁) :=
  commonPhysicalBondCanonicalParentComparisonExactMPSGroundPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ 1
    ⟨zero_le_one, le_rfl⟩
    (embeddedSptFixedPointRight D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 1 _
      (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
      (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
      (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁))
    (fun N hN => ker_interactionHamiltonian_normalizedBondInteraction_le_parent_of_mpv_eq
      hD₀ hD₁ 1 hN _ (mpv_embeddedSptFixedPointRight (by omega)))
    (fun g => ⟨sptGauge ρ₁ g, twistedTensor_embeddedSptFixedPointRight ρ₀ ρ₁ g⟩)

/-- The initial tensor of concatenated exact ground families is the
corresponding endpoint tensor. Source context: arXiv:1010.3732, Section II.C. -/
theorem ExactMPSGroundPath.trans_tensor_zero
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    (Q : ExactMPSGroundPath P) (S : ExactMPSGroundPath R)
    (hD : Q.bondDimension = S.bondDimension)
    (hTensor : HEq (Q.tensor 1) (S.tensor 0)) :
    HEq ((Q.trans S hD hTensor).tensor 0) (Q.tensor 0) := by
  rcases Q with ⟨D, hDpos, A, hA, hInjA, hneA, hLineA⟩
  rcases S with ⟨D', hDpos', B, hB, hInjB, hneB, hLineB⟩
  dsimp only at hD hTensor
  subst D'
  exact heq_of_eq (Path.extend_zero _)

/-- The final tensor of concatenated exact ground families is the
corresponding endpoint tensor. Source context: arXiv:1010.3732, Section II.C. -/
theorem ExactMPSGroundPath.trans_tensor_one
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    (Q : ExactMPSGroundPath P) (S : ExactMPSGroundPath R)
    (hD : Q.bondDimension = S.bondDimension)
    (hTensor : HEq (Q.tensor 1) (S.tensor 0)) :
    HEq ((Q.trans S hD hTensor).tensor 1) (S.tensor 1) := by
  rcases Q with ⟨D, hDpos, A, hA, hInjA, hneA, hLineA⟩
  rcases S with ⟨D', hDpos', B, hB, hInjB, hneB, hLineB⟩
  dsimp only at hD hTensor
  subst D'
  exact heq_of_eq (Path.extend_one _)

/-- The full canonical fixed-point path admits a continuous exact MPS
realization with the common ambient bond dimension. Source:
arXiv:1010.3732, Section II.F.2, `eq:sym:omega-gamma`. -/
noncomputable def commonPhysicalCanonicalFixedPointExactMPSGroundPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    ExactMPSGroundPath (commonPhysicalCanonicalFixedPointGappedPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁) := by
  let L := commonPhysicalLeftParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let M := commonPhysicalNormalizedBondExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let R := commonPhysicalRightParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  have hLM : HEq (L.reverse.tensor 1) (M.tensor 0) := heq_of_eq rfl
  exact (L.reverse.trans M rfl hLM).trans R rfl
    (ExactMPSGroundPath.trans_tensor_one L.reverse M rfl hLM)

/-- The initial tensor of the canonical fixed-point realization is the
included weighted endpoint tensor. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_zero
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    (commonPhysicalCanonicalFixedPointExactMPSGroundPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁).tensor 0 =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0) := by
  let L := commonPhysicalLeftParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let M := commonPhysicalNormalizedBondExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let R := commonPhysicalRightParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  have hLM : HEq (L.reverse.tensor 1) (M.tensor 0) := heq_of_eq rfl
  let LM := L.reverse.trans M rfl hLM
  have hLMR : HEq (LM.tensor 1) (R.tensor 0) :=
    ExactMPSGroundPath.trans_tensor_one L.reverse M rfl hLM
  exact eq_of_heq ((ExactMPSGroundPath.trans_tensor_zero LM R rfl hLMR).trans
    (ExactMPSGroundPath.trans_tensor_zero L.reverse M rfl hLM))

/-- The final tensor of the canonical fixed-point realization is the
included weighted endpoint tensor. Source: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_one
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    (commonPhysicalCanonicalFixedPointExactMPSGroundPath
      ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁).tensor 1 =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1) := by
  let L := commonPhysicalLeftParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let M := commonPhysicalNormalizedBondExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  let R := commonPhysicalRightParentComparisonExactMPSGroundPath
    ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁
  have hLM : HEq (L.reverse.tensor 1) (M.tensor 0) := heq_of_eq rfl
  let LM := L.reverse.trans M rfl hLM
  have hLMR : HEq (LM.tensor 1) (R.tensor 0) :=
    ExactMPSGroundPath.trans_tensor_one L.reverse M rfl hLM
  exact eq_of_heq (ExactMPSGroundPath.trans_tensor_one LM R rfl hLMR)

end MPSTensor
