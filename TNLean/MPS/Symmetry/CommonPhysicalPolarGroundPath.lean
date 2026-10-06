/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Core.IsometricBondCompression
import TNLean.MPS.Symmetry.CommonPhysicalEndpointPaths
import TNLean.MPS.Symmetry.CanonicalInjectiveGroundPath
import TNLean.MPS.Symmetry.ExactMPSPhaseGaugeInvariance

/-!
# Exact ground-state tensors along the common physical polar paths

The polar deformations of the original injective tensors represent the
ground-state lines of their canonical parent interactions. An isometric
inclusion of the bond space preserves all positive-length periodic vectors.
After multiplication by the fixed-point normalization, the two polar
families therefore admit representatives in the common direct-sum bond
space whose fixed-point endpoints are the weighted matrix-unit tensors.

Source: arXiv:1010.3732, Sections II.C and II.F.2,
equations eq:1d-sym:jointsym and eq:sym:omega-gamma.

**Scope restriction (one-site injective tensors and trivial character):**
The two polar ground-state families concern the single-block case with
trivial scalar character, as documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- Inclusion of a tensor into an isometric bond subspace. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
def isometricBondEmbedding {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (A : MPSTensor d D) : MPSTensor d E :=
  fun i => V * A i * Vᴴ

/-- An isometric bond inclusion preserves every positive-length periodic
vector. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:sym:omega-gamma. -/
theorem mpv_isometricBondEmbedding {d D E N : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (A : MPSTensor d D) (hN : 0 < N) (σ : Cfg d N) :
    mpv (isometricBondEmbedding V A) σ = mpv A σ := by
  refine mpv_eq_of_supported_isometric_bond_intertwiner
    (isometricBondEmbedding V A) A V hV (fun i => ?_) (fun i => ?_) hN σ
  all_goals simp only [isometricBondEmbedding, Matrix.mul_assoc,
    ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, Matrix.mul_one]

/-- A fixed isometric bond inclusion acts continuously on tensor families.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:sym:omega-gamma. -/
theorem continuous_isometricBondEmbedding {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) :
    Continuous (isometricBondEmbedding (d := d) V) := by
  unfold isometricBondEmbedding
  fun_prop

/-- A bond inclusion with a fixed off-corner correction chosen to reproduce
the prescribed tensor at parameter zero. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:sym:omega-gamma. -/
def supportedBondLift {d D E : ℕ} (V : Matrix (Fin E) (Fin D) ℂ)
    (A : ℝ → MPSTensor d D) (T : MPSTensor d E) (γ : ℝ) : MPSTensor d E :=
  isometricBondEmbedding V (A γ) + (T - isometricBondEmbedding V (A 0))

/-- The corrected bond lift has its prescribed initial tensor. Source
context: arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
theorem supportedBondLift_zero {d D E : ℕ} (V : Matrix (Fin E) (Fin D) ℂ)
    (A : ℝ → MPSTensor d D) (T : MPSTensor d E) : supportedBondLift V A T 0 = T := by
  simp only [supportedBondLift, ← add_sub_assoc, add_sub_cancel_left]

/-- The corrected lift retains the prescribed bond intertwiner. Source
context: arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
theorem supportedBondLift_intertwine {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (A : ℝ → MPSTensor d D) (T : MPSTensor d E)
    (hT : ∀ i, T i * V = V * A 0 i) (γ : ℝ) (i : Fin d) :
    supportedBondLift V A T γ i * V = V * A γ i := by
  simp only [supportedBondLift, isometricBondEmbedding, Pi.add_apply, Pi.sub_apply,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hV, Matrix.mul_one, hT,
    sub_self, add_zero]

/-- The corrected lift remains supported on its included row space.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:sym:omega-gamma. -/
theorem supportedBondLift_rowSupport {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (A : ℝ → MPSTensor d D) (T : MPSTensor d E)
    (hT : ∀ i, V * Vᴴ * T i = T i) (γ : ℝ) (i : Fin d) :
    V * Vᴴ * supportedBondLift V A T γ i = supportedBondLift V A T γ i := by
  simp only [supportedBondLift, isometricBondEmbedding, Pi.add_apply, Pi.sub_apply,
    Matrix.mul_add, Matrix.mul_sub, hT, Matrix.mul_assoc,
    ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

/-- A supported lift preserves every positive-length periodic vector ray.
Source context: arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
theorem supportedBondLift_samePositiveMpvRay {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (A : ℝ → MPSTensor d D) (T : MPSTensor d E)
    (hInt : ∀ i, T i * V = V * A 0 i)
    (hSupport : ∀ i, V * Vᴴ * T i = T i) (γ : ℝ) :
    SamePositiveMpvRay (supportedBondLift V A T γ) (A γ) := by
  intro N hN
  exact congrArg (fun v : Cfg d N → ℂ => Submodule.span ℂ {v})
    (funext (mpv_eq_of_supported_isometric_bond_intertwiner _ _ V hV
      (supportedBondLift_intertwine V hV A T hInt γ)
      (supportedBondLift_rowSupport V hV A T hSupport γ) hN))

/-- A fixed off-corner correction preserves continuity of a bond lift.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:sym:omega-gamma. -/
theorem continuousOn_supportedBondLift {d D E : ℕ}
    (V : Matrix (Fin E) (Fin D) ℂ) (A : ℝ → MPSTensor d D) (T : MPSTensor d E)
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (supportedBondLift V A T) (Set.Icc (0 : ℝ) 1) := by
  exact ((continuous_isometricBondEmbedding V).comp_continuousOn hA).add continuousOn_const

/-- An isometric bond intertwiner and row support preserve an exact MPS
ground-state realization, including off-corner letters invisible to every
closed positive-length word. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:sym:omega-gamma. -/
noncomputable def ExactMPSGroundPath.of_supported_isometric_bond_intertwiner
    {G : Type} [Group G] {d E : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    (Q : ExactMPSGroundPath P)
    (V : Matrix (Fin E) (Fin Q.bondDimension) ℂ) (hV : Vᴴ * V = 1)
    (B : ℝ → MPSTensor d E) (hB : ContinuousOn B (Set.Icc (0 : ℝ) 1))
    (hInt : ∀ γ i, B γ i * V = V * Q.tensor γ i)
    (hSupport : ∀ γ i, V * Vᴴ * B γ i = B γ i)
    (hDE : Q.bondDimension ≤ E) : ExactMPSGroundPath P where
  bondDimension := E
  bondDimension_pos := lt_of_lt_of_le Q.bondDimension_pos hDE
  tensor := B
  continuous := hB
  injective_representative γ hγ := by
    obtain ⟨D, hD, hle, A, hA, hRay⟩ := Q.injective_representative γ hγ
    refine ⟨D, hD, hle.trans hDE, A, hA, ?_⟩
    exact fun N hN => (congrArg (fun v : Cfg d N → ℂ => Submodule.span ℂ {v})
      (funext (mpv_eq_of_supported_isometric_bond_intertwiner (B γ) (Q.tensor γ)
        V hV (hInt γ) (hSupport γ) hN))).trans (hRay N hN)
  nonzero γ hγ N hN := by
    simpa only [funext (mpv_eq_of_supported_isometric_bond_intertwiner (B γ) (Q.tensor γ)
      V hV (hInt γ) (hSupport γ) hN)]
      using Q.nonzero γ hγ N hN
  ground_line γ hγ N hN := by
    simpa only [funext (mpv_eq_of_supported_isometric_bond_intertwiner (B γ) (Q.tensor γ)
      V hV (hInt γ) (hSupport γ) (by omega : 0 < N))]
      using Q.ground_line γ hγ N hN

/-- A supported bond lift realizes the same exact ground-state lines and
has its prescribed initial tensor. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:sym:omega-gamma. -/
noncomputable def ExactMPSGroundPath.supportedBondLift
    {G : Type} [Group G] {d E : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    (Q : ExactMPSGroundPath P)
    (V : Matrix (Fin E) (Fin Q.bondDimension) ℂ) (hV : Vᴴ * V = 1)
    (T : MPSTensor d E) (hInt : ∀ i, T i * V = V * Q.tensor 0 i)
    (hSupport : ∀ i, V * Vᴴ * T i = T i)
    (hDE : Q.bondDimension ≤ E) : ExactMPSGroundPath P :=
  Q.of_supported_isometric_bond_intertwiner V hV
    (MPSTensor.supportedBondLift V Q.tensor T)
    (continuousOn_supportedBondLift V Q.tensor T Q.continuous)
    (supportedBondLift_intertwine V hV Q.tensor T hInt)
    (supportedBondLift_rowSupport V hV Q.tensor T hSupport) hDE

private theorem rotatePhysical_bond_intertwiner {d m D E : ℕ}
    (Q : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hInt : ∀ i, A i * V = V * B i) (j : Fin m) :
    rotatePhysical Q A j * V = V * rotatePhysical Q B j := by
  simp only [rotatePhysical, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, hInt]

private theorem rotatePhysical_bond_rowSupport {d m D E : ℕ}
    (Q : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D)
    (V : Matrix (Fin D) (Fin E) ℂ) (hSupport : ∀ i, V * Vᴴ * A i = A i) (j : Fin m) :
    V * Vᴴ * rotatePhysical Q A j = rotatePhysical Q A j := by
  simp only [rotatePhysical, Matrix.mul_sum, Matrix.mul_smul, hSupport]

private noncomputable def scaledEmbeddedPolarGroundPath
    {G : Type} [Group G] {d m D : ℕ} [NeZero D]
    {U : G →* Matrix.unitaryGroup (Fin m) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator m 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hP : ∀ γ ∈ Set.Icc (0 : ℝ) 1, P.interaction γ =
      LinearMap.toMatrix' (parentInteraction (rotatePhysical E (polarDeformation A γ)) 2)) :
    ExactMPSGroundPath P := by
  refine exactMPSGroundPath_of_canonicalInjective P
    (fun γ => sptScale D • rotatePhysical E (polarDeformation A γ)) ?_ ?_ ?_
  · exact ((continuous_rotatePhysical E).comp_continuousOn
      (continuous_polarDeformation A).continuousOn).const_smul (sptScale D)
  · exact fun γ hγ => (isInjective_kraus_isometry (polarDeformation A γ) E hE
      (isInjective_polarDeformation hA hγ)).smul (sptScale_ne_zero (D := D))
  · exact fun γ hγ => (hP γ hγ).trans (congrArg LinearMap.toMatrix'
      (parentInteraction_eq_of_groundSpace_eq
        (groundSpace_smul_eq (rotatePhysical E (polarDeformation A γ))
          (sptScale D) (sptScale_ne_zero (D := D)) 2).symm))

private theorem commonLeftPolarEndpoint_bond_intertwiner
    {d₀ D₀ : ℕ} (d₁ D₁ : ℕ) (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (i : Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) :
    rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0) i *
          Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
        (sptScale D₀ • rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A)
          (polarIsometricTensor A)) i := by
  rw [sptScale_smul_commonPhysicalEmbeddingLeft_polar_endpoint d₁ D₁ hA]
  exact rotatePhysical_bond_intertwiner _ _ _ _
    (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁) i

private theorem commonRightPolarEndpoint_bond_intertwiner
    {d₁ D₁ : ℕ} (d₀ D₀ : ℕ) (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (i : Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) :
    rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1) i *
          Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
        (sptScale D₁ • rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A)
          (polarIsometricTensor A)) i := by
  rw [sptScale_smul_commonPhysicalEmbeddingRight_polar_endpoint d₀ D₀ hA]
  exact rotatePhysical_bond_intertwiner _ _ _ _
    (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁) i

private theorem commonWeightedEndpointLeft_bond_rowSupport
    (d₀ d₁ D₀ D₁ : ℕ) (i : Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) :
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
        (Matrix.coordinateInclusion (Fin.castAddEmb D₁))ᴴ *
          rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
            (weightedMatrixUnitInterpolation D₀ D₁ 0) i =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0) i :=
  rotatePhysical_bond_rowSupport _ _ _
    (fun p => Matrix.coordinateInclusion_projection_mul_of_rowSupport _ _
      (weightedMatrixUnitInterpolation_zero_rowSupport D₀ D₁ p)) i

private theorem commonWeightedEndpointRight_bond_rowSupport
    (d₀ d₁ D₀ D₁ : ℕ) (i : Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) :
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
        (Matrix.coordinateInclusion (Fin.natAddEmb D₀))ᴴ *
          rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
            (weightedMatrixUnitInterpolation D₀ D₁ 1) i =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1) i :=
  rotatePhysical_bond_rowSupport _ _ _
    (fun p => Matrix.coordinateInclusion_projection_mul_of_rowSupport _ _
      (weightedMatrixUnitInterpolation_one_rowSupport D₀ D₁ p)) i

private noncomputable def leftSupportedPolarGroundPath
    {G : Type} [Group G] {d₀ D₀ : ℕ} [NeZero D₀] (d₁ D₁ : ℕ)
    {U : G →* Matrix.unitaryGroup
      (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (hP : ∀ γ ∈ Set.Icc (0 : ℝ) 1, P.interaction γ =
      LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) (polarDeformation A γ)) 2)) :
    ExactMPSGroundPath P := by
  let S := scaledEmbeddedPolarGroundPath P (commonPhysicalEmbeddingLeft d₁ D₁ A)
    (commonPhysicalEmbeddingLeft_isometry d₁ D₁ hA) A hA hP
  refine S.supportedBondLift (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
    (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
    (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
      (weightedMatrixUnitInterpolation D₀ D₁ 0)) ?_
    (commonWeightedEndpointLeft_bond_rowSupport d₀ d₁ D₀ D₁) ?_
  · exact fun i => (commonLeftPolarEndpoint_bond_intertwiner d₁ D₁ A hA i).trans
      (congrArg (fun B : MPSTensor d₀ D₀ => Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
        (sptScale D₀ • rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) B) i)
        (polarDeformation_zero A)).symm
  · omega

private noncomputable def rightSupportedPolarGroundPath
    {G : Type} [Group G] {d₁ D₁ : ℕ} [NeZero D₁] (d₀ D₀ : ℕ)
    {U : G →* Matrix.unitaryGroup
      (Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁)) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (hP : ∀ γ ∈ Set.Icc (0 : ℝ) 1, P.interaction γ =
      LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) (polarDeformation A γ)) 2)) :
    ExactMPSGroundPath P := by
  let S := scaledEmbeddedPolarGroundPath P (commonPhysicalEmbeddingRight d₀ D₀ A)
    (commonPhysicalEmbeddingRight_isometry d₀ D₀ hA) A hA hP
  exact S.supportedBondLift (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
    (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
    (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
      (weightedMatrixUnitInterpolation D₀ D₁ 1))
    (fun i => (commonRightPolarEndpoint_bond_intertwiner d₀ D₀ A hA i).trans
      (congrArg (fun B : MPSTensor d₁ D₁ => Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
        (sptScale D₁ • rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) B) i)
        (polarDeformation_zero A)).symm)
    (commonWeightedEndpointRight_bond_rowSupport d₀ d₁ D₀ D₁) (Nat.le_add_left _ _)

/-- The left polar deformation admits a continuous exact ground-state
family in the common bond space, retaining the off-corner letters of its
weighted fixed-point endpoint. Source: arXiv:1010.3732, Sections II.C and
II.F.2, equation eq:sym:omega-gamma. -/
noncomputable def commonPhysicalLeftPolarExactMPSGroundPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₀ g) A =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ) :
    ExactMPSGroundPath
      (commonPhysicalLeftPolarGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov) :=
  leftSupportedPolarGroundPath d₁ D₁
    (commonPhysicalLeftPolarGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov) A hA
    (fun _ _ => by rfl)

/-- The right polar deformation admits a continuous exact ground-state
family in the common bond space, retaining the off-corner letters of its
weighted fixed-point endpoint. Source: arXiv:1010.3732, Sections II.C and
II.F.2, equation eq:sym:omega-gamma. -/
noncomputable def commonPhysicalRightPolarExactMPSGroundPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₁ g) A =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    ExactMPSGroundPath
      (commonPhysicalRightPolarGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov) :=
  rightSupportedPolarGroundPath d₀ D₀
    (commonPhysicalRightPolarGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov) A hA
    (fun _ _ => by rfl)

/-- The fixed-point endpoint is the included weighted matrix-unit tensor.
Source: arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
theorem commonPhysicalLeftPolarExactMPSGroundPath_tensor_zero
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₀ g) A =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ) :
    (commonPhysicalLeftPolarExactMPSGroundPath
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov).tensor 0 =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0) := by
  change supportedBondLift _ _ _ 0 = _
  exact supportedBondLift_zero _ _ _

/-- The original endpoint represents the same periodic ground-state line
as the actual physically included tensor. Source: arXiv:1010.3732,
Sections II.C and II.F.2, equation eq:sym:omega-gamma. -/
theorem commonPhysicalLeftPolarExactMPSGroundPath_samePositiveMpvRay_one
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₀ D₀) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₀ g) A =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ) :
    SamePositiveMpvRay
      ((commonPhysicalLeftPolarExactMPSGroundPath
        ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov).tensor 1)
      (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) A) := by
  change SamePositiveMpvRay
    (supportedBondLift (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
      (fun γ => sptScale D₀ •
        rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) (polarDeformation A γ))
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0)) 1)
    (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) A)
  refine SamePositiveMpvRay.trans
    (B := sptScale D₀ • rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) A) ?_
    (samePositiveMpvRay_of_smul_gaugeEquiv (sptScale D₀)
      (sptScale_ne_zero (D := D₀)) (GaugeEquiv.refl _)).symm
  have hInt : ∀ i,
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0)) i *
        Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
        (sptScale D₀ •
          rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) (polarDeformation A 0)) i :=
    fun i => (commonLeftPolarEndpoint_bond_intertwiner d₁ D₁ A hA i).trans
      (congrArg (fun B : MPSTensor d₀ D₀ => Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
        (sptScale D₀ • rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) B) i)
        (polarDeformation_zero A)).symm
  simpa only [polarDeformation_one] using
    supportedBondLift_samePositiveMpvRay (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
      (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
      (fun γ => sptScale D₀ •
        rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A) (polarDeformation A γ))
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 0)) hInt
      (commonWeightedEndpointLeft_bond_rowSupport d₀ d₁ D₀ D₁) 1

/-- The fixed-point endpoint is the included weighted matrix-unit tensor.
Source: arXiv:1010.3732, Section II.F.2, equation eq:sym:omega-gamma. -/
theorem commonPhysicalRightPolarExactMPSGroundPath_tensor_zero
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₁ g) A =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    (commonPhysicalRightPolarExactMPSGroundPath
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov).tensor 0 =
      rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1) := by
  change supportedBondLift _ _ _ 0 = _
  exact supportedBondLift_zero _ _ _

/-- The original endpoint represents the same periodic ground-state line
as the actual physically included tensor. Source: arXiv:1010.3732,
Sections II.C and II.F.2, equation eq:sym:omega-gamma. -/
theorem commonPhysicalRightPolarExactMPSGroundPath_samePositiveMpvRay_one
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A : MPSTensor d₁ D₁) (hA : Kraus.IsInjective A)
    (hCov : ∀ g, rotatePhysical (U₁ g) A =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    SamePositiveMpvRay
      ((commonPhysicalRightPolarExactMPSGroundPath
        ρ₀ ρ₁ h₀ h₁ U₀ U₁ A hA hCov).tensor 1)
      (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) A) := by
  change SamePositiveMpvRay
    (supportedBondLift (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
      (fun γ => sptScale D₁ •
        rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) (polarDeformation A γ))
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1)) 1)
    (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) A)
  refine SamePositiveMpvRay.trans
    (B := sptScale D₁ • rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) A) ?_
    (samePositiveMpvRay_of_smul_gaugeEquiv (sptScale D₁)
      (sptScale_ne_zero (D := D₁)) (GaugeEquiv.refl _)).symm
  have hInt : ∀ i,
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1)) i *
        Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
        (sptScale D₁ •
          rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) (polarDeformation A 0)) i :=
    fun i => (commonRightPolarEndpoint_bond_intertwiner d₀ D₀ A hA i).trans
      (congrArg (fun B : MPSTensor d₁ D₁ => Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
        (sptScale D₁ • rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) B) i)
        (polarDeformation_zero A)).symm
  simpa only [polarDeformation_one] using
    supportedBondLift_samePositiveMpvRay (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
      (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
      (fun γ => sptScale D₁ •
        rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A) (polarDeformation A γ))
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (weightedMatrixUnitInterpolation D₀ D₁ 1)) hInt
      (commonWeightedEndpointRight_bond_rowSupport d₀ d₁ D₀ D₁) 1

end MPSTensor
