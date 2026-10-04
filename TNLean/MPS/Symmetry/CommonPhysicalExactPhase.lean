/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Symmetry.PolarVirtualCohomology
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.MPS.Symmetry.PhysicalMatrixBondCovariance
import TNLean.MPS.Symmetry.CommonPhysicalCanonicalGroundPath
import TNLean.MPS.Symmetry.CommonPhysicalInjectivePath
import TNLean.MPS.Symmetry.CommonPhysicalPolarGroundPath
import TNLean.MPS.Symmetry.CommonPhysicalEndpointOrthogonality
import TNLean.MPS.Symmetry.ExactMPSPhaseGaugeInvariance

/-!
# Exact MPS phase paths from common physical embeddings

The forward construction joins the polar deformations and the canonical
fixed-point interpolation in a single physical representation. The whole
original physical spaces have orthogonal isometric images.
Source: arXiv:1010.3732, Sections II.C and II.F.2.

**Scope restriction (one-site injective tensors and trivial character):**
The concrete construction concerns the single-block, one-site injective
case with trivial scalar character, as recorded in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- One-site blocking reindexes the physical matrix by the canonical
one-letter equivalence. Source context: arXiv:1010.3732, Section II.C. -/
theorem blockKron_one_eq_submatrix {m n : ℕ}
    (U : Matrix (Fin m) (Fin n) ℂ) :
    blockKron 1 U = U.submatrix (singleBlockEquiv m) (singleBlockEquiv n) := by
  ext i j
  change (∏ k : Fin 1, U (decodeBlock m 1 i k) (decodeBlock n 1 j k)) = _
  rw [Fin.prod_univ_one]
  rfl

/-- Inclusion after one-site blocking is the original physical inclusion.
Source context: arXiv:1010.3732, Section II.C. -/
theorem rotatePhysical_submatrix_singleBlockEquiv_blockTensor_one {d m D : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) :
    rotatePhysical (E.submatrix id (singleBlockEquiv d)) (blockTensor A 1) =
      rotatePhysical E A := by
  ext i a b
  simp only [rotatePhysical, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, smul_eq_mul, blockTensor, Kraus.blockTensor_one_apply]
  exact
    (Equiv.sum_comp (singleBlockEquiv d) (fun j => E i j * A j a b))

/-- A path between the actual included canonical parents, with exact MPS
endpoint rays and orthogonal physical embeddings, satisfies the independent
phase condition with one-site blocking and trivial endpoint characters.
Source: arXiv:1010.3732, Sections II.C and II.F.2. -/
theorem isSameExactMPSGappedPhase_of_oneSite_path
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ m : ℕ}
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (U : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (E₀ : Matrix (Fin m) (Fin d₀) ℂ) (E₁ : Matrix (Fin m) (Fin d₁) ℂ)
    (hE₀ : E₀ᴴ * E₀ = 1) (hE₁ : E₁ᴴ * E₁ = 1) (horth : E₀ᴴ * E₁ = 0)
    (hCov₀ : ∀ g, (U g : Matrix (Fin m) (Fin m) ℂ) * E₀ =
      E₀ * (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ))
    (hCov₁ : ∀ g, (U g : Matrix (Fin m) (Fin m) ℂ) * E₁ =
      E₁ * (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ))
    (P : SymmetricGappedInteractionPath U
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical E₀ A₀) 2))
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical E₁ A₁) 2)))
    (Q : ExactMPSGroundPath P)
    (hQ₀ : SamePositiveMpvRay (Q.tensor 0) (rotatePhysical E₀ A₀))
    (hQ₁ : SamePositiveMpvRay (Q.tensor 1) (rotatePhysical E₁ A₁)) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  have hGram {a b p q : ℕ} (E : Matrix (Fin m) (Fin a) ℂ)
      (F : Matrix (Fin m) (Fin b) ℂ) (r : Fin p → Fin a) (c : Fin q → Fin b) :
      (E.submatrix id r)ᴴ * F.submatrix id c = (Eᴴ * F).submatrix r c := by
    rw [Matrix.conjTranspose_submatrix]
    exact (Matrix.submatrix_mul Eᴴ F r id c Function.bijective_id).symm
  refine ⟨1, zero_lt_one, m, U, 1, 1, by simp, by simp,
    E₀.submatrix id (singleBlockEquiv d₀), E₁.submatrix id (singleBlockEquiv d₁),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hGram, hE₀, Matrix.submatrix_one_equiv]
  · rw [hGram, hE₁, Matrix.submatrix_one_equiv]
  · rw [hGram, horth]
    rfl
  · intro g
    simp only [MonoidHom.one_apply, one_smul]
    change (U g : Matrix (Fin m) (Fin m) ℂ) * E₀.submatrix id (singleBlockEquiv d₀) =
      E₀.submatrix id (singleBlockEquiv d₀) *
        blockKron 1 (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ)
    rw [blockKron_one_eq_submatrix]
    have hL := Matrix.submatrix_mul_equiv (U g : Matrix (Fin m) (Fin m) ℂ) E₀
      id (Equiv.refl _) (singleBlockEquiv d₀)
    have hR := Matrix.submatrix_mul_equiv E₀ (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ)
      id (singleBlockEquiv d₀) (singleBlockEquiv d₀)
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      hL.trans ((congrArg (fun M => M.submatrix id (singleBlockEquiv d₀))
        (hCov₀ g)).trans hR.symm)
  · intro g
    simp only [MonoidHom.one_apply, one_smul]
    change (U g : Matrix (Fin m) (Fin m) ℂ) * E₁.submatrix id (singleBlockEquiv d₁) =
      E₁.submatrix id (singleBlockEquiv d₁) *
        blockKron 1 (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ)
    rw [blockKron_one_eq_submatrix]
    have hL := Matrix.submatrix_mul_equiv (U g : Matrix (Fin m) (Fin m) ℂ) E₁
      id (Equiv.refl _) (singleBlockEquiv d₁)
    have hR := Matrix.submatrix_mul_equiv E₁ (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ)
      id (singleBlockEquiv d₁) (singleBlockEquiv d₁)
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      hL.trans ((congrArg (fun M => M.submatrix id (singleBlockEquiv d₁))
        (hCov₁ g)).trans hR.symm)
  · rw [rotatePhysical_submatrix_singleBlockEquiv_blockTensor_one,
      rotatePhysical_submatrix_singleBlockEquiv_blockTensor_one]
    exact ⟨P, Q, hQ₀, hQ₁⟩

/-- For a unitary virtual action, inverse conjugation is adjoint
conjugation in the original physical coordinates. Source context:
arXiv:1010.3732, Section II.F.2, lines 886–929. -/
theorem rotatePhysical_covariance_of_unitary_virtual_action
    {G : Type} [Group G] {d D : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hUnitary : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (A : MPSTensor d D)
    (hρ : ∀ g i, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ g, rotatePhysical (U g) A =
      fun i => (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  intro g
  funext i
  change twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i = _
  rw [hρ g i, Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hUnitary g⁻¹)]

/-- An actual virtual implementation of an injective physical symmetry
admits a gauge-equivalent nonzero rescaling with a unitary virtual action
in the same cohomology class. Source: arXiv:1010.3732, Sections II.C and
II.F.2, the preparation preceding the fixed-point interpolation. -/
theorem exists_unitary_covariant_preparation_with_virtual_class
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    {ωA : TNLean.Algebra.ScalarCocycle G}
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ρA : TNLean.Algebra.ProjectiveRepresentation (D := D) ωA)
    (hρA : ∀ g i, twistedTensor A
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g i =
      (ρA.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρA.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ (B : MPSTensor d D) (c : ℂ) (ωB : TNLean.Algebra.ScalarCocycle G)
      (ρB : TNLean.Algebra.ProjectiveRepresentation (D := D) ωB),
      c ≠ 0 ∧ GaugeEquiv (c • A) B ∧ Kraus.IsInjective B ∧
      ωB.CohomologousTo ωA ∧
      (∀ g, (ρB.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      ∀ g, rotatePhysical (U g) B =
        fun i => (sptGauge ρB g : Matrix (Fin D) (Fin D) ℂ) * B i *
          (sptGauge ρB g : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) :=
    fun g => GaugeEquiv.sameMPV ⟨ρA.X (g⁻¹), hρA g⟩
  obtain ⟨B, c, ωB, ρB, hc, hGauge, hB, _, _, hClass, hUnitary, hPolar, _⟩ :=
    exists_prepared_polarGappedInteractionPath_with_virtual_class A hA U hSym ρA hρA
  refine ⟨B, c, ωB, ρB, hc, hGauge, hB, hClass, hUnitary, ?_⟩
  exact rotatePhysical_covariance_of_unitary_virtual_action ρB hUnitary U B
    (fun g i => by simpa using hPolar 1 g i)

/-- Concatenation retains the first family's common ambient bond dimension.
Source context: arXiv:1010.3732, Section II.C. -/
theorem ExactMPSGroundPath.trans_bondDimension
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    (Q : ExactMPSGroundPath P) (S : ExactMPSGroundPath R)
    (hD : Q.bondDimension = S.bondDimension)
    (hTensor : HEq (Q.tensor 1) (S.tensor 0)) :
    (Q.trans S hD hTensor).bondDimension = Q.bondDimension := by
  rcases Q with ⟨D, hDpos, A, hA, hInjA, hneA, hLineA⟩
  rcases S with ⟨D', hDpos', B, hB, hInjB, hneB, hLineB⟩
  dsimp only at hD hTensor
  subst D'
  rfl

/-- Three exact ground-state families concatenate across literal tensor
junctions, with the first physical path reversed. Source context:
arXiv:1010.3732, Section II.F.2, the polar and fixed-point interpolation. -/
noncomputable def ExactMPSGroundPath.reverseTransTrans
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ h₃ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₁ h₀}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    {S : SymmetricGappedInteractionPath U h₂ h₃}
    (L : ExactMPSGroundPath P) (M : ExactMPSGroundPath R) (T : ExactMPSGroundPath S)
    (hDLM : L.bondDimension = M.bondDimension)
    (hDMT : M.bondDimension = T.bondDimension)
    (hLM : HEq (L.tensor 0) (M.tensor 0)) (hMT : HEq (M.tensor 1) (T.tensor 0)) :
    ExactMPSGroundPath ((P.reverse.trans R).trans S) := by
  have hLM' : HEq (L.reverse.tensor 1) (M.tensor 0) := by
    simpa only [ExactMPSGroundPath.reverse, sub_self] using hLM
  exact (L.reverse.trans M hDLM hLM').trans T
    ((ExactMPSGroundPath.trans_bondDimension L.reverse M hDLM hLM').trans (hDLM.trans hDMT))
    ((ExactMPSGroundPath.trans_tensor_one L.reverse M hDLM hLM').trans hMT)

/-- The initial tensor of the three-stage exact family is the
corresponding original endpoint tensor. Source context:
arXiv:1010.3732, Section II.F.2. -/
theorem ExactMPSGroundPath.reverseTransTrans_tensor_zero
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ h₃ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₁ h₀}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    {S : SymmetricGappedInteractionPath U h₂ h₃}
    (L : ExactMPSGroundPath P) (M : ExactMPSGroundPath R) (T : ExactMPSGroundPath S)
    (hDLM : L.bondDimension = M.bondDimension)
    (hDMT : M.bondDimension = T.bondDimension)
    (hLM : HEq (L.tensor 0) (M.tensor 0)) (hMT : HEq (M.tensor 1) (T.tensor 0)) :
    HEq ((L.reverseTransTrans M T hDLM hDMT hLM hMT).tensor 0)
      (L.tensor 1) := by
  have hLM' : HEq (L.reverse.tensor 1) (M.tensor 0) := by
    simpa only [ExactMPSGroundPath.reverse, sub_self] using hLM
  let LM := L.reverse.trans M hDLM hLM'
  have hD : LM.bondDimension = T.bondDimension :=
    (ExactMPSGroundPath.trans_bondDimension L.reverse M hDLM hLM').trans (hDLM.trans hDMT)
  have hJoin : HEq (LM.tensor 1) (T.tensor 0) :=
    (ExactMPSGroundPath.trans_tensor_one L.reverse M hDLM hLM').trans hMT
  have hReverse : HEq (L.reverse.tensor 0) (L.tensor 1) := by
    simp only [ExactMPSGroundPath.reverse, sub_zero]
    rfl
  exact ((ExactMPSGroundPath.trans_tensor_zero LM T hD hJoin).trans
    (ExactMPSGroundPath.trans_tensor_zero L.reverse M hDLM hLM')).trans hReverse

/-- The final tensor of the three-stage exact family is the
corresponding original endpoint tensor. Source context:
arXiv:1010.3732, Section II.F.2. -/
theorem ExactMPSGroundPath.reverseTransTrans_tensor_one
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ h₃ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₁ h₀}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    {S : SymmetricGappedInteractionPath U h₂ h₃}
    (L : ExactMPSGroundPath P) (M : ExactMPSGroundPath R) (T : ExactMPSGroundPath S)
    (hDLM : L.bondDimension = M.bondDimension)
    (hDMT : M.bondDimension = T.bondDimension)
    (hLM : HEq (L.tensor 0) (M.tensor 0)) (hMT : HEq (M.tensor 1) (T.tensor 0)) :
    HEq ((L.reverseTransTrans M T hDLM hDMT hLM hMT).tensor 1)
      (T.tensor 1) := by
  have hLM' : HEq (L.reverse.tensor 1) (M.tensor 0) := by
    simpa only [ExactMPSGroundPath.reverse, sub_self] using hLM
  let LM := L.reverse.trans M hDLM hLM'
  have hD : LM.bondDimension = T.bondDimension :=
    (ExactMPSGroundPath.trans_bondDimension L.reverse M hDLM hLM').trans (hDLM.trans hDMT)
  have hJoin : HEq (LM.tensor 1) (T.tensor 0) :=
    (ExactMPSGroundPath.trans_tensor_one L.reverse M hDLM hLM').trans hMT
  exact ExactMPSGroundPath.trans_tensor_one LM T hD hJoin

/-- An exact ground-state family on the concrete common physical path,
with the original endpoint rays, gives the independent one-site phase
condition. Its physical intertwiners follow from the original tensor
covariances. Source: arXiv:1010.3732, Sections II.C and II.F.2. -/
private theorem isSameExactMPSGappedPhase_of_common_factor_groundPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ)
    (Q : ExactMPSGroundPath (commonPhysicalInjectiveGappedPath
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ A₁ hA₁ hCov₀ hCov₁))
    (hQ₀ : SamePositiveMpvRay (Q.tensor 0)
      (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀))
    (hQ₁ : SamePositiveMpvRay (Q.tensor 1)
      (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁)) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  have hMatrix₀ (g : G) :
      (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ) * physicalMatrix A₀ =
        physicalMatrix A₀ * sptKron (sptGauge ρ₀ g) := by
    exact physicalMatrix_mul_eq_sptKron_of_unitary_covariance
      A₀ (U₀ g) (sptGauge ρ₀ g) (h₀ g⁻¹) (hCov₀ g)
  have hMatrix₁ (g : G) :
      (U₁ g : Matrix (Fin d₁) (Fin d₁) ℂ) * physicalMatrix A₁ =
        physicalMatrix A₁ * sptKron (sptGauge ρ₁ g) := by
    exact physicalMatrix_mul_eq_sptKron_of_unitary_covariance
      A₁ (U₁ g) (sptGauge ρ₁ g) (h₁ g⁻¹) (hCov₁ g)
  exact isSameExactMPSGappedPhase_of_oneSite_path A₀ A₁ U₀ U₁
    (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
    (commonPhysicalEmbeddingLeft d₁ D₁ A₀) (commonPhysicalEmbeddingRight d₀ D₀ A₁)
    (commonPhysicalEmbeddingLeft_isometry d₁ D₁ hA₀)
    (commonPhysicalEmbeddingRight_isometry d₀ D₀ hA₁)
    (commonPhysicalEmbeddingLeft_conjTranspose_mul_right_eq_zero A₀ A₁)
    (fun g => commonPhysicalEmbeddingLeft_intertwiner ρ₀ ρ₁ h₀ h₁ U₀ U₁
      hA₀ g (hMatrix₀ g))
    (fun g => commonPhysicalEmbeddingRight_intertwiner ρ₀ ρ₁ h₀ h₁ U₀ U₁
      hA₁ g (hMatrix₁ g))
    (commonPhysicalInjectiveGappedPath ρ₀ ρ₁ h₀ h₁ U₀ U₁
      A₀ hA₀ A₁ hA₁ hCov₀ hCov₁)
    Q hQ₀ hQ₁

/-- The reversed left polar family, the canonical fixed-point family,
and the right polar family form an exact ground-state certificate for the
actual common physical interaction path. Their tensor junctions are literal
equalities. Source: arXiv:1010.3732, Sections II.C and II.F.2. -/
noncomputable def commonPhysicalInjectiveExactMPSGroundPath
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    ExactMPSGroundPath (commonPhysicalInjectiveGappedPath
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ A₁ hA₁ hCov₀ hCov₁) := by
  let L := commonPhysicalLeftPolarExactMPSGroundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀
  let M := commonPhysicalCanonicalFixedPointExactMPSGroundPath
    ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁
  let R := commonPhysicalRightPolarExactMPSGroundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁
  have hLM : HEq (L.tensor 0) (M.tensor 0) :=
    heq_of_eq ((commonPhysicalLeftPolarExactMPSGroundPath_tensor_zero
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀).trans
        (commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_zero
          ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁).symm)
  have hMR : HEq (M.tensor 1) (R.tensor 0) :=
    heq_of_eq ((commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_one
      ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁).trans
        (commonPhysicalRightPolarExactMPSGroundPath_tensor_zero
          ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁).symm)
  exact L.reverseTransTrans M R rfl rfl hLM hMR

/-- Injective tensors with a common unitary virtual factor and their
original exact physical covariances belong to the same independent exact
MPS gapped phase. Source: arXiv:1010.3732, Section II.F.2. -/
theorem isSameExactMPSGappedPhase_of_unitary_common_factor
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  let L := commonPhysicalLeftPolarExactMPSGroundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀
  let M := commonPhysicalCanonicalFixedPointExactMPSGroundPath
    ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁
  let R := commonPhysicalRightPolarExactMPSGroundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁
  have hLM : HEq (L.tensor 0) (M.tensor 0) :=
    heq_of_eq ((commonPhysicalLeftPolarExactMPSGroundPath_tensor_zero
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀).trans
        (commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_zero
          ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁).symm)
  have hMR : HEq (M.tensor 1) (R.tensor 0) :=
    heq_of_eq ((commonPhysicalCanonicalFixedPointExactMPSGroundPath_tensor_one
      ρ₀ ρ₁ (NeZero.pos D₀) (NeZero.pos D₁) h₀ h₁ U₀ U₁).trans
        (commonPhysicalRightPolarExactMPSGroundPath_tensor_zero
          ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁).symm)
  let Q := commonPhysicalInjectiveExactMPSGroundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ A₁ hA₁ hCov₀ hCov₁
  refine isSameExactMPSGappedPhase_of_common_factor_groundPath
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ A₁ hA₁ hCov₀ hCov₁ Q ?_ ?_
  · have hzero : Q.tensor 0 = L.tensor 1 :=
      eq_of_heq (ExactMPSGroundPath.reverseTransTrans_tensor_zero L M R
        rfl rfl hLM hMR)
    rw [hzero]
    exact commonPhysicalLeftPolarExactMPSGroundPath_samePositiveMpvRay_one
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₀ hA₀ hCov₀
  · have hone : Q.tensor 1 = R.tensor 1 :=
      eq_of_heq (ExactMPSGroundPath.reverseTransTrans_tensor_one L M R
        rfl rfl hLM hMR)
    rw [hone]
    exact commonPhysicalRightPolarExactMPSGroundPath_samePositiveMpvRay_one
      ρ₀ ρ₁ h₀ h₁ U₀ U₁ A₁ hA₁ hCov₁

/-- Cohomologous unitary virtual actions suffice for the independent
exact phase relation. Unit-circle rephasing retains the original physical
covariances. Source: arXiv:1010.3732, Section II.F.2, lines 886–929. -/
theorem isSameExactMPSGappedPhase_of_unitary_cohomologous
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hCov₀ : ∀ g, rotatePhysical (U₀ g) A₀ =
      fun i => (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (sptGauge ρ₀ g : Matrix (Fin D₀) (Fin D₀) ℂ)ᴴ)
    (hCov₁ : ∀ g, rotatePhysical (U₁ g) A₁ =
      fun i => (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (sptGauge ρ₁ g : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ)
    (hCoh : ω₁.CohomologousTo ω₀) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  obtain ⟨σ, φ, hσ, hX⟩ :=
    ρ₀.exists_unitary_rephase_of_unitary_cohomologous ρ₁ h₀ h₁ hCoh
  exact isSameExactMPSGappedPhase_of_unitary_common_factor
    ρ₀ σ h₀ hσ U₀ U₁ A₀ hA₀ A₁ hA₁ hCov₀
    (rotatePhysical_covariance_of_circle_rephase ρ₁ σ φ hX U₁ A₁ hCov₁)

/-- One-site injective tensors with actual virtual implementations in the
same cohomology class belong to the same independent exact MPS gapped phase.
The virtual implementations need not be unitary: preparation, interpolation,
and gauge invariance supply the phase witnesses for the original tensors.
Source: arXiv:1010.3732, Sections II.C and II.F.2. -/
theorem isSameExactMPSGappedPhase_of_isInjective_cohomologous
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (A₀ : MPSTensor d₀ D₀) (hA₀ : Kraus.IsInjective A₀)
    (A₁ : MPSTensor d₁ D₁) (hA₁ : Kraus.IsInjective A₁)
    (hρ₀ : ∀ g i, twistedTensor A₀
      ((Matrix.unitaryGroup (Fin d₀) ℂ).subtype.comp U₀) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A₁
      ((Matrix.unitaryGroup (Fin d₁) ℂ).subtype.comp U₁) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ))
    (hCoh : ω₁.CohomologousTo ω₀) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ := by
  obtain ⟨B₀, c₀, η₀, σ₀, hc₀, hGauge₀, hB₀, hClass₀, hσ₀, hCov₀⟩ :=
    exists_unitary_covariant_preparation_with_virtual_class A₀ hA₀ U₀ ρ₀ hρ₀
  obtain ⟨B₁, c₁, η₁, σ₁, hc₁, hGauge₁, hB₁, hClass₁, hσ₁, hCov₁⟩ :=
    exists_unitary_covariant_preparation_with_virtual_class A₁ hA₁ U₁ ρ₁ hρ₁
  have hPrepared := isSameExactMPSGappedPhase_of_unitary_cohomologous
    σ₀ σ₁ hσ₀ hσ₁ U₀ U₁
    B₀ hB₀ B₁ hB₁ hCov₀ hCov₁
    (hClass₁.trans (hCoh.trans hClass₀.symm))
  exact hPrepared.of_smul_gaugeEquiv c₀ c₁ hc₀ hc₁ hGauge₀ hGauge₁
end MPSTensor
