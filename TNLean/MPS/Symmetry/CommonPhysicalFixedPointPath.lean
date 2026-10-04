/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.InteractionHamiltonianSymmetry
import TNLean.MPS.Symmetry.CommonPhysicalEndpoints
import TNLean.MPS.Symmetry.EmbeddedFixedPointParent
import TNLean.MPS.Symmetry.IsometricParentInteraction
import TNLean.MPS.Symmetry.NormalizedBondLocalSymmetry
import TNLean.MPS.Symmetry.PhysicalInteractionGroundSpace
import TNLean.MPS.Symmetry.PhysicalSpectatorBondTransport

/-!
# The fixed-point path in the common physical representation

The direct-sum bond interpolation is included into the common physical
space, retaining the two original physical complements with energy one.
Its commuting local projections retain their uniform gap and their unique
transported ground line. Ordered affine comparisons connect the two bond
endpoints to the corresponding canonical parent projections.

Source: arXiv:1010.3732, Sections II.D.2 and II.F.2, equations
eq:sym:omega-gamma and eq:1d-sym:jointsym.

**Scope restriction (one-site injective tensors and trivial character):**
The endpoint construction concerns the single-block, one-site injective
case, with trivial scalar character. These restrictions are documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Unitary symmetry is preserved by physical conjugation when the
rectangular physical map intertwines the two unitary actions. -/
theorem commute_singleKrausMap_of_unitary_intertwiner
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (V : Matrix ι ι ℂ) (E : Matrix κ ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup κ ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hE : U * E = E * V) (M : Matrix ι ι ℂ) (hM : Commute V M) :
    Commute U (singleKrausMap E M) := by
  have hRight : Eᴴ * U = V * Eᴴ := by
    have h := congrArg Matrix.conjTranspose hE
    have hh := congrArg (fun A => V * A * U) h
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose] at hh
    rw [(Matrix.mem_unitaryGroup_iff'.mp hU), Matrix.mul_one,
      ← Matrix.mul_assoc V, (Matrix.mem_unitaryGroup_iff.mp hV), Matrix.one_mul] at hh
    exact hh.symm
  apply (commute_iff_eq _ _).mpr
  calc
    U * singleKrausMap E M = (U * E) * M * Eᴴ := by
      simp only [singleKrausMap_apply, Matrix.mul_assoc]
    _ = (E * V) * M * Eᴴ := by rw [hE]
    _ = E * (M * V) * Eᴴ := by rw [Matrix.mul_assoc E V M, hM.eq]
    _ = (E * M) * (Eᴴ * U) := by simp only [Matrix.mul_assoc, hRight]
    _ = singleKrausMap E M * U := by simp only [singleKrausMap_apply, Matrix.mul_assoc]

end Matrix

namespace MPSTensor

/-- A two-site interaction extended through a physical intertwiner
commutes with the enlarged on-site action. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem isometricInteractionExtension_commute_onSiteTensorPow {d m : ℕ}
    (U : Matrix.unitaryGroup (Fin m) ℂ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (E : Matrix (Fin m) (Fin d) ℂ)
    (hE : (U : Matrix (Fin m) (Fin m) ℂ) * E =
      E * (V : Matrix (Fin d) (Fin d) ℂ))
    (A : MPOTensor.ChainOperator d 2)
    (hA : Commute A (onSiteTensorPow 2 (V : Matrix (Fin d) (Fin d) ℂ))) :
    Commute (isometricInteractionExtension E A)
      (onSiteTensorPow 2 (U : Matrix (Fin m) (Fin m) ℂ)) := by
  have hInt : onSiteTensorPow 2 (U : Matrix (Fin m) (Fin m) ℂ) *
      MPOTensor.sitewisePhysicalMatrix E 2 =
      MPOTensor.sitewisePhysicalMatrix E 2 *
        onSiteTensorPow 2 (V : Matrix (Fin d) (Fin d) ℂ) := by
    change Matrix.rectKronecker (fun _ : Fin 2 => (U : Matrix (Fin m) (Fin m) ℂ)) *
      Matrix.rectKronecker (fun _ : Fin 2 => E) =
      Matrix.rectKronecker (fun _ : Fin 2 => E) *
        Matrix.rectKronecker (fun _ : Fin 2 => (V : Matrix (Fin d) (Fin d) ℂ))
    rw [Matrix.rectKronecker_mul, Matrix.rectKronecker_mul]
    simp only [hE]
  have hUnitary {r : ℕ} (R : Matrix.unitaryGroup (Fin r) ℂ) :
      onSiteTensorPow 2 (R : Matrix (Fin r) (Fin r) ℂ) ∈
        Matrix.unitaryGroup (Cfg r 2) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr
      (onSiteTensorPow_conjTranspose_mul_self (SetLike.coe_mem R) 2)
  exact ((Commute.one_right _).sub_right
    (Matrix.commute_singleKrausMap_of_unitary_intertwiner _ _ _ (hUnitary U) (hUnitary V)
      hInt (1 - A) ((Commute.one_right _).sub_right hA.symm))).symm

/-- The periodic translates of the normalized independent-bond interaction
commute. Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem normalizedBondInteraction_translate_commute {D₀ D₁ N : ℕ} [NeZero N]
    (γ : ℝ) (hN : 2 ≤ N) (i j : Fin N) :
    Commute (MPOTensor.embedLocalOperator 2 N hN i (normalizedBondInteraction D₀ D₁ γ))
      (MPOTensor.embedLocalOperator 2 N hN j (normalizedBondInteraction D₀ D₁ γ)) := by
  let P := (incomingBondPerm (D₀ + D₁) N).permMatrix ℂ
  let η := normalizedBondInterpolationVector D₀ D₁ γ
  have hTranslated (k : Fin N) :
      MPOTensor.embedLocalOperator 2 N hN k (normalizedBondInteraction D₀ D₁ γ) =
        singleKrausMap P (bondPenaltyAt η (by omega) (finRotate N k)) := by
    rw [normalizedBondInteraction, embed_twoSiteBondInteraction_eq_conj]
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, singleKrausMap_apply, P, η, bondPenaltyAt]
  have hP : Pᴴ * P = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp (incomingBondPerm_mem_unitaryGroup (D₀ + D₁) N))
  rw [hTranslated i, hTranslated j]
  apply (commute_iff_eq _ _).mpr
  rw [← Matrix.singleKrausMap_mul_of_isometry P hP,
    ← Matrix.singleKrausMap_mul_of_isometry P hP]
  exact congrArg (singleKrausMap P)
    (bondPenaltyAt_commute η (by omega) (finRotate N i) (finRotate N j)).eq

/-- The normalized bond interaction in the active summand of the common
physical space, with energy one on unused two-site states. Source:
arXiv:1010.3732, Section II.F.2, equations eq:sym:omega-gamma
and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalNormalizedBondInteraction
    (D₀ D₁ d₀ d₁ : ℕ) (γ : ℝ) :
    MPOTensor.ChainOperator (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) 2 :=
  isometricInteractionExtension
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (normalizedBondInteraction D₀ D₁ γ)

/-- Every enlarged normalized bond term is an orthogonal projection.
Source: arXiv:1010.3732, Section II.F.2, eq:sym:omega-gamma. -/
theorem commonPhysicalNormalizedBondInteraction_isStarProjection
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (d₀ d₁ : ℕ) (γ : ℝ) :
    IsStarProjection (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) :=
  isometricInteractionExtension_isStarProjection _
    (commonFixedPointInclusion_isometry _ d₀ d₁) _
    (normalizedBondInteraction_isStarProjection h₀ h₁ γ)

/-- Including the continuous normalized bond interpolation in the common
physical space preserves continuity. Source: arXiv:1010.3732,
Section II.F.2, eq:sym:omega-gamma. -/
theorem continuous_commonPhysicalNormalizedBondInteraction
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (d₀ d₁ : ℕ) :
    Continuous (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁) := by
  let E := MPOTensor.sitewisePhysicalMatrix
    (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) 2
  change Continuous (fun γ => 1 - E * (1 - normalizedBondInteraction D₀ D₁ γ) * Eᴴ)
  exact continuous_const.sub
    ((continuous_const.matrix_mul (continuous_const.sub
      (continuous_normalizedBondInteraction h₀ h₁))).matrix_mul continuous_const)

/-- A periodic kernel inclusion is preserved by physical extension when
the smaller local interaction is a commuting projection. Source context:
arXiv:1010.3732, Section II.F.2, comparison of canonical parents. -/
theorem isometricInteractionExtension_ker_le_of_ker_le {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A B : MPOTensor.ChainOperator d 2) (hA : IsStarProjection A)
    (hB : B.IsHermitian) (hN : 2 ≤ N)
    (hcommOld : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i A)
        (MPOTensor.embedLocalOperator 2 N hN j A))
    (hcommNew : ∀ i j : Fin N,
      Commute (MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E A))
        (MPOTensor.embedLocalOperator 2 N hN j (isometricInteractionExtension E A)))
    (hker : LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian B hN))) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (isometricInteractionExtension E B) hN)) := by
  rw [isometricInteractionExtension_ker_eq_map E hE A hA hN hcommOld hcommNew]
  rintro x ⟨y, hy, rfl⟩
  have hyB := LinearMap.mem_ker.mp (hker hy)
  have hInt : Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E B) hN) ∘ₗ
        Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) =
      Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) ∘ₗ
        Matrix.toEuclideanLin (interactionHamiltonian B hN) := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg Matrix.toEuclideanLin
        (interactionHamiltonian_isometricInteractionExtension_intertwiner E hE B hB hN)
  change Matrix.toEuclideanLin
    (interactionHamiltonian (isometricInteractionExtension E B) hN)
      (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) y) = 0
  calc
    _ = Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)
        (Matrix.toEuclideanLin (interactionHamiltonian B hN) y) :=
      LinearMap.congr_fun hInt y
    _ = 0 := by rw [hyB, map_zero]

/-- The enlarged normalized bond Hamiltonian has zero ground energy on
every periodic chain of length at least two. Source: arXiv:1010.3732,
Section II.F.2, eq:sym:omega-gamma. -/
theorem commonPhysicalNormalizedBondInteraction_zero_mem_spectrum
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N) :
    (0 : ℂ) ∈ spectrum ℂ
      (interactionHamiltonian (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN) := by
  have hdet : Matrix.det
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN) = 0 := by
    simpa only [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using
      (interactionHamiltonian_normalizedBondInteraction_spectrum_gap_one h₀ h₁ γ hN).1
  obtain ⟨ψ, hψ, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact isometricInteractionExtension_zero_mem_spectrum _
    (commonFixedPointInclusion_isometry _ d₀ d₁) _
    (normalizedBondInteraction_isStarProjection h₀ h₁ γ).isSelfAdjoint.isHermitian
    hN ψ hψ hz

/-- The local bond comparison with a canonical parent persists in the
common physical space. Source: arXiv:1010.3732, Section II.F.2,
eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
theorem commonPhysicalNormalizedBondInteraction_le_parent {D₀ D₁ R : ℕ}
    (d₀ d₁ : ℕ) (γ : ℝ)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) R)
    (horder : normalizedBondInteraction D₀ D₁ γ ≤
      LinearMap.toMatrix' (parentInteraction B 2)) :
    commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ ≤
      LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) B) 2) := by
  rw [parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension _
    (commonFixedPointInclusion_isometry _ d₀ d₁)]
  exact isometricInteractionExtension_mono _ horder

/-- The enlarged normalized bond terms commute at every pair of sites.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem commonPhysicalNormalizedBondInteraction_translate_commute
    {D₀ D₁ N : ℕ} [NeZero N] (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N) (i j : Fin N) :
    Commute (MPOTensor.embedLocalOperator 2 N hN i
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ))
      (MPOTensor.embedLocalOperator 2 N hN j
        (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ)) := by
  simpa only [physicalSpectatorBondInteraction_eq_isometricInteractionExtension,
    commonPhysicalNormalizedBondInteraction, normalizedBondInteraction] using
    physicalSpectatorBondInteraction_translate_commute (D₀ + D₁) d₀ d₁
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ))) hN i j

/-- The enlarged normalized bond Hamiltonians retain the uniform gap of
one above zero. Source: arXiv:1010.3732, Section II.F.2, eq:sym:omega-gamma. -/
theorem commonPhysicalNormalizedBondInteraction_spectrum_gap_one
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N) :
    ∀ z ∈ spectrum ℂ (interactionHamiltonian
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  simpa only [physicalSpectatorBondInteraction_eq_isometricInteractionExtension,
    commonPhysicalNormalizedBondInteraction, normalizedBondInteraction] using
    physicalSpectatorBondInteraction_spectrum_gap_one (D₀ + D₁) d₀ d₁ _
      (bondPenalty_reindex_isStarProjection _
        (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ)) hN

/-- The enlarged periodic Hamiltonian has precisely the transported
weighted matrix-unit MPS ground line. Source: arXiv:1010.3732,
Section II.F.2, eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
theorem commonPhysicalNormalizedBondInteraction_groundSpace
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN)) =
      Submodule.span ℂ {(Matrix.toEuclideanLin
        (MPOTensor.sitewisePhysicalMatrix
          (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) N)
        (WithLp.toLp 2 (mpv (N := N) (weightedMatrixUnitInterpolation D₀ D₁ γ))))} := by
  have : NeZero N := ⟨by omega⟩
  exact isometricInteractionExtension_ker_eq_span _
    (commonFixedPointInclusion_isometry _ d₀ d₁) _
    (normalizedBondInteraction_isStarProjection h₀ h₁ γ) hN
    (normalizedBondInteraction_translate_commute γ hN)
    (commonPhysicalNormalizedBondInteraction_translate_commute d₀ d₁ γ hN) _
    (interactionHamiltonian_normalizedBondInteraction_groundSpace h₀ h₁ γ hN)

/-- The tensor power of a rectangular physical map carries the periodic
MPS vector to that of the rotated tensor. Source context: arXiv:1010.3732,
Section II.F.2, eq:1d-sym:jointsym. -/
theorem toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical {d m D N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (A : MPSTensor d D) :
    Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)
        (WithLp.toLp 2 (mpv (N := N) A)) =
      WithLp.toLp 2 (mpv (N := N) (rotatePhysical E A)) := by
  change WithLp.toLp 2 ((Matrix.rectKronecker fun _ : Fin N => E).mulVec (mpv A)) =
    WithLp.toLp 2 (mpv (rotatePhysical E A))
  rw [mpv_eq_groundSpaceMap_one A N, mpv_eq_groundSpaceMap_one (rotatePhysical E A) N,
    groundSpaceMap_rotatePhysical_rectangular]

/-- The ground line is the periodic MPS line of the explicitly included
weighted tensor. Source: arXiv:1010.3732, Section II.F.2,
eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
theorem commonPhysicalNormalizedBondInteraction_groundSpace_eq_span_mpv
    {D₀ D₁ N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := N)
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (weightedMatrixUnitInterpolation D₀ D₁ γ))))} := by
  rw [commonPhysicalNormalizedBondInteraction_groundSpace h₀ h₁ d₀ d₁ γ hN,
    toEuclideanLin_sitewisePhysicalMatrix_mpv_rotatePhysical]

/-- Every enlarged bond zero mode is a canonical-parent zero mode whenever
this inclusion holds before adjoining the unused physical states.
Source: arXiv:1010.3732, Section II.F.2, canonical-parent comparison. -/
theorem commonPhysicalNormalizedBondInteraction_ker_le_parent
    {D₀ D₁ R N : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁)
    (d₀ d₁ : ℕ) (γ : ℝ) (hN : 2 ≤ N)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) R)
    (hker : LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (normalizedBondInteraction D₀ D₁ γ) hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (LinearMap.toMatrix' (parentInteraction B 2)) hN))) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN)) ≤
      LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
        (LinearMap.toMatrix' (parentInteraction
          (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) B) 2))
        hN)) := by
  have : NeZero N := ⟨by omega⟩
  rw [parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension _
    (commonFixedPointInclusion_isometry _ d₀ d₁)]
  exact isometricInteractionExtension_ker_le_of_ker_le _
    (commonFixedPointInclusion_isometry _ d₀ d₁) _ _
    (normalizedBondInteraction_isStarProjection h₀ h₁ γ)
    (parentInteraction_toMatrix'_isStarProjection B 2).isSelfAdjoint.isHermitian hN
    (normalizedBondInteraction_translate_commute γ hN)
    (commonPhysicalNormalizedBondInteraction_translate_commute d₀ d₁ γ hN) hker

/-- Covariance of an active tensor gives symmetry of its canonical parent
in the actual three-summand physical representation. Source:
arXiv:1010.3732, Section II.F.2, eq:1d-sym:jointsym. -/
theorem commonPhysicalParentInteraction_commute_onSite
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ R N : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (B : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) R) (g : G)
    (hCov : GaugeEquiv B
      (rotatePhysical (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g) B))
    (hN : 2 ≤ N) :
    Commute (interactionHamiltonian (LinearMap.toMatrix' (parentInteraction
      (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) B) 2)) hN)
      (Matrix.finKronecker fun _ : Fin N =>
        (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g : Matrix _ _ ℂ)) := by
  let V := sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
    (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))
  let U := commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁
  let E := commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁
  let A := rotatePhysical E B
  let Ug : Matrix (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁))
      (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁)) ℂ := U g
  let Vg : Matrix (Fin ((D₀ + D₁) * (D₀ + D₁)))
      (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ := V g
  have hCovA : GaugeEquiv A (rotatePhysical Ug A) :=
    gaugeEquiv_rotatePhysical_of_intertwiner E B Vg Ug
      (commonFixedPointInclusion_intertwiner V U₀ U₁ g) hCov
  have hLocal := parentInteraction_matrix_commute_onSiteTensorPow A Ug
    (SetLike.coe_mem (U g)) hCovA 2
  change Commute (interactionHamiltonian
    (LinearMap.toMatrix' (parentInteraction A 2)) hN) (onSiteTensorPow N Ug)
  exact interactionHamiltonian_commute_onSiteTensorPow Ug _ hN hLocal

/-- The enlarged normalized bond interaction commutes with the fixed
two-site physical representation. Source: arXiv:1010.3732,
Section II.F.2, eq:1d-sym:jointsym. -/
theorem commonPhysicalNormalizedBondInteraction_commute_onSiteTensorPow
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) (g : G) (γ : ℝ) :
    Commute (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ)
      (onSiteTensorPow 2
        (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g : Matrix _ _ ℂ)) := by
  let V := sptFixedPointUnitaryAction (ρ₀.directSum ρ₁)
    (fun g => ρ₀.directSum_mem_unitaryGroup ρ₁ g (h₀ g) (h₁ g))
  let U := commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁
  have hLocal : Commute (normalizedBondInteraction D₀ D₁ γ)
      (onSiteTensorPow 2 (V g : Matrix (Fin ((D₀ + D₁) * (D₀ + D₁)))
        (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ)) :=
    normalizedBondInteraction_commute_onSite ρ₀ ρ₁ h₀ h₁ g γ
  exact isometricInteractionExtension_commute_onSiteTensorPow (U g) (V g) _
    (commonFixedPointInclusion_intertwiner V U₀ U₁ g) _ hLocal

/-- Every enlarged periodic bond Hamiltonian commutes with the common
on-site symmetry. Source: arXiv:1010.3732, Section II.F.2,
eq:1d-sym:jointsym. -/
theorem commonPhysicalNormalizedBondInteraction_commute_onSite
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ N : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) (g : G) (γ : ℝ) (hN : 2 ≤ N) :
    Commute (interactionHamiltonian
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN)
      (Matrix.finKronecker fun _ : Fin N =>
        (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g : Matrix _ _ ℂ)) := by
  let Ug : Matrix (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁))
      (Fin (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁)) ℂ :=
    commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁ g
  have hLocal := commonPhysicalNormalizedBondInteraction_commute_onSiteTensorPow
    ρ₀ ρ₁ h₀ h₁ U₀ U₁ g γ
  change Commute (interactionHamiltonian
    (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ) hN) (onSiteTensorPow N Ug)
  exact interactionHamiltonian_commute_onSiteTensorPow Ug _ hN hLocal

/-- The normalized direct-sum bond interpolation is a symmetric uniformly
gapped path in the common physical space, retaining both original physical
complements. Source: arXiv:1010.3732, Section II.F.2,
eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalNormalizedBondGappedPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ 0)
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ 1) where
  interaction := commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁
  interaction_zero := rfl
  interaction_one := rfl
  hermitian γ _ :=
    (commonPhysicalNormalizedBondInteraction_isStarProjection
      hD₀ hD₁ d₀ d₁ γ).isSelfAdjoint.isHermitian
  norm_le_one γ _ :=
    (commonPhysicalNormalizedBondInteraction_isStarProjection hD₀ hD₁ d₀ d₁ γ).norm_le _
  continuous := (continuous_commonPhysicalNormalizedBondInteraction hD₀ hD₁ d₀ d₁).continuousOn
  gap := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro γ _ N hN
    refine ⟨0, commonPhysicalNormalizedBondInteraction_zero_mem_spectrum
      hD₀ hD₁ d₀ d₁ γ hN, ?_⟩
    simpa only [zero_add] using
      commonPhysicalNormalizedBondInteraction_spectrum_gap_one hD₀ hD₁ d₀ d₁ γ hN
  symmetric γ _ g N hN :=
    commonPhysicalNormalizedBondInteraction_commute_onSite ρ₀ ρ₁ h₀ h₁ U₀ U₁ g γ hN

/-- For a fixed normalized bond, its ordered canonical-parent comparison
is a symmetric uniformly gapped affine path in the common physical space.
The local order and periodic kernel inclusion are supplied before physical
extension. Source: arXiv:1010.3732, Section II.F.2,
eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalBondCanonicalParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ R : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) (γ : ℝ)
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
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) B) 2)) := by
  let U := commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁
  let A := commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ γ
  let C := rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁) B
  have hA := commonPhysicalNormalizedBondInteraction_isStarProjection hD₀ hD₁ d₀ d₁ γ
  have hC := parentInteraction_toMatrix'_isStarProjection C 2
  refine orderedGappedInteractionPath U A _
    (Matrix.nonneg_iff_posSemidef.mp hA.nonneg)
    (Matrix.nonneg_iff_posSemidef.mp hC.nonneg)
    (commonPhysicalNormalizedBondInteraction_le_parent d₀ d₁ γ B horder)
    (hA.norm_le _) (parentInteraction_toMatrix'_norm_le_one C 2)
    ?_ ?_ ⟨1, zero_lt_one, fun N hN z hz =>
      (commonPhysicalNormalizedBondInteraction_spectrum_gap_one hD₀ hD₁ d₀ d₁ γ hN z hz).2⟩
    (fun N hN g =>
      commonPhysicalNormalizedBondInteraction_commute_onSite ρ₀ ρ₁ h₀ h₁ U₀ U₁ g γ hN)
    (fun N hN g =>
      commonPhysicalParentInteraction_commute_onSite ρ₀ ρ₁ h₀ h₁ U₀ U₁ B g (hCov g) hN)
  · intro N hN x hx
    have hxES : WithLp.toLp 2 x ∈ LinearMap.ker
        (Matrix.toEuclideanLin (interactionHamiltonian A hN)) := by
      change WithLp.toLp 2 ((interactionHamiltonian A hN).mulVec x) = 0
      rw [hx, WithLp.toLp_zero]
    have hparent := commonPhysicalNormalizedBondInteraction_ker_le_parent
      hD₀ hD₁ d₀ d₁ γ hN B (hker N hN) hxES
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, WithLp.toLp_eq_zero] using hparent
  · intro N hN
    have hspec : (0 : ℂ) ∈ spectrum ℂ
        (Matrix.toEuclideanLin (interactionHamiltonian A hN)) := by
      rw [Matrix.spectrum_toLpLin]
      exact commonPhysicalNormalizedBondInteraction_zero_mem_spectrum hD₀ hD₁ d₀ d₁ γ hN
    obtain ⟨x, hx⟩ :=
      (Module.End.HasEigenvalue.of_mem_spectrum hspec).exists_hasEigenvector
    exact ⟨x, hx.2, by simpa only [zero_smul] using hx.apply_eq_smul⟩

/-- The first enlarged bond endpoint is joined to the canonical parent of
the first fixed-point tensor in the active summand. Source: arXiv:1010.3732,
Section II.F.2, eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalLeftParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ 0)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointLeft D₀ D₁)) 2)) :=
  commonPhysicalBondCanonicalParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ 0
    (embeddedSptFixedPointLeft D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 0 _
      (Matrix.coordinateInclusion (Fin.castAddEmb D₁))
      (Matrix.coordinateInclusion_isometry (Fin.castAddEmb D₁))
      (weightedMatrixUnitInterpolation_zero_intertwine D₀ D₁))
    (fun N hN => ker_interactionHamiltonian_normalizedBondInteraction_le_parent_of_mpv_eq
      hD₀ hD₁ 0 hN _ (mpv_embeddedSptFixedPointLeft (by omega)))
    (fun g => ⟨sptGauge ρ₀ g, twistedTensor_embeddedSptFixedPointLeft ρ₀ ρ₁ g⟩)

/-- The second enlarged bond endpoint is joined to the canonical parent of
the second fixed-point tensor in the same active summand. Source:
arXiv:1010.3732, Section II.F.2, eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalRightParentComparisonPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (commonPhysicalNormalizedBondInteraction D₀ D₁ d₀ d₁ 1)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointRight D₀ D₁)) 2)) :=
  commonPhysicalBondCanonicalParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁ 1
    (embeddedSptFixedPointRight D₀ D₁)
    (normalizedBondInteraction_le_parent_of_isometric_bond_intertwiner hD₀ hD₁ 1 _
      (Matrix.coordinateInclusion (Fin.natAddEmb D₀))
      (Matrix.coordinateInclusion_isometry (Fin.natAddEmb D₀))
      (weightedMatrixUnitInterpolation_one_intertwine D₀ D₁))
    (fun N hN => ker_interactionHamiltonian_normalizedBondInteraction_le_parent_of_mpv_eq
      hD₀ hD₁ 1 hN _ (mpv_embeddedSptFixedPointRight (by omega)))
    (fun g => ⟨sptGauge ρ₁ g, twistedTensor_embeddedSptFixedPointRight ρ₀ ρ₁ g⟩)

/-- The canonical parents of the two prescribed fixed-point tensors are
connected in the common physical representation by a symmetric uniformly
gapped path. Both original physical complements are retained. Source:
arXiv:1010.3732, Section II.F.2, eq:sym:omega-gamma and eq:1d-sym:jointsym. -/
noncomputable def commonPhysicalCanonicalFixedPointGappedPath
    {G : Type} [Group G] {D₀ D₁ d₀ d₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ)
    (U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ) :
    SymmetricGappedInteractionPath (commonSptPhysicalAction ρ₀ ρ₁ h₀ h₁ U₀ U₁)
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointLeft D₀ D₁)) 2))
      (LinearMap.toMatrix' (parentInteraction
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
          (embeddedSptFixedPointRight D₀ D₁)) 2)) :=
  ((commonPhysicalLeftParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁).reverse.trans
    (commonPhysicalNormalizedBondGappedPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁)).trans
      (commonPhysicalRightParentComparisonPath ρ₀ ρ₁ hD₀ hD₁ h₀ h₁ U₀ U₁)

end MPSTensor
