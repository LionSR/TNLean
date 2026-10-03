/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.UnitInterval
import TNLean.MPS.ParentHamiltonian.PhysicalActionWordTupleSpan
import TNLean.MPS.ParentHamiltonian.CompactParentInteractionGap
import TNLean.MPS.Periodic.Applications

/-!
# Uniform gaps along a positive affine physical deformation

On the retained physical space, let \(Q>0\) be supplied and set
\(Q_\gamma=\gamma Q+(1-\gamma)I\), for \(0\le\gamma\le1\).
The resulting physical transformations preserve joint one-site injectivity
and give a uniform periodic gap at range two. The same conclusion holds for
the source's positive interactions obtained by conjugating the initial parent
projection with \((Q_\gamma^{-1})^{\otimes2}\).

The positive factor and initial tensor are supplied; a left polar decomposition
of an arbitrary initial tensor is not constructed here.
Source: arXiv:1010.3732, eq. (1d-iso:polardec), lines 575--594 and 610--625,
and Appendix A.
-/

open scoped Matrix BigOperators Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The affine positive factor on the retained physical space.
Source: arXiv:1010.3732, lines 589--592. -/
noncomputable def positivePhysicalDeformation (Q : Matrix (Fin d) (Fin d) ℂ) (γ : unitInterval) :
    Matrix (Fin d) (Fin d) ℂ :=
  (γ : ℝ) • Q + (1 - (γ : ℝ)) • 1

/-- Every member of the affine positive path is positive definite.
Source: arXiv:1010.3732, lines 589--592. -/
theorem positivePhysicalDeformation_posDef
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (γ : unitInterval) :
    (positivePhysicalDeformation Q γ).PosDef := by
  by_cases hγ : (γ : ℝ) = 0
  · simpa [positivePhysicalDeformation, hγ] using
      (Matrix.PosDef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosDef)
  exact (hQ.smul (lt_of_le_of_ne γ.prop.1 (Ne.symm hγ))).add_posSemidef
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef).smul
      (sub_nonneg.mpr γ.prop.2))

/-- The affine physical path starts at the identity.
Source: arXiv:1010.3732, lines 589--594. -/
@[simp] theorem positivePhysicalDeformation_zero (Q : Matrix (Fin d) (Fin d) ℂ) :
    positivePhysicalDeformation Q 0 = 1 := by
  simp [positivePhysicalDeformation]

/-- The affine physical path ends at the supplied positive factor.
Source: arXiv:1010.3732, lines 589--594. -/
@[simp] theorem positivePhysicalDeformation_one (Q : Matrix (Fin d) (Fin d) ℂ) :
    positivePhysicalDeformation Q 1 = Q := by
  simp [positivePhysicalDeformation]

/-- The affine physical deformation is continuous.
Source: arXiv:1010.3732, lines 589--594. -/
theorem continuous_positivePhysicalDeformation (Q : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (positivePhysicalDeformation Q) := by
  exact (continuous_subtype_val.smul continuous_const).add
    ((continuous_const.sub continuous_subtype_val).smul continuous_const)

/-- Invertibility holds throughout the affine positive path.
Source: arXiv:1010.3732, lines 589--594. -/
theorem positivePhysicalDeformation_isUnit
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (γ : unitInterval) :
    IsUnit (positivePhysicalDeformation Q γ) :=
  (positivePhysicalDeformation_posDef Q hQ γ).isUnit

/-- The canonical two-site parent Hamiltonians along the affine physical path
have a gap uniform in the parameter and every periodic length at least two.
The initial simultaneous one-site span is supplied after the source's initial
blocking. Source: arXiv:1010.3732, lines 589--594 and Appendix A. -/
theorem exists_uniform_parentHamiltonianES_gap_positivePhysicalDeformation
    [NeZero d] [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1)
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) μ
          (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) μ
            (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))) 2 N v‖ := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_parentHamiltonianES_gap_of_compact_physicalAction
    A (S := 1) (R := 2) zero_lt_one hSpan le_rfl
    (positivePhysicalDeformation Q) (continuous_positivePhysicalDeformation Q)
    (positivePhysicalDeformation_isUnit Q hQ) (fun _ => μ) (fun _ => hμ) isCompact_univ
  exact ⟨δ, hδ, fun γ => hgap γ (Set.mem_univ γ)⟩

/-- The inverse physical factor varies continuously along the positive path.
Source: arXiv:1010.3732, the definition of \(\Lambda_\gamma\) at lines 615--617. -/
theorem continuous_positivePhysicalDeformation_inv
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) :
    Continuous fun γ : unitInterval => (positivePhysicalDeformation Q γ)⁻¹ := by
  apply continuous_iff_continuousAt.2
  intro γ
  have hdet : IsUnit (positivePhysicalDeformation Q γ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (positivePhysicalDeformation_isUnit Q hQ γ)
  have hinv : ContinuousAt Ring.inverse (positivePhysicalDeformation Q γ).det := by
    simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt hdet.unit
  exact (continuousAt_matrix_inv _ hinv).comp
    (continuous_positivePhysicalDeformation Q).continuousAt

/-- Tensor powers of continuous physical maps vary continuously as operators.
Source: arXiv:1010.3732, the definition of \(\Lambda_\gamma\) at lines 615--617. -/
theorem continuous_onSiteTensorPow_toContinuousLinearMap_family
    {X : Type*} [TopologicalSpace X] (M : X → Matrix (Fin d) (Fin d) ℂ)
    (hM : Continuous M) (L : ℕ) :
    Continuous fun x =>
      (Matrix.toEuclideanLin (onSiteTensorPow L (M x))).toContinuousLinearMap := by
  have hpow : Continuous fun x => onSiteTensorPow L (M x) :=
    continuous_matrix fun σ τ => by
      simpa only [onSiteTensorPow_apply] using
        continuous_finsetProd Finset.univ (fun n _ => hM.matrix_elem (σ n) (τ n))
  let e : Matrix (Cfg d L) (Cfg d L) ℂ ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d L)) :=
    Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap
  exact e.toContinuousLinearEquiv.continuous.comp hpow

/-- The positive interaction obtained by inverse physical conjugation is a
continuous family in operator norm. Source: arXiv:1010.3732, lines 615--623. -/
theorem continuous_deformedInteraction_positivePhysicalDeformation
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (L : ℕ)
    (h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)) :
    Continuous fun γ : unitInterval =>
      (deformedInteraction L (positivePhysicalDeformation Q γ) h).toContinuousLinearMap := by
  have hInv := continuous_positivePhysicalDeformation_inv Q hQ
  change Continuous fun γ : unitInterval =>
    ((Matrix.toEuclideanLin
      (onSiteTensorPow L ((positivePhysicalDeformation Q γ)⁻¹)ᴴ)).toContinuousLinearMap).comp
      h.toContinuousLinearMap |>.comp
        (Matrix.toEuclideanLin
          (onSiteTensorPow L (positivePhysicalDeformation Q γ)⁻¹)).toContinuousLinearMap
  exact ((continuous_onSiteTensorPow_toContinuousLinearMap_family
    (fun γ => ((positivePhysicalDeformation Q γ)⁻¹)ᴴ) hInv.matrix_conjTranspose L).clm_comp
      (continuous_const : Continuous fun _ : unitInterval => h.toContinuousLinearMap)).clm_comp
    (continuous_onSiteTensorPow_toContinuousLinearMap_family _ hInv L)

/-- The source's two-site positive interaction along the affine deformation,
\(h_\gamma=\Lambda_\gamma h_0\Lambda_\gamma\), where
\(\Lambda_\gamma=(Q_\gamma^{-1})^{\otimes2}\) and \(h_0\) is the canonical
initial parent projection. Positivity of the supplied factor makes the inverse
Hermitian, so inverse-adjoint conjugation equals the source formula.
Source: arXiv:1010.3732, lines 610--623. -/
noncomputable def positiveDeformedParentInteractionES {D : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (γ : unitInterval) :
    EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  (deformedInteraction 2 (positivePhysicalDeformation Q γ)
    (parentInteractionES A 2)).toContinuousLinearMap

/-- The source interaction has exactly the deformed local ground space as
its kernel, and is positive. Source: arXiv:1010.3732, lines 623--625. -/
theorem isParentInteraction_positiveDeformedParentInteractionES {D : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (A : MPSTensor d D)
    (γ : unitInterval) :
    IsParentInteraction (rotatePhysical (positivePhysicalDeformation Q γ) A) 2
      (positiveDeformedParentInteractionES Q A γ).toLinearMap := by
  exact (isParentInteraction_parentInteractionES A 2).deformedInteraction 2
    (positivePhysicalDeformation_isUnit Q hQ γ)

/-- The source's positive two-site interactions have a gap uniform in the
parameter and every periodic length at least two. The positive factor is on
the retained physical space, and the initial joint one-site span is supplied
following blocking. Source: arXiv:1010.3732, Appendix A, lines 2475--2580. -/
theorem exists_uniform_positiveDeformedParentInteractionES_gap
    [NeZero d] [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1)
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A) γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A) γ).toLinearMap N v‖ := by
  have hParent (γ : unitInterval) : IsParentInteraction
      (toTensorFromBlocks μ (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j)))
      2 (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A) γ).toLinearMap := by
    simpa only [rotatePhysical_toTensorFromBlocks] using
      isParentInteraction_positiveDeformedParentInteractionES Q hQ (toTensorFromBlocks μ A) γ
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_block_parentInteraction_gap_of_compact
    (fun _ : unitInterval => μ)
    (fun γ j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))
    (fun _ => hμ)
    (fun j => continuous_rotatePhysical_family _ (fun _ => A j)
      (continuous_positivePhysicalDeformation Q) continuous_const)
    (S := 1) zero_lt_one
    (fun γ => (wordTupleSpanTop_rotatePhysical_iff _
      (positivePhysicalDeformation_isUnit Q hQ γ) A 1).2 hSpan)
    (R := 2) le_rfl
    (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A))
    (continuous_deformedInteraction_positivePhysicalDeformation Q hQ 2
      (parentInteractionES (toTensorFromBlocks μ A) 2)) hParent isCompact_univ
  exact ⟨δ, hδ, fun γ => hgap γ (Set.mem_univ γ)⟩

/-- Positivity of the physical factor turns inverse-adjoint conjugation into
the two-sided inverse conjugation printed in the source.
Source: arXiv:1010.3732, lines 615--623. -/
theorem positiveDeformedParentInteractionES_eq {D : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (A : MPSTensor d D)
    (γ : unitInterval) :
    (positiveDeformedParentInteractionES Q A γ).toLinearMap =
      Matrix.toEuclideanLin (onSiteTensorPow 2 (positivePhysicalDeformation Q γ)⁻¹) ∘ₗ
        parentInteractionES A 2 ∘ₗ
          Matrix.toEuclideanLin (onSiteTensorPow 2 (positivePhysicalDeformation Q γ)⁻¹) := by
  change deformedInteraction 2 (positivePhysicalDeformation Q γ) (parentInteractionES A 2) = _
  rw [deformedInteraction, (positivePhysicalDeformation_posDef Q hQ γ).isHermitian.inv]

end MPSTensor
