/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IsometricDeformation
import TNLean.MPS.ParentHamiltonian.CompactOpenParentInteractionGap

/-!
# Uniform open-chain gaps along the isometric deformation

The affine positive physical path preserves simultaneous one-site spanning.
Compactness gives a canonical two-site gap uniform in the path parameter and
all open-chain lengths at least two. The inverse-conjugated positive
interaction has the same local kernel and inherits a uniform gap.

The joint left polar decomposition supplies the positive factor and initial
isometric blocks from the original tensor. Pairwise inequivalent normalized
normal blocks admit a finite initial blocking to which these conclusions
apply. The gap is measured on the orthogonal complement of the open kernel;
free boundary degrees of freedom remain in that kernel.

Source: arXiv:1010.3732, eq. (1d-iso:polardec), lines 575--625 and Appendix A.
The open-chain estimates use Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2
and Section 6. The initial joint one-site span is supplied or derived by
blocking; normality alone is not identified with one-site injectivity.
-/

open scoped Matrix BigOperators ComplexOrder Topology

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- The supplied affine positive physical deformation has one canonical
two-site open-chain gap uniform in its parameter and every length at least
two. Source: arXiv:1010.3732, lines 589--594 and Appendix A; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_openParentHamiltonianES_gap_positivePhysicalDeformation
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1)
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks μ
          (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks μ
            (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))) 2 N v‖ := by
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
      (fun _ : unitInterval => μ)
      (fun γ j => rotatePhysical (positivePhysicalDeformation Q γ) (A j))
      (fun _ => hμ)
      (fun j => continuous_rotatePhysical_family _ (fun _ => A j)
        (continuous_positivePhysicalDeformation Q) continuous_const)
      (S := 1) zero_lt_one
      (fun γ => (wordTupleSpanTop_rotatePhysical_iff _
        (positivePhysicalDeformation_isUnit Q hQ γ) A 1).2 hSpan)
      (R := 2) le_rfl isCompact_univ
  exact ⟨δ, hδ, fun γ => hgap γ (Set.mem_univ γ)⟩

/-- The source's inverse-conjugated two-site interaction along a supplied
positive affine path has one gap uniform in the parameter and every open
length at least two. Source: arXiv:1010.3732, lines 610--625 and Appendix A;
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_positiveDeformedParentInteractionES_open_gap
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1)
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A) γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (positiveDeformedParentInteractionES Q
            (toTensorFromBlocks μ A) γ).toLinearMap N v‖ := by
  have hParent (γ : unitInterval) : IsParentInteraction
      (toTensorFromBlocks μ (fun j => rotatePhysical (positivePhysicalDeformation Q γ) (A j)))
      2 (positiveDeformedParentInteractionES Q (toTensorFromBlocks μ A) γ).toLinearMap := by
    simpa only [rotatePhysical_toTensorFromBlocks] using
      isParentInteraction_positiveDeformedParentInteractionES Q hQ (toTensorFromBlocks μ A) γ
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_block_openParentInteraction_gap_of_compact
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

/-- The constructed joint isometric deformation has one canonical two-site
open-chain gap uniform in its parameter and every length at least two.
The positive polar factor is derived from the original blocks.
Source: arXiv:1010.3732, lines 575--625 and Appendix A; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_isometricDeformation_open_parent_gap
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N v‖ := by
  exact exists_uniform_openParentHamiltonianES_gap_positivePhysicalDeformation
    (leftPolarBlocks A) ((wordTupleSpanTop_leftPolarBlocks_iff A 1).2 hSpan)
    (fun _ => 1) (by simp) (leftPolarPhysicalFactor A) (leftPolarPhysicalFactor_posDef A)

/-- The source's positive interaction along the constructed joint isometric
path has one gap uniform in the parameter and every open length at least two.
Source: arXiv:1010.3732, lines 610--625 and Appendix A; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_isometricDeformation_open_interaction_gap
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (isometricDeformationInteractionES A γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (isometricDeformationInteractionES A γ).toLinearMap N v‖ := by
  exact exists_uniform_positiveDeformedParentInteractionES_open_gap
    (leftPolarBlocks A) ((wordTupleSpanTop_leftPolarBlocks_iff A 1).2 hSpan)
    (fun _ => 1) (by simp) (leftPolarPhysicalFactor A) (leftPolarPhysicalFactor_posDef A)

omit [∀ j, NeZero (dim j)] in
/-- Pairwise inequivalent normalized normal blocks admit a finite initial
blocking after which their constructed isometric path has one canonical
open-chain gap uniform in its parameter and every blocked length at least two.
The blocking satisfies \(L+1\leq3\max(\sum_jD_j,1)^5\).
Source: arXiv:1010.3732, lines 575--625 and Appendix A; arXiv:1606.00608,
lines 317--345, for the simultaneous blocking bound. -/
theorem exists_blocked_isometricDeformation_open_parent_gap_of_isNormalTensor
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hNormal : ∀ j, IsNormalTensor (A j)) (hDistinct : BlocksNotGaugePhaseEquiv A) :
    ∃ L : ℕ, 0 < L ∧ L + 1 ≤ 3 * (max (∑ j, dim j) 1) ^ 5 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
        ∀ v ∈ (LinearMap.ker (openParentHamiltonianES
          (toTensorFromBlocks (fun _ => 1)
            (isometricDeformationBlocks (fun j => blockTensor (A j) L) γ)) 2 N))ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES
            (toTensorFromBlocks (fun _ => 1)
              (isometricDeformationBlocks (fun j => blockTensor (A j) L) γ)) 2 N v‖ := by
  let : ∀ j, NeZero (dim j) := fun j => ⟨(hNormal j).bondDim_ne_zero⟩
  obtain ⟨L, hL, hBound, hSpan⟩ :=
    exists_positive_blockTensor_wordTupleSpanTop_one_of_isNormalTensor A hNormal hDistinct
  exact ⟨L, hL, hBound, exists_uniform_isometricDeformation_open_parent_gap
    (fun j => blockTensor (A j) L) hSpan⟩

omit [∀ j, NeZero (dim j)] in
/-- Pairwise inequivalent normalized normal blocks admit a finite initial
blocking after which the source's positive isometric-deformation interaction
has one open-chain gap uniform in its parameter and every blocked length at
least two. The blocking satisfies \(L+1\leq3\max(\sum_jD_j,1)^5\).
Source: arXiv:1010.3732, lines 575--625 and Appendix A; arXiv:1606.00608,
lines 317--345, for the simultaneous blocking bound. -/
theorem exists_blocked_isometricDeformation_open_interaction_gap_of_isNormalTensor
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hNormal : ∀ j, IsNormalTensor (A j)) (hDistinct : BlocksNotGaugePhaseEquiv A) :
    ∃ L : ℕ, 0 < L ∧ L + 1 ≤ 3 * (max (∑ j, dim j) 1) ^ 5 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
        ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
          (isometricDeformationInteractionES (fun j => blockTensor (A j) L) γ).toLinearMap N))ᗮ,
          δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
            (isometricDeformationInteractionES
              (fun j => blockTensor (A j) L) γ).toLinearMap N v‖ := by
  let : ∀ j, NeZero (dim j) := fun j => ⟨(hNormal j).bondDim_ne_zero⟩
  obtain ⟨L, hL, hBound, hSpan⟩ :=
    exists_positive_blockTensor_wordTupleSpanTop_one_of_isNormalTensor A hNormal hDistinct
  exact ⟨L, hL, hBound, exists_uniform_isometricDeformation_open_interaction_gap
    (fun j => blockTensor (A j) L) hSpan⟩

end MPSTensor
