/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LeftPolar
import TNLean.MPS.ParentHamiltonian.PositivePhysicalDeformationGap

/-!
# The isometric deformation of a jointly injective block tensor

The physical map \(P\) has one column for each matrix coordinate of each
block. Its left polar decomposition produces \(P=QW\), with \(Q>0\)
on the original physical space and \(WW^\dagger\) the projection onto
\(\operatorname{ran}P\). The positive factor is extended by the identity
outside this range. The blocks of \(W\) remain jointly injective, so the
affine deformation \(Q_\gamma W\) has a periodic parent gap uniform in
\(\gamma\in[0,1]\) and all chain lengths at least two.

Source: arXiv:1010.3732, eq. (1d-iso:polardec), lines 575--625,
and Appendix A. The one-site simultaneous span is the source's initial
blocking assumption.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The joint physical map of the block tensor, with domain the direct sum
of the block matrix spaces. Source: arXiv:1010.3732, lines 575--584. -/
def blockPhysicalMatrix (A : (j : Fin r) → MPSTensor d (dim j)) :
    Matrix (Fin d) (BlockEntryIndex dim) ℂ :=
  fun i p => A p.1 i p.2.1 p.2.2

/-- The blocks of the partial isometry in the joint left polar decomposition.
Source: arXiv:1010.3732, eq. (1d-iso:polardec), lines 579--584. -/
noncomputable def leftPolarBlocks (A : (j : Fin r) → MPSTensor d (dim j)) :
    (j : Fin r) → MPSTensor d (dim j) :=
  fun j i a b => Matrix.leftPolarIso (blockPhysicalMatrix A) i ⟨j, a, b⟩

/-- The joint positive physical factor of a block tensor, extended by the
identity outside the physical support. Source: arXiv:1010.3732, lines 579--584. -/
noncomputable def leftPolarPhysicalFactor (A : (j : Fin r) → MPSTensor d (dim j)) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.leftPolarPos (blockPhysicalMatrix A)

/-- The physical factor constructed from the original tensor is positive
definite. Source: arXiv:1010.3732, lines 579--584. -/
theorem leftPolarPhysicalFactor_posDef (A : (j : Fin r) → MPSTensor d (dim j)) :
    (leftPolarPhysicalFactor A).PosDef :=
  Matrix.posDef_leftPolarPos (blockPhysicalMatrix A)

/-- The original blocks are recovered from their joint isometric form by
the constructed positive physical factor.
Source: arXiv:1010.3732, eq. (1d-iso:polardec). -/
theorem rotatePhysical_leftPolarPhysicalFactor_leftPolarBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (j : Fin r) :
    rotatePhysical (leftPolarPhysicalFactor A) (leftPolarBlocks A j) = A j := by
  ext i a b
  simpa [rotatePhysical, leftPolarPhysicalFactor, leftPolarBlocks,
    Matrix.mul_apply, Matrix.sum_apply, blockPhysicalMatrix] using
      congrFun (congrFun (Matrix.leftPolarPos_mul_leftPolarIso (blockPhysicalMatrix A)) i)
        ⟨j, a, b⟩

/-- The joint left polar decomposition preserves simultaneous spanning at
every length. Source: arXiv:1010.3732, lines 589--597 and Appendix A. -/
theorem wordTupleSpanTop_leftPolarBlocks_iff
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    WordTupleSpanTop (leftPolarBlocks A) L ↔ WordTupleSpanTop A L := by
  simpa only [rotatePhysical_leftPolarPhysicalFactor_leftPolarBlocks] using
    (wordTupleSpanTop_rotatePhysical_iff (leftPolarPhysicalFactor A)
      (leftPolarPhysicalFactor_posDef A).isUnit (leftPolarBlocks A) L).symm

/-- The joint physical map of the left polar blocks is the partial isometry
in the left polar decomposition. Source: arXiv:1010.3732, lines 579--584. -/
theorem blockPhysicalMatrix_leftPolarBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    blockPhysicalMatrix (leftPolarBlocks A) = Matrix.leftPolarIso (blockPhysicalMatrix A) := rfl

/-- The left polar blocks are coisometric on the physical support.
Source: arXiv:1010.3732, lines 579--584. -/
theorem blockPhysicalMatrix_leftPolarBlocks_mul_conjTranspose
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    blockPhysicalMatrix (leftPolarBlocks A) * (blockPhysicalMatrix (leftPolarBlocks A))ᴴ =
      Matrix.polarSupport (blockPhysicalMatrix A)ᴴ := by
  exact Matrix.leftPolarIso_mul_conjTranspose (blockPhysicalMatrix A)

/-- The affine path from the joint isometric form to the original blocks.
Source: arXiv:1010.3732, lines 589--594. -/
noncomputable def isometricDeformationBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (γ : unitInterval) :
    (j : Fin r) → MPSTensor d (dim j) :=
  fun j => rotatePhysical (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ)
    (leftPolarBlocks A j)

/-- The isometric deformation starts at the joint left polar isometry.
Source: arXiv:1010.3732, lines 589--594. -/
@[simp] theorem isometricDeformationBlocks_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    isometricDeformationBlocks A 0 = leftPolarBlocks A := by
  exact funext fun j => by simp [isometricDeformationBlocks]

/-- The isometric deformation ends at the original blocks, without a
supplied polar factor. Source: arXiv:1010.3732, lines 589--594. -/
@[simp] theorem isometricDeformationBlocks_one
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    isometricDeformationBlocks A 1 = A := by
  exact funext fun j => by
    simp [isometricDeformationBlocks,
      rotatePhysical_leftPolarPhysicalFactor_leftPolarBlocks]

/-- The constructed isometric path is continuous at every block.
Source: arXiv:1010.3732, lines 589--594. -/
theorem continuous_isometricDeformationBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (j : Fin r) :
    Continuous fun γ : unitInterval => isometricDeformationBlocks A γ j := by
  exact continuous_rotatePhysical_family _ (fun _ => leftPolarBlocks A j)
    (continuous_positivePhysicalDeformation (leftPolarPhysicalFactor A)) continuous_const

/-- Simultaneous spanning persists throughout the constructed isometric
path. Source: arXiv:1010.3732, lines 594--597 and Appendix A. -/
theorem wordTupleSpanTop_isometricDeformationBlocks_iff
    (A : (j : Fin r) → MPSTensor d (dim j)) (γ : unitInterval) (L : ℕ) :
    WordTupleSpanTop (isometricDeformationBlocks A γ) L ↔ WordTupleSpanTop A L := by
  exact (wordTupleSpanTop_rotatePhysical_iff
    (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ)
    (positivePhysicalDeformation_isUnit _ (leftPolarPhysicalFactor_posDef A) γ)
    (leftPolarBlocks A) L).trans (wordTupleSpanTop_leftPolarBlocks_iff A L)

/-- The source's positive two-site interaction along the constructed
isometric path. Source: arXiv:1010.3732, lines 610--625. -/
noncomputable def isometricDeformationInteractionES
    (A : (j : Fin r) → MPSTensor d (dim j)) (γ : unitInterval) :
    EuclideanSpace ℂ (Cfg d 2) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  positiveDeformedParentInteractionES (leftPolarPhysicalFactor A)
    (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) γ

variable [NeZero d] [∀ j, NeZero (dim j)]

omit [NeZero d] [∀ j, NeZero (dim j)] in
/-- The positive interactions of the constructed isometric deformation
vary continuously in operator norm.
Source: arXiv:1010.3732, lines 610--628. -/
theorem continuous_isometricDeformationInteractionES
    (A : (j : Fin r) → MPSTensor d (dim j)) :
    Continuous (isometricDeformationInteractionES A) := by
  exact continuous_deformedInteraction_positivePhysicalDeformation
    (leftPolarPhysicalFactor A) (leftPolarPhysicalFactor_posDef A) 2
    (parentInteractionES (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) 2)

omit [NeZero d] [∀ j, NeZero (dim j)] in
/-- The constructed interaction is positive and its kernel is exactly the
two-site ground space along the constructed path.
Source: arXiv:1010.3732, lines 623--625. -/
theorem isParentInteraction_isometricDeformationInteractionES
    (A : (j : Fin r) → MPSTensor d (dim j)) (γ : unitInterval) :
    IsParentInteraction (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2
      (isometricDeformationInteractionES A γ).toLinearMap := by
  change IsParentInteraction
    (toTensorFromBlocks (fun _ => 1) (fun j =>
      rotatePhysical (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ)
        (leftPolarBlocks A j))) 2 _
  rw [← rotatePhysical_toTensorFromBlocks]
  exact isParentInteraction_positiveDeformedParentInteractionES (leftPolarPhysicalFactor A)
    (leftPolarPhysicalFactor_posDef A) (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) γ

/-- The canonical two-site parents of the constructed isometric path have
a positive gap uniform in the path parameter and every ring of length at
least two. The positive polar factor is derived from the original tensor.
Source: arXiv:1010.3732, lines 575--625 and Appendix A. -/
theorem exists_uniform_isometricDeformation_parent_gap
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N v‖ := by
  exact exists_uniform_parentHamiltonianES_gap_positivePhysicalDeformation
    (leftPolarBlocks A) ((wordTupleSpanTop_leftPolarBlocks_iff A 1).2 hSpan)
    (fun _ => 1) (by simp) (leftPolarPhysicalFactor A) (leftPolarPhysicalFactor_posDef A)

/-- The source's positive interactions along the constructed isometric
path have a gap uniform in the parameter and every ring of length at least
two. Source: arXiv:1010.3732, lines 575--625 and Appendix A. -/
theorem exists_uniform_isometricDeformation_interaction_gap
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (isometricDeformationInteractionES A γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (isometricDeformationInteractionES A γ).toLinearMap N v‖ := by
  exact exists_uniform_positiveDeformedParentInteractionES_gap
    (leftPolarBlocks A) ((wordTupleSpanTop_leftPolarBlocks_iff A 1).2 hSpan)
    (fun _ => 1) (by simp) (leftPolarPhysicalFactor A) (leftPolarPhysicalFactor_posDef A)

omit [∀ j, NeZero (dim j)] in
/-- Pairwise inequivalent normal blocks admit a finite initial blocking
after which their constructed isometric deformation has a uniform positive
parent-Hamiltonian gap. The blocking length satisfies
\(L+1\leq3\max(\sum_jD_j,1)^5\).
Source: arXiv:1010.3732, lines 575--625 and Appendix A; the dimension bound
is the blocking estimate of arXiv:1606.00608, lines 317--345. -/
theorem exists_blocked_isometricDeformation_parent_gap_of_isNormalTensor
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hNormal : ∀ j, IsNormalTensor (A j)) (hDistinct : BlocksNotGaugePhaseEquiv A) :
    ∃ L : ℕ, 0 < L ∧ L + 1 ≤ 3 * (max (∑ j, dim j) 1) ^ 5 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
        ∀ v ∈ (LinearMap.ker (parentHamiltonianES
          (toTensorFromBlocks (fun _ => 1)
            (isometricDeformationBlocks (fun j => blockTensor (A j) L) γ)) 2 N))ᗮ,
          δ * ‖v‖ ≤ ‖parentHamiltonianES
            (toTensorFromBlocks (fun _ => 1)
              (isometricDeformationBlocks (fun j => blockTensor (A j) L) γ)) 2 N v‖ := by
  let : ∀ j, NeZero (dim j) := fun j => ⟨(hNormal j).bondDim_ne_zero⟩
  obtain ⟨L, hL, hBound, hSpan⟩ :=
    exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor
      A (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (le_max_left _ _) hNormal hDistinct
  exact ⟨L, hL, hBound, exists_uniform_isometricDeformation_parent_gap
    (fun j => blockTensor (A j) L) (wordTupleSpanTop_blockTensor_one A hSpan)⟩

end MPSTensor
