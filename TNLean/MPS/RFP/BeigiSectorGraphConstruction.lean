/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.MPS.MPDO.CommutingBondEtaDecomposition
import TNLean.MPS.RFP.BeigiSectorGraph

/-!
# Constructing Beigi sector data from a commuting parent interaction

This file derives the symmetric two-sided sector coordinates of a nearest-neighbor
commuting parent interaction and packages them as `BeigiSectorGraphData`.

## Main declarations

* `IsNNCPH.nonempty_beigiSectorGraphData`: existence of Beigi's finite sector graph data;
* `IsNNCPH.beigiSectorGraphData`: a chosen source-faithful sector graph datum.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III, equation (2).
-/

open scoped ComplexOrder Kronecker Matrix MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The canonical two-site parent interaction is an orthogonal projection.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section II, paragraph before Lemma 2.1, and
Section III, equation (2). -/
theorem twoSiteParentInteractionMatrix_isStarProjection (A : MPSTensor d D) :
    IsStarProjection (twoSiteParentInteractionMatrix A) := by
  rw [isStarProjection_iff']
  constructor
  · have h := congrArg LinearMap.toMatrix' (parentInteraction_idempotent A 2)
    simp only [LinearMap.toMatrix'_mul] at h
    rw [twoSiteParentInteractionMatrix]
    change (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))) (LinearMap.toMatrix' (parentInteraction A 2)) *
        (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))) (LinearMap.toMatrix' (parentInteraction A 2)) =
      (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d))) (LinearMap.toMatrix' (parentInteraction A 2))
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))]
    exact congrArg (Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))) h
  · simpa [Matrix.star_eq_conjTranspose] using
      (twoSiteParentInteractionMatrix_isHermitian A).eq

/-- The complementary two-site parent interaction is an orthogonal projection.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, equation (2). -/
theorem twoSiteParentGroundProjectorMatrix_isStarProjection (A : MPSTensor d D) :
    IsStarProjection (twoSiteParentGroundProjectorMatrix A) := by
  exact (twoSiteParentInteractionMatrix_isStarProjection A).one_sub

/-- The complementary two-site parent interaction is positive semidefinite.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, equation (2). -/
theorem twoSiteParentGroundProjectorMatrix_posSemidef (A : MPSTensor d D) :
    (twoSiteParentGroundProjectorMatrix A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact (twoSiteParentGroundProjectorMatrix_isStarProjection A).nonneg

/-- The two overlapping lifts of the complementary parent interaction commute.

This is the complement form of the local commutator used in Beigi's spatial
decomposition.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III, equation (2). -/
theorem IsNNCPH.twoSiteParentGroundProjectorMatrix_overlappingLifts_commute
    {A : MPSTensor d D} (hNNCPH : IsNNCPH A 3) :
    Matrix.leftOverlappingLift (twoSiteParentGroundProjectorMatrix A) *
        Matrix.rightOverlappingLift (twoSiteParentGroundProjectorMatrix A) =
      Matrix.rightOverlappingLift (twoSiteParentGroundProjectorMatrix A) *
        Matrix.leftOverlappingLift (twoSiteParentGroundProjectorMatrix A) := by
  let H := twoSiteParentInteractionMatrix A
  have hLeft : Matrix.leftOverlappingLift (c := Fin d) (1 - H) =
      1 - Matrix.leftOverlappingLift (c := Fin d) H := by
    ext x y
    simp [Matrix.leftOverlappingLift, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  have hRight : Matrix.rightOverlappingLift (a := Fin d) (1 - H) =
      1 - Matrix.rightOverlappingLift (a := Fin d) H := by
    ext x y
    simp [Matrix.rightOverlappingLift, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  rw [twoSiteParentGroundProjectorMatrix, hLeft, hRight]
  have hComm := hNNCPH.twoSiteParentInteractionMatrix_overlappingLifts_commute
  calc
    (1 - Matrix.leftOverlappingLift H) * (1 - Matrix.rightOverlappingLift H) =
        1 - Matrix.leftOverlappingLift H - Matrix.rightOverlappingLift H +
          Matrix.leftOverlappingLift H * Matrix.rightOverlappingLift H := by
      noncomm_ring
    _ = 1 - Matrix.leftOverlappingLift H - Matrix.rightOverlappingLift H +
          Matrix.rightOverlappingLift H * Matrix.leftOverlappingLift H := by
      rw [hComm]
    _ = (1 - Matrix.rightOverlappingLift H) * (1 - Matrix.leftOverlappingLift H) := by
      noncomm_ring

/-- Idempotence of a block-diagonal eta-pair operator forces idempotence of each
neighboring eta operator. Positivity of the outer dimensions supplies fixed basis
indices. Evaluating `((1 ⊗ₖ η q h) ⊗ₖ 1) ^ 2 = (1 ⊗ₖ η q h) ⊗ₖ 1` at those
indices reduces the block identity to `(η q h) ^ 2 = η q h`. -/
private theorem eta_isIdempotent_of_blockDiagonal_isIdempotent
    {K : ℕ} {dl dr : Fin K → ℕ}
    (hdl : ∀ q, 0 < dl q) (hdr : ∀ q, 0 < dr q)
    (η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ)
    (hBlock : IsIdempotentElem
      (Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ))) :
    ∀ q h, IsIdempotentElem (η q h) := by
  classical
  intro q h
  rw [IsIdempotentElem] at hBlock ⊢
  have hBlocks :
      (fun qh : Fin K × Fin K ↦
        (((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
            η qh.1 qh.2) ⊗ₖ
              (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) *
          (((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
            η qh.1 qh.2) ⊗ₖ
              (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ))) =
        fun qh : Fin K × Fin K ↦
          ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
            η qh.1 qh.2) ⊗ₖ
              (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ) := by
    apply Matrix.blockDiagonal'_injective
    rw [Matrix.blockDiagonal'_mul]
    exact hBlock
  have hSector := congrFun hBlocks (q, h)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul] at hSector
  let l0 : Fin (dl q) := ⟨0, hdl q⟩
  let r0 : Fin (dr h) := ⟨0, hdr h⟩
  ext x y
  have hEntry := congrFun (congrFun hSector ((l0, x), r0)) ((l0, y), r0)
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply, l0, r0] using hEntry

/-- A nearest-neighbor commuting parent interaction determines Beigi's finite sector graph
data in the symmetric two-sided coordinates.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III, equation (2). -/
theorem IsNNCPH.nonempty_beigiSectorGraphData
    {A : MPSTensor d D} (hNNCPH : IsNNCPH A 3) :
    Nonempty (BeigiSectorGraphData A) := by
  classical
  obtain ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hηpos, hηblock⟩ :=
    Matrix.exists_positive_etaPair_decomposition_of_overlappingLifts_commute
      (twoSiteParentGroundProjectorMatrix A)
      (twoSiteParentGroundProjectorMatrix_posSemidef A)
      hNNCPH.twoSiteParentGroundProjectorMatrix_overlappingLifts_commute
  have hUU : (U ⊗ₖ U) ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    Matrix.kronecker_mem_unitary hU hU
  have hConj : IsStarProjection
      (star (U ⊗ₖ U) * twoSiteParentGroundProjectorMatrix A * (U ⊗ₖ U)) := by
    have h := IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
      (twoSiteParentGroundProjectorMatrix_isStarProjection A) (U ⊗ₖ U)
      (Matrix.mem_unitaryGroup_iff.mp hUU)
    simpa [Matrix.star_eq_conjTranspose] using h
  have hReindexed : IsIdempotentElem
      (Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm
        (star (U ⊗ₖ U) * twoSiteParentGroundProjectorMatrix A * (U ⊗ₖ U))) := by
    rw [IsIdempotentElem]
    rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact congrArg
      (Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm)
      hConj.isIdempotentElem.eq
  have hBlockIdem : IsIdempotentElem
      (Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) := by
    rw [← hηblock]
    exact hReindexed
  have hηidem := eta_isIdempotent_of_blockDiagonal_isIdempotent hdl hdr η hBlockIdem
  exact ⟨{
    sectorCount := K
    leftDim := dl
    rightDim := dr
    sectorEquiv := e
    unitary := U
    unitary_mem := hU
    edgeProjector := η
    edgeProjector_isOrthogonal := fun q h ↦ ⟨(hηpos q h).isHermitian, hηidem q h⟩
    groundProjector_block := hηblock }⟩

/-- A chosen Beigi sector graph datum for a nearest-neighbor commuting parent interaction.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III, equation (2). -/
noncomputable def IsNNCPH.beigiSectorGraphData
    {A : MPSTensor d D} (hNNCPH : IsNNCPH A 3) : BeigiSectorGraphData A :=
  Classical.choice hNNCPH.nonempty_beigiSectorGraphData

end MPSTensor
