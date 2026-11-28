/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Kronecker.CommutingDecomposition
import TNLean.MPS.ParentHamiltonian.Commuting.Defs
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import TNLean.MPS.ParentHamiltonian.Commuting.KroneckerTransport

/-!
# Spatial decomposition of the two-site parent interaction

This file places the canonical two-site parent interaction in the coordinates
used by the Bravyi--Vyalyi decomposition.  On three sites, nearest-neighbor
commutation says that the two overlapping lifts of this Hermitian matrix
commute.  Beigi's spatial decomposition therefore applies directly.

## Main declarations

* `twoSiteParentInteractionMatrix`: the canonical two-site parent interaction
  in ordered-pair coordinates;
* `IsNNCPH.twoSiteParentInteractionMatrix_isHermitian_and_overlappingLifts_commute`:
  the Hermitian commuting-overlap input to the spatial decomposition;
* `IsNNCPH.exists_unitary_blockActions_of_twoSiteParentInteractionMatrix`:
  the resulting unitary block actions on the middle physical site.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Sections II--IV.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Theorem 3.10, lines 534--540.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-! ### Coordinate transport -/

/-- The common left-associated coordinates for three consecutive physical sites.
The equivalence sends a configuration `x` to `((x 0, x 1), x 2)`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
def threeSiteParentInteractionEquiv (n : Type*) :
    (Fin 3 → n) ≃ ((n × n) × n) :=
  (finThreeArrowEquiv n).trans (Equiv.prodAssoc n n n).symm

/-- In common left-associated three-site coordinates, the first-pair lift of a
two-site operator is its left overlapping matrix lift.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem leftPairLift_toMatrix_reindex_leftAssociated
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    Matrix.reindex (threeSiteParentInteractionEquiv α)
        (threeSiteParentInteractionEquiv α)
        (LinearMap.toMatrix' (leftPairLift Q)) =
      Matrix.leftOverlappingLift
        (Matrix.reindex (finTwoArrowEquiv α)
          (finTwoArrowEquiv α) (LinearMap.toMatrix' Q)) := by
  classical
  rw [threeSiteParentInteractionEquiv]
  change Matrix.reindex (Equiv.prodAssoc α α α).symm
      (Equiv.prodAssoc α α α).symm
      (Matrix.reindex (finThreeArrowEquiv α)
        (finThreeArrowEquiv α)
        (LinearMap.toMatrix' (leftPairLift Q))) = _
  rw [leftPairLift_toMatrix_reindex]
  ext p q
  simp [appendixBLeftPairMatrixAux, Matrix.leftOverlappingLift,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply]

/-- In common left-associated three-site coordinates, the final-pair lift of a
two-site operator is its right overlapping matrix lift.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem rightPairLift_toMatrix_reindex_leftAssociated
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    Matrix.reindex (threeSiteParentInteractionEquiv α)
        (threeSiteParentInteractionEquiv α)
        (LinearMap.toMatrix' (rightPairLift Q)) =
      Matrix.rightOverlappingLift
        (Matrix.reindex (finTwoArrowEquiv α)
          (finTwoArrowEquiv α) (LinearMap.toMatrix' Q)) := by
  classical
  rw [threeSiteParentInteractionEquiv]
  change Matrix.reindex (Equiv.prodAssoc α α α).symm
      (Equiv.prodAssoc α α α).symm
      (Matrix.reindex (finThreeArrowEquiv α)
        (finThreeArrowEquiv α)
        (LinearMap.toMatrix' (rightPairLift Q))) = _
  rw [rightPairLift_toMatrix_reindex]
  ext p q
  simp [appendixBRightPairMatrixAux, Matrix.rightOverlappingLift,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply]

/-! ### The canonical interaction and its overlapping lifts -/

/-- The canonical two-site parent interaction in ordered-pair coordinates.

Source: arXiv:1606.00608, Definition 3.9 and Theorem 3.10, lines 517--540. -/
noncomputable def twoSiteParentInteractionMatrix (A : MPTensor α (Fin D)) :
    Matrix (α × α) (α × α) ℂ :=
  Matrix.reindex (finTwoArrowEquiv α) (finTwoArrowEquiv α)
    (LinearMap.toMatrix' (parentInteraction A 2))

/-- The canonical two-site parent interaction matrix is Hermitian.

Source: arXiv:1606.00608, Definition 3.9, lines 517--525. -/
theorem twoSiteParentInteractionMatrix_isHermitian (A : MPTensor α (Fin D)) :
    (twoSiteParentInteractionMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.reindex
  exact (isStarProjection_toMatrix'_parentInteraction A 2).isSelfAdjoint.isHermitian

/-- On three sites, nearest-neighbor parent commutation becomes commutation of
the two natural overlapping lifts of the canonical two-site interaction.

Source: arXiv:1606.00608, Theorem 3.10, lines 534--540; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem IsNNCPH.twoSiteParentInteractionMatrix_overlappingLifts_commute
    {A : MPTensor α (Fin D)} (hNNCPH : IsNNCPH A 3) :
    Matrix.leftOverlappingLift (twoSiteParentInteractionMatrix A) *
        Matrix.rightOverlappingLift (twoSiteParentInteractionMatrix A) =
      Matrix.rightOverlappingLift (twoSiteParentInteractionMatrix A) *
        Matrix.leftOverlappingLift (twoSiteParentInteractionMatrix A) := by
  have hComm := hNNCPH (0 : Fin 3) (1 : Fin 3)
  rw [term_two_three_zero_eq_leftPairLift_parentInteraction,
    term_two_three_one_eq_rightPairLift_parentInteraction] at hComm
  have hMatrix := congrArg LinearMap.toMatrix' hComm
  simp only [LinearMap.toMatrix'_mul] at hMatrix
  let e := threeSiteParentInteractionEquiv α
  rw [twoSiteParentInteractionMatrix,
    ← leftPairLift_toMatrix_reindex_leftAssociated,
    ← rightPairLift_toMatrix_reindex_leftAssociated]
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (LinearMap.toMatrix' (leftPairLift (parentInteraction A 2))) *
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (LinearMap.toMatrix' (rightPairLift (parentInteraction A 2))) =
    (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (LinearMap.toMatrix' (rightPairLift (parentInteraction A 2))) *
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (LinearMap.toMatrix' (leftPairLift (parentInteraction A 2)))
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  exact congrArg (Matrix.reindex e e) hMatrix

/-- The canonical two-site interaction is Hermitian, and its two overlapping
lifts commute on three sites.

This is exactly the local input to the spatial decomposition of Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem IsNNCPH.twoSiteParentInteractionMatrix_isHermitian_and_overlappingLifts_commute
    {A : MPTensor α (Fin D)} (hNNCPH : IsNNCPH A 3) :
    (twoSiteParentInteractionMatrix A).IsHermitian ∧
      Matrix.leftOverlappingLift (twoSiteParentInteractionMatrix A) *
          Matrix.rightOverlappingLift (twoSiteParentInteractionMatrix A) =
        Matrix.rightOverlappingLift (twoSiteParentInteractionMatrix A) *
          Matrix.leftOverlappingLift (twoSiteParentInteractionMatrix A) :=
  ⟨twoSiteParentInteractionMatrix_isHermitian A,
    hNNCPH.twoSiteParentInteractionMatrix_overlappingLifts_commute⟩

/-! ### Bravyi--Vyalyi spatial block actions -/

/-- The canonical two-site parent interaction admits Beigi's explicit unitary
block-action decomposition on the middle physical site.

Source: Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3;
arXiv:1606.00608, Theorem 3.10, lines 534--540. -/
theorem IsNNCPH.exists_unitary_blockActions_of_twoSiteParentInteractionMatrix
    {A : MPTensor α (Fin D)} (hNNCPH : IsNNCPH A 3) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ α)
      (U : Matrix α α ℂ)
      (R : ∀ q, Matrix (α × Fin (dl q)) (α × Fin (dl q)) ℂ)
      (S : ∀ q, Matrix (Fin (dr q) × α) (Fin (dr q) × α) ℂ),
      U ∈ Matrix.unitaryGroup α ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q, (R q).IsHermitian) ∧ (∀ q, (S q).IsHermitian) ∧
        Matrix.reindex (Matrix.leftSpatialBlockEquiv e).symm
            (Matrix.leftSpatialBlockEquiv e).symm
            (star ((1 : Matrix α α ℂ) ⊗ₖ U) *
              twoSiteParentInteractionMatrix A *
              ((1 : Matrix α α ℂ) ⊗ₖ U)) =
          (Matrix.blockDiagonal' fun q =>
            R q ⊗ₖ (1 : Matrix (Fin (dr q)) (Fin (dr q)) ℂ)) ∧
        Matrix.reindex (Matrix.rightSpatialBlockEquiv e).symm
            (Matrix.rightSpatialBlockEquiv e).symm
            (star (U ⊗ₖ (1 : Matrix α α ℂ)) *
              twoSiteParentInteractionMatrix A *
              (U ⊗ₖ (1 : Matrix α α ℂ))) =
          (Matrix.blockDiagonal' fun q =>
            (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) ⊗ₖ S q) := by
  rcases hNNCPH.twoSiteParentInteractionMatrix_isHermitian_and_overlappingLifts_commute
    with ⟨hHermitian, hComm⟩
  exact Matrix.exists_unitary_blockActions_of_overlappingLifts_commute
    (twoSiteParentInteractionMatrix A) (twoSiteParentInteractionMatrix A)
    hHermitian hHermitian hComm

end MPSTensor
