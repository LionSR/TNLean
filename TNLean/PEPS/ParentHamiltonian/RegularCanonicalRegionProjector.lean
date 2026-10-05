/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionalProjectorRange
import TNLean.PEPS.ParentHamiltonian.CoordinateRangeProjector
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift

/-!
# Actual canonical regular regional range projectors commute

The orthogonal projector onto the range of the original regular open-region
matrix, extended by the identity outside the region, is the explicit product
of commuting vertex, edge and flatness constraints. Thus these actual range
projectors commute on arbitrary overlapping graph regions.

This is SCP10, arXiv:1001.3807, Theorem 6.12 in canonical regular half-edge
physical coordinates. Transport to arbitrary G-isometric site maps is separate.
-/

open scoped Matrix Kronecker

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The orthogonal projector onto the actual canonical regular open-region range. -/
noncomputable def regularCanonicalRegionRangeProjector (R : Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  coordinateRangeProjector (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R).mulVecLin.range

/-- The extended actual regional range projector is the explicit commuting constraint product. -/
theorem dependentRegionOperatorLift_regularCanonicalRegionRangeProjector (R : Finset V) :
    dependentRegionOperatorLift (Out := fun v => IncidentEdge Γ v → G) R
        (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R) =
      regularGlobalRegionConstraint (Γ := Γ) (G := G) R := by
  classical
  have hL := dependentRegionOperatorLift_isStarProjection (Out := fun v => IncidentEdge Γ v → G) R
    (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R)
    (coordinateRangeProjector_isStarProjection _)
  apply matrix_eq_of_isStarProjection_range_eq hL (regularGlobalRegionConstraint_isStarProjection R)
  rw [range_regularGlobalRegionConstraint]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_regularGlobalRegionRange_iff]
    intro τ
    apply (coordinateRangeProjector_mulVec_eq_self_iff _ _).mp
    change regularCanonicalRegionRangeProjector R *ᵥ _ = _
    let L := dependentRegionOperatorLift (Out := fun v => IncidentEdge Γ v → G) R
      (regularCanonicalRegionRangeProjector R)
    have hfix : L *ᵥ (L *ᵥ y) = L *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hL.isIdempotentElem.eq]
    exact (dependentRegionOperatorLift_mulVec_eq_self_iff
      (Out := fun v => IncidentEdge Γ v → G) R _ _).mp hfix τ
  · intro hx
    refine ⟨x, ?_⟩
    apply (dependentRegionOperatorLift_mulVec_eq_self_iff
      (Out := fun v => IncidentEdge Γ v → G) R _ _).mpr
    intro τ
    apply (coordinateRangeProjector_mulVec_eq_self_iff _ _).mpr
    exact (mem_regularGlobalRegionRange_iff R x).mp hx τ

/-- Orthogonal projectors onto actual canonical regular regional ranges commute
for arbitrary overlapping regions of the original graph. -/
theorem regularCanonicalRegionRangeProjector_lifts_commute (R S : Finset V) :
    Commute (dependentRegionOperatorLift (Out := fun v => IncidentEdge Γ v → G) R
      (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R))
      (dependentRegionOperatorLift (Out := fun v => IncidentEdge Γ v → G) S
        (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) S)) := by
  rw [dependentRegionOperatorLift_regularCanonicalRegionRangeProjector,
    dependentRegionOperatorLift_regularCanonicalRegionRangeProjector]
  exact regularGlobalRegionConstraint_commute R S

end TNLean.PEPS
