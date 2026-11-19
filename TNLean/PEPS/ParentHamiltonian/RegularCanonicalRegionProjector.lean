/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionalProjectorRange
import TNLean.PEPS.ParentHamiltonian.CoordinateRangeProjector
import TNLean.PEPS.ParentHamiltonian.VertexVirtualParentTransport
import TNLean.PEPS.ParentHamiltonian.DependentRegionCoordinates

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

omit [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
/-- The slice of a global vector along a complementary configuration is the slice, in the
regional contraction's coordinates, of the same vector read on the full-region configurations. -/
private theorem dependentRegionSlice_comp_dependentGlobalConfigEquiv (R : Finset V)
    (x : ManyBody.Config (fun v => IncidentEdge Γ v → G) → ℂ)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ
        (x ∘ (dependentGlobalConfigEquiv (Out := fun v => IncidentEdge Γ v → G))) =
      placeSlice R (fun w ↦ τ ⟨w.1, by simp [w.2]⟩) x := by
  funext α
  change x (dependentGlobalConfigEquiv (Out := fun v => IncidentEdge Γ v → G)
    (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R α τ)) = x _
  congr 1

/-- The placed actual regional range projector is the explicit commuting constraint product of
the regional contraction, read on the global configurations. -/
theorem place_regularCanonicalRegionRangeProjector (R : Finset V) :
    ManyBody.place (X := fun v => IncidentEdge Γ v → G) R
        (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R) =
      Matrix.reindex (dependentGlobalConfigEquiv (Out := fun v => IncidentEdge Γ v → G))
        (dependentGlobalConfigEquiv (Out := fun v => IncidentEdge Γ v → G))
        (regularGlobalRegionConstraint (Γ := Γ) (G := G) R) := by
  classical
  let e := dependentGlobalConfigEquiv (V := V) (Out := fun v => IncidentEdge Γ v → G)
  let C := regularGlobalRegionConstraint (Γ := Γ) (G := G) R
  have hC := regularGlobalRegionConstraint_isStarProjection (Γ := Γ) (G := G) R
  have hL := isStarProjection_place (Out := fun v => IncidentEdge Γ v → G) R
    (coordinateRangeProjector_isStarProjection
      (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R).mulVecLin.range)
  have hQ : IsStarProjection (Matrix.reindex e e C) := by
    rw [isStarProjection_iff'] at hC ⊢
    refine ⟨?_, ?_⟩
    · rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hC.1]
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
        ← Matrix.star_eq_conjTranspose, hC.2]
  -- membership in either range is a condition on all complementary slices
  have hfix (M : Matrix (ManyBody.Config (fun v => IncidentEdge Γ v → G))
      (ManyBody.Config (fun v => IncidentEdge Γ v → G)) ℂ) (hM : IsStarProjection M) (x) :
      x ∈ M.mulVecLin.range ↔ M *ᵥ x = x := by
    constructor
    · rintro ⟨y, rfl⟩
      change M *ᵥ (M *ᵥ y) = M *ᵥ y
      rw [Matrix.mulVec_mulVec, hM.isIdempotentElem.eq]
    · exact fun h ↦ ⟨x, h⟩
  apply matrix_eq_of_isStarProjection_range_eq hL hQ
  ext x
  rw [hfix _ hL, hfix _ hQ, place_mulVec_eq_self_iff]
  have hQx : Matrix.reindex e e C *ᵥ x = x ↔ C *ᵥ (x ∘ e) = x ∘ e := by
    constructor
    · intro h
      have := congrArg (· ∘ e) h
      simpa [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_def] using this
    · intro h
      have := congrArg (· ∘ e.symm) h
      simpa [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_def] using this
  rw [hQx]
  have hCx : C *ᵥ (x ∘ e) = x ∘ e ↔ x ∘ e ∈ regularGlobalRegionRange R := by
    rw [← range_regularGlobalRegionConstraint]
    exact ⟨fun h ↦ ⟨x ∘ e, h⟩, fun ⟨y, hy⟩ ↦ by
      rw [← hy]
      change C *ᵥ (C *ᵥ y) = C *ᵥ y
      rw [Matrix.mulVec_mulVec, hC.isIdempotentElem.eq]⟩
  rw [hCx, mem_regularGlobalRegionRange_iff]
  let c : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R) ≃
      ManyBody.ComplConfig (fun v => IncidentEdge Γ v → G) R :=
    { toFun := fun τ w ↦ τ ⟨w.1, by simp [w.2]⟩
      invFun := fun τ w ↦ τ ⟨w.1, (Finset.mem_sdiff.mp w.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simp only [e, dependentRegionSlice_comp_dependentGlobalConfigEquiv]
  rw [c.forall_congr_left]
  refine forall_congr' fun τ ↦ ?_
  rw [coordinateRangeProjector_mulVec_eq_self_iff]
  rfl

/-- Orthogonal projectors onto actual canonical regular regional ranges commute
for arbitrary overlapping regions of the original graph. -/
theorem regularCanonicalRegionRangeProjector_lifts_commute (R S : Finset V) :
    Commute (ManyBody.place (X := fun v => IncidentEdge Γ v → G) R
      (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R))
      (ManyBody.place (X := fun v => IncidentEdge Γ v → G) S
        (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) S)) := by
  rw [place_regularCanonicalRegionRangeProjector, place_regularCanonicalRegionRangeProjector]
  exact (regularGlobalRegionConstraint_commute R S).map
    (Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalConfigEquiv (Out := fun v => IncidentEdge Γ v → G)))

end TNLean.PEPS
