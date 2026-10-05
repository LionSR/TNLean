/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularIsometricSiteImages
import TNLean.PEPS.ParentHamiltonian.ProductSiteProjectorCommutation

/-!
# Commuting physical parent interactions of regular G-isometric PEPS

For locally regular G-isometric tensors on a finite graph, the canonical
orthogonal parent interactions commute on arbitrary overlapping regions.
The proof identifies the actual canonical regular regional ranges, transports
their orthogonal projections through the original rectangular site maps, and
cancels only the nonzero spectator site-image factors outside the union.
No surjectivity onto the ambient physical space is required.

**Scope restriction (finite simple graphs):** Periodic presentations with self-loops or
parallel bonds are not encoded by this graph theorem. In particular, the older two-site
MPS ring convention remains separate; see the gap note below.

Source: Schuch, Cirac, Pérez-García 2010, arXiv:1001.3807, Theorem 6.12,
`Papers/1001.3807/paper_v3.tex`, lines 2131–2153.

**Local fix (complement):** The parent interaction is one minus the actual
local range projector. The source's diagram names the range projector h,
although its stated parent interaction is the complement. See
`docs/paper-gaps/scp10_g_isometric_commuting_parent_hamiltonian.tex`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

omit [DecidableEq G] in
/-- Actual physical range projectors of regular G-isometric PEPS commute on
arbitrary overlapping graph regions. All site-image support and nonzero
spectator conditions are derived from local G-isometry. -/
theorem regularIsometric_regionRangeProjector_lifts_commute
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R S : Finset V) :
    Commute (dependentRegionOperatorLift (Out := fun _ => Fin d) R
        (coordinateRangeProjector (regionGroundSpace (groupBondTensor a) R)))
      (dependentRegionOperatorLift (Out := fun _ => Fin d) S
        (coordinateRangeProjector (regionGroundSpace (groupBondTensor a) S))) := by
  classical
  obtain ⟨L, J, hAL, hJ, hJ0, hJA⟩ := exists_regularIsometric_siteImageProjectors a ha
  exact commute_dependentRegionOperatorLift_of_productSiteTransport R S
    (fun v => Matrix.of fun s α => a v α s) L J _ _
    (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) R)
    (regularCanonicalRegionRangeProjector (Γ := Γ) (G := G) S)
    hAL hJ hJ0 (coordinateRangeProjector_isStarProjection _)
    (coordinateRangeProjector_isStarProjection _)
    (product_siteImages_mul_regionRangeProjector a (fun v => (ha v).toIsGInjective) J hJA R)
    (product_siteImages_mul_regionRangeProjector a (fun v => (ha v).toIsGInjective) J hJA S)
    (regularIsometric_regionRangeProjector_intertwine a ha R)
    (regularIsometric_regionRangeProjector_intertwine a ha S)
    (regularCanonicalRegionRangeProjector_lifts_commute R S)

/-- The canonical parent interaction is an orthogonal projector. -/
theorem canonicalRegionParentInteraction_isStarProjection (A : Tensor Γ d) (R : Finset V) :
    IsStarProjection (canonicalRegionParentInteraction A R) := by
  classical
  apply (isStarProjection_iff').mpr
  constructor
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2]
    simp only [canonicalRegionParentInteraction, LinearEquiv.apply_symm_apply]
    exact (Submodule.isSymmetricProjection_starProjection
      (regionGroundSpaceES A R)ᗮ).isIdempotentElem.eq
  · exact (canonicalRegionParentInteraction_posSemidef A R).isHermitian

/-- The canonical parent interaction is the complement of the coordinate
orthogonal projector onto the actual regional ground space. -/
theorem canonicalRegionParentInteraction_eq_one_sub_rangeProjector
    (A : Tensor Γ d) (R : Finset V) :
    canonicalRegionParentInteraction A R =
      1 - coordinateRangeProjector (regionGroundSpace A R) := by
  classical
  let P := canonicalRegionParentInteraction A R
  have hP : IsStarProjection P := canonicalRegionParentInteraction_isStarProjection A R
  have hrange : (1 - P).mulVecLin.range = regionGroundSpace A R := by
    rw [← ker_canonicalRegionParentInteraction A R]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change P *ᵥ ((1 - P) *ᵥ y) = 0
      rw [Matrix.mulVec_mulVec, hP.mul_one_sub_self, Matrix.zero_mulVec]
    · intro hx
      refine ⟨x, ?_⟩
      change (1 - P) *ᵥ x = x
      change P *ᵥ x = 0 at hx
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_zero]
  have h := eq_coordinateRangeProjector_of_range hP.one_sub _ hrange
  rw [← h]
  exact (sub_sub_cancel 1 P).symm

/-- The two coordinate conventions for extending a physical regional operator agree. -/
theorem regionLocalTerm_eq_dependentRegionOperatorLift (R : Finset V)
    (H : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    regionLocalTerm R H =
      (dependentRegionOperatorLift (Out := fun _ => Fin d) R H).submatrix
        (fullRegionConfigEquiv d) (fullRegionConfigEquiv d) := by
  classical
  ext σ τ
  simp only [regionLocalTerm, dependentRegionOperatorLift, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp [Matrix.kroneckerMap, Matrix.one_apply, regionConfigEquiv, dependentRegionConfigEquiv,
    fullRegionConfigEquiv]

/-- Extending a complementary interaction gives the complement of the extended projector. -/
theorem dependentRegionOperatorLift_one_sub (R : Finset V)
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    dependentRegionOperatorLift (Out := fun _ => Fin d) R (1 - P) =
      1 - dependentRegionOperatorLift (Out := fun _ => Fin d) R P := by
  classical
  rw [dependentRegionOperatorLift_sub,
    dependentRegionOperatorLift_one (Out := fun _ => Fin d)]

omit [DecidableEq G] in
/-- Source: SCP10, arXiv:1001.3807, Theorem 6.12. The actual canonical physical
parent terms of locally regular G-isometric PEPS commute for any two regions.
The local term is one minus the actual range projector, as required by the
parent-Hamiltonian definition. -/
theorem regularIsometric_canonicalRegionParentInteractions_commute
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R S : Finset V) :
    Commute (regionLocalTerm R (canonicalRegionParentInteraction (groupBondTensor a) R))
      (regionLocalTerm S (canonicalRegionParentInteraction (groupBondTensor a) S)) := by
  classical
  have hrange := regularIsometric_regionRangeProjector_lifts_commute a ha R S
  have hcomp := (Commute.one_right _).sub_right ((Commute.one_left _).sub_left hrange)
  rw [canonicalRegionParentInteraction_eq_one_sub_rangeProjector,
    canonicalRegionParentInteraction_eq_one_sub_rangeProjector,
    regionLocalTerm_eq_dependentRegionOperatorLift,
    regionLocalTerm_eq_dependentRegionOperatorLift,
    dependentRegionOperatorLift_one_sub, dependentRegionOperatorLift_one_sub]
  change _ * _ = _ * _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcomp.eq]

end TNLean.PEPS
