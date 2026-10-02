/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionEntropyBound
import TNLean.PEPS.TorusSingletonRegion

/-!
# Physical supports of regular G-injective torus regions

Every single-site cut of a native square torus has connected complementary
regions and four crossing bonds. Thus the single-site physical density of
regular G-injective tensors has rank `|G|^3`, and its normalized entropy is
at most `3 log |G|`. Equal closed vectors have equal local ground spaces;
even descriptions by two different finite groups determine the same group
order. These assertions require no separately supplied connectivity or
nonvanishing hypotheses.

Positive bounded coordinate rectangles whose side lengths are smaller than
the two torus periods likewise have connected complementary regions, so their
physical support is their entire regional ground space.

**Scope restriction (regular native torus):** Both periods are at least three,
and the virtual spaces carry regular finite-group labels. The semi-regular
case and smaller periodic networks are not included; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 5.2 and
Corollary 6.10, local source lines 1318–1358 and 2074–2090. These are
auxiliary necessary local relations toward a regular G-injective Fundamental
Theorem; no factorization into individual bond gauges is asserted.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Numbering the four actual crossing bonds of a one-site torus region.
Source: SCP10, the square-lattice construction at lines 1935–1990. -/
noncomputable def torusSingletonBoundaryEquiv (v : X) :
    {f : Edge Γₜ // IsRegionBoundaryEdge {v} f} ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (card_regionBoundaryEdge_torus_singleton v)

variable {G : Type*} [Group G] [Fintype G] {d : ℕ}

/-- Every single-site physical support of a regular G-injective square-torus
PEPS is exactly its local ground space. Source: SCP10, Lemma 5.2 and
Corollary 6.10, lines 1318–1358 and 2074–2090. -/
theorem range_regionReducedDensity_torus_singleton_of_regular
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (v : X) :
    (Matrix.mulVecLin (regionReducedDensity (groupBondTensor a) {v})).range =
      regionGroundSpace (groupBondTensor a) {v} :=
  range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected_cut
    a ha {v} (torusGraph_singleton_connected v) (torusGraph_compl_singleton_connected v)
    3 (torusSingletonBoundaryEquiv v)

/-- The one-site physical density of a regular G-injective square-torus
PEPS has rank the cube of the group order. Source: SCP10, the regular
boundary count in Corollary 6.10, lines 2074–2090. -/
theorem rank_regionReducedDensity_torus_singleton_of_regular
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (v : X) :
    (regionReducedDensity (groupBondTensor a) {v}).rank = Fintype.card G ^ 3 :=
  rank_regionReducedDensity_of_regular_connected_cut
    a ha {v} (torusGraph_singleton_connected v) (torusGraph_compl_singleton_connected v)
    3 (torusSingletonBoundaryEquiv v)

/-- A physical site admitting a regular G-injective square-torus description
has at least the cube of the group order in physical dimension. Source:
SCP10, the invariant virtual space in Definition 5.1 and the regular
boundary count in Corollary 6.10, lines 1278–1296 and 2074–2090. -/
theorem card_group_cube_le_physicalDimension_regular_torus
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) :
    Fintype.card G ^ 3 ≤ d := by
  have h := Matrix.rank_le_card_width (regionReducedDensity (groupBondTensor a) {0})
  rw [rank_regionReducedDensity_torus_singleton_of_regular a ha 0] at h
  simpa [RegionPhysicalConfig] using h

/-- The actual closed vector of regular G-injective square-torus tensors
cannot vanish. Source: SCP10, the positive regular boundary rank in
Corollary 6.10, lines 2074–2090. -/
theorem stateCoeff_groupBondTensor_torus_ne_zero_of_regular
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) :
    stateCoeff (groupBondTensor a) ≠ 0 :=
  stateCoeff_groupBondTensor_ne_zero_of_regular_connected_cut a ha {0}
    (torusGraph_singleton_connected 0) (torusGraph_compl_singleton_connected 0)
    3 (torusSingletonBoundaryEquiv 0)

/-- The single-site entropy is bounded by three group logarithms without
isometry or a flat-spectrum assumption. Source: SCP10, Corollary 6.10,
lines 2074–2090, and Wolf Section 8.2 for the entropy-rank bound. -/
theorem entropy_normalizedRegionReducedDensity_torus_singleton_of_regular
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (v : X) :
    let ρ := normalizedRegionReducedDensity (groupBondTensor a) {v}
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤ 3 * Real.log (Fintype.card G : ℝ) ∧
      renyiEntropy ρ hρ 0 = 3 * Real.log (Fintype.card G : ℝ) := by
  classical
  exact entropy_normalizedRegionReducedDensity_of_regular_connected_cut
    a ha {v} (torusGraph_singleton_connected v) (torusGraph_compl_singleton_connected v)
    3 (torusSingletonBoundaryEquiv v)

/-- Equal closed regular G-injective torus states have equal one-site
physical ground spaces. This is an auxiliary necessary local relation
toward a Fundamental Theorem, from SCP10, Lemma 5.2. -/
theorem regionGroundSpace_torus_singleton_eq_of_sameState_regular
    (a b : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (b v)))
    (hAB : SameState (groupBondTensor a) (groupBondTensor b)) (v : X) :
    regionGroundSpace (groupBondTensor a) {v} = regionGroundSpace (groupBondTensor b) {v} :=
  regionGroundSpace_eq_of_sameState_regular_connected a b ha hb hAB torusGraph_connected {v}
    (torusGraph_singleton_connected v) (torusGraph_compl_singleton_connected v)

/-- The closed physical state of a regular G-injective square-torus PEPS
determines the order of the finite virtual group, even between two different
group descriptions. Source: SCP10, regular boundary ranks in Corollary 6.10,
lines 2074–2090. No isomorphism of the groups is claimed. -/
theorem card_group_eq_of_sameState_regular_torus
    {H : Type*} [Group H] [Fintype H]
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (b : (v : X) → (IncidentEdge Γₜ v → H) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (b v)))
    (hAB : SameState (groupBondTensor a) (groupBondTensor b)) :
    Fintype.card G = Fintype.card H := by
  apply card_group_eq_of_sameState_regular_connected_cut a b ha hb hAB {0}
    (torusGraph_singleton_connected 0) (torusGraph_compl_singleton_connected 0)
  rw [card_regionBoundaryEdge_torus_singleton]
  decide

/-- A positive bounded coordinate rectangle with both side lengths shorter
than the periods has its entire regional ground space as the physical
support. Source: SCP10, rectangular regions in lines 1935–1957 and
Corollary 6.10, lines 2074–2090. -/
theorem range_regionReducedDensity_torus_rectangle_of_regular
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v)))
    (xStart yStart xLen yLen : ℕ)
    (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxLen : xLen < width) (hyLen : yLen < height)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    (Matrix.mulVecLin (regionReducedDensity (groupBondTensor a) R)).range =
      regionGroundSpace (groupBondTensor a) R :=
  range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected a ha torusGraph_connected _
    (torusGraph_rectangle_connected xStart yStart xLen yLen hxPos hyPos hxBound hyBound)
    (torusGraph_compl_rectangle_connected xStart yStart xLen yLen hxLen hyLen)

end TNLean.PEPS
