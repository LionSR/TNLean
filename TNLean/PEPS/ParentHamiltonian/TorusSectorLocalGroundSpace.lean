/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionSupport
import TNLean.PEPS.RegularTorusEntropy

/-!
# Torus closures in local regional ground spaces

Bond insertions outside the edges incident to a region preserve its open-region
ground space. Thus every physical slice of the resulting closed tensor lies
in the original regional ground space. On a native torus this applies to every
holonomy closure and every coherent sum of closures on a rectangle strictly
interior to the coordinate intervals. All original regional parent interactions
annihilate these states. Isometry, G-injectivity, and commutativity of closure
elements are not needed for these local membership statements.

**Scope restriction (interior regular cuts):** Both periods are at least three,
the virtual coordinates are regular group labels, and the rectangle has no
incident seam bond. Global ground-space classification and regions meeting a
seam are not asserted; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the closure construction
in Theorem 5.5 and `eq:2d:peps-with-ug-uh`, local source lines 1440–1545 and
1935–1990. These are auxiliary local membership consequences, rather than the
full torus ground-space classification.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- Complementary regular bond insertions preserve the regional physical
ground space. Source: SCP10, closure deformation away from a local region
in the proof of Theorem 5.5 and lines 1935–1990. -/
theorem regionGroundSpace_regularTwistedSite_eq_of_trivial_on_incident
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : Edge Γ → G)
    (R : Finset V) (hu : ∀ f : Edge Γ, IsRegionIncidentEdge R f → u f = 1) :
    regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  let e := Fintype.equivFin {f : Edge Γ // IsRegionBoundaryEdge R f}
  rw [← range_regularOpenRegionMatrix_eq_regionGroundSpace (regularTwistedSite a u) R e,
    ← range_regularOpenRegionMatrix_eq_regionGroundSpace a R e]
  exact congrArg (fun M => (Matrix.mulVecLin M).range)
    (regularTwistedOpenRegionMatrix_eq_of_trivial_on_incident a u R hu e)

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)] [DecidableEq G]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height

/-- Every native holonomy closure has all local physical slices in the
original ground space on a strictly interior rectangle. Source: SCP10,
local closure construction in Theorem 5.5 and lines 1935–1990. -/
theorem torusGClosure_slice_mem_regionGroundSpace_interior_rectangle
    (a : G → G → G → G → Fin d → ℂ) (g h : G)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
      (fun σ => torusGClosure (leftRegularMatrix G) a g h (assembleRegionσ R σ τ)) ∈
        regionGroundSpace (groupBondTensor (torusIncidentSite a)) R := by
  intro R τ
  have hslice := stateCoeff_slice_mem_regionGroundSpace
    (groupBondTensor
      (regularTwistedSite (torusIncidentSite a) (torusClosureEdgeAssignment g h))) R τ
  rw [regionGroundSpace_regularTwistedSite_eq_of_trivial_on_incident _ _ R
    (torusClosureEdgeAssignment_eq_one_on_rectangle_incident
      g h xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd)] at hslice
  simpa only [torusGClosure_eq_stateCoeff_twisted] using hslice

/-- Arbitrary coherent sums of native closures retain their original
interior regional ground-space slices. Source: SCP10, linear span of
closure states in Theorem 5.5 and the rectangular cut in lines 1935–1990. -/
theorem torusGClosure_sum_slice_mem_regionGroundSpace_interior_rectangle
    {I : Type*} [Fintype I]
    (a : G → G → G → G → Fin d → ℂ) (pairs : I → G × G) (μ : I → ℂ)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
      (fun σ => (∑ i, μ i • torusGClosure (leftRegularMatrix G) a (pairs i).1 (pairs i).2)
        (assembleRegionσ R σ τ)) ∈ regionGroundSpace (groupBondTensor (torusIncidentSite a)) R := by
  intro R τ
  have hs (i : I) := torusGClosure_slice_mem_regionGroundSpace_interior_rectangle
    a (pairs i).1 (pairs i).2 xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd τ
  have hsum := Submodule.sum_mem (regionGroundSpace (groupBondTensor (torusIncidentSite a)) R)
    (fun i (_ : i ∈ Finset.univ) => Submodule.smul_mem _ (μ i) (hs i))
  convert hsum using 1
  ext σ
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

/-- Every original parent interaction on a strict interior rectangle
annihilates every coherent closure superposition. Source: SCP10, local
parent constraints on the closure span in Theorem 5.5, lines 1440–1545. -/
theorem regionLocalTerm_torusGClosure_sum_eq_zero_interior_rectangle
    {I : Type*} [Fintype I]
    (a : G → G → G → G → Fin d → ℂ) (pairs : I → G × G) (μ : I → ℂ)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    ∀ hR : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      IsRegionParentInteraction (groupBondTensor (torusIncidentSite a)) R hR →
      regionLocalTerm R hR *ᵥ
        (∑ i, μ i • torusGClosure (leftRegularMatrix G) a (pairs i).1 (pairs i).2) = 0 := by
  intro R hR hh
  exact (regionLocalTerm_mulVec_eq_zero_iff _ R hh _).mpr
    (torusGClosure_sum_slice_mem_regionGroundSpace_interior_rectangle
      a pairs μ xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd)

end TNLean.PEPS
