/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSingletonRegion

/-!
# Native four-leg G-injectivity in incident graph coordinates

The top, right, down, and left virtual labels identify the native four-leg
site map with the site map on the actual incident graph edges. The coordinate
identification intertwines simultaneous regular translation, so G-injectivity
is preserved. No isometry hypothesis is required.

**Scope restriction (regular simple torus):** The virtual representation is
regular and both torus periods are at least three. Smaller tori require
parallel bonds; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1
and the square-lattice construction preceding Theorem 6.9, local source
lines 1278–1296 and 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*}

/-- Native four-leg labels and actual incident-bond labels are bijective.
Source: SCP10, the square-lattice virtual legs in Definition 5.1. -/
noncomputable def torusIncidentCoordinatesEquiv (v : TorusVertex width height) :
    (IncidentEdge (torusGraph width height) v → G) ≃ G × G × G × G :=
  ((torusIncidentLegEquiv v).symm.arrowCongr (Equiv.refl G)).trans (finFourArrowEquiv G)

/-- The coordinate equivalence reads top, right, down, and left labels.
Source: SCP10, the square-lattice construction at lines 1935–1990. -/
theorem torusIncidentCoordinatesEquiv_apply (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → G) :
    torusIncidentCoordinatesEquiv v η = torusIncidentCoordinates v η := rfl

variable [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

omit [Fintype G] [DecidableEq G] in
/-- Native incident coordinates intertwine simultaneous regular translation.
Source: SCP10, invariant virtual action in Definition 5.1. -/
theorem torusIncidentCoordinatesEquiv_smul (v : TorusVertex width height)
    (g : G) (η : IncidentEdge (torusGraph width height) v → G) :
    torusIncidentCoordinatesEquiv v (g • η) = g • torusIncidentCoordinatesEquiv v η := rfl

omit [Group G] [DecidableEq G] in
/-- The native and graph site maps agree after the actual incident coordinate
identification. Source: SCP10, the local virtual-to-physical map in
Definition 5.1, lines 1278–1296. -/
theorem regularSiteMap_torusIncidentSite_eq_siteMap
    (a : G → G → G → G → Fin d → ℂ) (v : TorusVertex width height)
    (x : (IncidentEdge (torusGraph width height) v → G) → ℂ) :
    regularSiteMap (torusIncidentSite a v) x =
      siteMap a (x ∘ (torusIncidentCoordinatesEquiv v).symm) := by
  classical
  ext s
  change (∑ η, torusIncidentSite a v η s * x η) =
    ∑ θ : G × G × G × G, a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s *
      x ((torusIncidentCoordinatesEquiv v).symm θ)
  have h := Equiv.sum_comp (torusIncidentCoordinatesEquiv (G := G) v)
    (fun θ : G × G × G × G => a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s *
      x ((torusIncidentCoordinatesEquiv v).symm θ))
  simp only [Equiv.symm_apply_apply] at h
  simpa only [Equiv.symm_apply_apply, torusIncidentCoordinatesEquiv_apply,
    torusIncidentCoordinates, torusIncidentSite] using h

/-- Native regular G-injectivity is preserved on the actual incident graph
edges. Source: SCP10, Definition 5.1, lines 1278–1296. This is a coordinate
identification, and introduces no isometry hypothesis. -/
theorem IsGInjective.isGInjective_torusIncidentSite
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) :
    IsGInjective (regularLegRepresentation (IncidentEdge (torusGraph width height) v))
      (regularSiteMap (torusIncidentSite a v)) := by
  classical
  let e := torusIncidentCoordinatesEquiv (G := G) v
  have hrep (g : G) (x : (IncidentEdge (torusGraph width height) v → G) → ℂ) :
      (regularLegRepresentation (IncidentEdge (torusGraph width height) v) g x) ∘ e.symm =
        torusLegRep (leftRegularMatrix G) g (x ∘ e.symm) := by
    funext θ
    simp only [Function.comp_apply, regularLegRepresentation_apply,
      torusLegRep_leftRegularMatrix_apply]
    congr 1
    apply e.injective
    rw [torusIncidentCoordinatesEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, regularSiteMap_torusIncidentSite_eq_siteMap]
    rw [hrep]
    exact LinearMap.congr_fun (ha.invariant g) (x ∘ e.symm)
  · intro x hx hzero
    have hy : x ∘ e.symm ∈ (torusLegRep (leftRegularMatrix G)).invariants := by
      intro g
      rw [← hrep, hx g]
    have hz := ha.injOn_invariants (x ∘ e.symm) hy
      (by simpa only [regularSiteMap_torusIncidentSite_eq_siteMap] using hzero)
    exact e.symm.surjective.injective_comp_right hz

/-- The untwisted native closure is the actual closed contraction of its
incident graph tensor. Source: SCP10, `eq:2d:peps-with-ug-uh`, with identity
closure elements, lines 1935–1990. -/
theorem torusGClosure_one_eq_stateCoeff_torusIncidentSite
    (a : G → G → G → G → Fin d → ℂ) :
    torusGClosure (width := width) (height := height) (leftRegularMatrix G) a 1 1 =
      stateCoeff (groupBondTensor (torusIncidentSite a)) := by
  have hu (f : Edge (torusGraph width height)) : torusClosureEdgeAssignment (G := G) 1 1 f = 1 := by
    unfold torusClosureEdgeAssignment
    cases torusEdgeEquiv.symm f <;>
      simp [torusHorizontalClosureElement, torusVerticalClosureElement]
  have ht : regularTwistedSite (torusIncidentSite (width := width) (height := height) a)
      (torusClosureEdgeAssignment 1 1) = torusIncidentSite a := by
    funext v η s
    have hη : regularTwistedLabels (torusClosureEdgeAssignment (G := G) 1 1) v η = η := by
      funext f
      simp [regularTwistedLabels, hu]
    simp only [regularTwistedSite, hη]
  funext σ
  rw [torusGClosure_eq_stateCoeff_twisted, ht]

end TNLean.PEPS
