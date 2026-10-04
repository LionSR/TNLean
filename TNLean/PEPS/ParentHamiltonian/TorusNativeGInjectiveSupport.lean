/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusRegularRegionSupport
import TNLean.PEPS.TorusIncidentGInjectivity

/-!
# Local support rigidity for native regular G-injective tensors

The native four-leg regular representation gives G-injective tensors on the
actual incident graph edges. Consequently the physical density of every
single site recovers its full local ground space. Two native descriptions
with equal untwisted closures have equal single-site ground spaces; if the
descriptions use two different finite groups, those groups have equal orders.

**Scope restriction (native regular tensors):** Both torus periods are at
least three, the virtual representation is regular, and the closure elements
are the identity. This gives necessary local relations, not a factorization
into virtual bond gauges. The more general representation and closure cases
remain separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1
and Corollary 6.10, local source lines 1278–1296 and 2074–2090.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- Native regular G-injectivity recovers the full one-site physical ground
space from its closed-state reduced density. Source: SCP10, Definition 5.1
and Corollary 6.10, lines 1278–1296 and 2074–2090. -/
theorem IsGInjective.range_regionReducedDensity_torus_singleton
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) :
    (Matrix.mulVecLin (regionReducedDensity (groupBondTensor (torusIncidentSite a)) {v})).range =
      regionGroundSpace (groupBondTensor (torusIncidentSite a)) {v} :=
  range_regionReducedDensity_torus_singleton_of_regular (torusIncidentSite a)
    (fun w => ha.isGInjective_torusIncidentSite w) v

/-- The native regular one-site reduced density has rank the cube of the
group order. Source: SCP10, Corollary 6.10, lines 2074–2090. -/
theorem IsGInjective.rank_regionReducedDensity_torus_singleton
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) :
    (regionReducedDensity (groupBondTensor (torusIncidentSite a)) {v}).rank = Fintype.card G ^ 3 :=
  rank_regionReducedDensity_torus_singleton_of_regular (torusIncidentSite a)
    (fun w => ha.isGInjective_torusIncidentSite w) v

/-- Equal untwisted native regular closures have equal one-site ground
spaces. This is a necessary local relation toward a Fundamental Theorem,
derived from SCP10, Definition 5.1 and Corollary 6.10. -/
theorem regionGroundSpace_torus_singleton_eq_of_torusGClosure_one_eq
    (a b : G → G → G → G → Fin d → ℂ)
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (hb : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap b))
    (hstate : torusGClosure (width := width) (height := height) (leftRegularMatrix G) a 1 1 =
      torusGClosure (leftRegularMatrix G) b 1 1) (v : TorusVertex width height) :
    regionGroundSpace (groupBondTensor (torusIncidentSite a)) {v} =
      regionGroundSpace (groupBondTensor (torusIncidentSite b)) {v} := by
  apply regionGroundSpace_torus_singleton_eq_of_sameState_regular (torusIncidentSite a)
    (torusIncidentSite b) (fun w => ha.isGInjective_torusIncidentSite w)
    (fun w => hb.isGInjective_torusIncidentSite w) _ v
  rw [torusGClosure_one_eq_stateCoeff_torusIncidentSite,
    torusGClosure_one_eq_stateCoeff_torusIncidentSite] at hstate
  exact fun σ => congrFun hstate σ

/-- Equal untwisted native closures determine the order of the finite regular
virtual group, including when the groups in the two descriptions differ.
Source: SCP10, the regular boundary count in Corollary 6.10,
lines 2074–2090. No group isomorphism is asserted. -/
theorem card_group_eq_of_torusGClosure_one_eq
    {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (a : G → G → G → G → Fin d → ℂ)
    (b : H → H → H → H → Fin d → ℂ)
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (hb : IsGInjective (torusLegRep (leftRegularMatrix H)) (siteMap b))
    (hstate : torusGClosure (width := width) (height := height) (leftRegularMatrix G) a 1 1 =
      torusGClosure (leftRegularMatrix H) b 1 1) :
    Fintype.card G = Fintype.card H := by
  apply card_group_eq_of_sameState_regular_torus (width := width) (height := height)
    (torusIncidentSite a)
    (torusIncidentSite b) (fun w => ha.isGInjective_torusIncidentSite w)
    (fun w => hb.isGInjective_torusIncidentSite w)
  rw [torusGClosure_one_eq_stateCoeff_torusIncidentSite,
    torusGClosure_one_eq_stateCoeff_torusIncidentSite] at hstate
  exact fun σ => congrFun hstate σ

end TNLean.PEPS
