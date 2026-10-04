/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryRoute
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
/-!
# Induced walks retain the region's inserted operators

Replacing exterior and crossing operators does not change an actual walk
entirely inside a region. This elementary restriction identity supports the
closed-walk measurement of SCP10, Section 6.6, lines 2380–2415.
-/
namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]
omit [Group G] in
/-- Restriction to internal edges discards the arbitrary exterior assignment.
Auxiliary to SCP10, the actual region contraction, lines 1935–1957. -/
theorem regularRegionInternalOperators_bondExtension (R : Finset V)
    (u w : Edge Γ → G) :
    regularRegionInternalOperators R (regularRegionBondExtension R u w) =
      regularRegionInternalOperators R u := by
  funext e
  exact ite_eq_left (inducedRegionEdgeEquiv R e).2
/-- Every induced-region walk reads the original internal operators after
extension by arbitrary exterior coefficients. Auxiliary to SCP10,
closed-walk flux measurement, lines 2380–2415. -/
theorem regularWalkHolonomy_induced_bondExtension (R : Finset V)
    (u w : Edge Γ → G) {x y : {v : V // v ∈ R}}
    (p : (Γ.induce (R : Set V)).Walk x y) :
    regularWalkHolonomy (regularRegionInternalOperators R
      (regularRegionBondExtension R u w)) p =
      regularWalkHolonomy u (p.map (SimpleGraph.Embedding.induce (R : Set V)).toHom) := by
  rw [regularRegionInternalOperators_bondExtension, regularWalkHolonomy_inducedWalk]
end TNLean.PEPS
