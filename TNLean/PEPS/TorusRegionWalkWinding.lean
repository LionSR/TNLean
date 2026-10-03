/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWalkWinding
import TNLean.PEPS.TorusRegionLiftGauge
import TNLean.PEPS.TorusRegionRealization
import TNLean.PEPS.RegularBoundaryRoute

/-!
# Actual region walk crossing numbers from integer lifts

An integer unit-step lift determines the seam crossing numbers of every actual
walk in the induced region graph. They are the differences of the two integer
deck coordinates of its endpoints. The proof uses the universal abelian closure
with group `Multiplicative (ℤ × ℤ)`, so both crossing numbers are recovered at
once from the previously established native transport and gradient identities.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:move-strings`, lines 1622–1647, and the complement path argument in the
proof of Theorem 6.9, lines 1935–1990; auxiliary walk identity.

Simple connectedness of the actual cell union supplies such a lift and makes
the crossing numbers independent of the interior walk with fixed endpoints.

**Scope restriction (auxiliary interior walks):** These statements concern
walks through the region. They do not assert the exterior-path existence
required by Theorem 6.9. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The crossing numbers of an actual region walk are the differences of its
endpoint deck coordinates. Source: SCP10, seam deformation and complement path
argument, lines 1622–1647 and 1935–1990. -/
theorem torusWalkWinding_of_isTorusRegionIntegerLift
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) {v w : {v // v ∈ R}}
    (p : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Walk v w) :
    torusWalkWinding
        (p.map (SimpleGraph.Embedding.induce (R : Set (TorusVertex width height))).toHom) =
      ((L w).1 / (width : ℤ) - (L v).1 / (width : ℤ),
        (L w).2 / (height : ℤ) - (L v).2 / (height : ℤ)) := by
  let g := Multiplicative.ofAdd ((0, -1) : ℤ × ℤ)
  let h := Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)
  have hgh : Commute g h := Commute.all _ _
  let k := torusRegionLiftGauge R L g h
  have hu : regularRegionInternalOperators R (torusClosureEdgeAssignment g h) =
      (fun e => k e.1.2 * (k e.1.1)⁻¹) := by
    funext e
    exact (torusRegionLiftGauge_gradient hL g h hgh (inducedRegionEdgeEquiv R e)).symm
  have hp : regularWalkHolonomy (regularRegionInternalOperators R
      (torusClosureEdgeAssignment g h)) p = k w * (k v)⁻¹ := by
    rw [hu, regularWalkHolonomy_gradient]
  rw [regularWalkHolonomy_inducedWalk,
    regularWalkHolonomy_torusClosureEdgeAssignment g h hgh] at hp
  have he := congrArg Multiplicative.toAdd hp
  simpa [g, h, k, torusRegionLiftGauge, toAdd_mul, toAdd_inv, toAdd_zpow,
    Prod.smul_mk, sub_eq_add_neg] using he

/-- Simple connectedness of the actual closed-cell realization makes the seam
crossing numbers independent of the interior walk with fixed endpoints. The
integer lift is derived, rather than supplied. Source: SCP10, contractible
block and seam deformation, lines 1935–1990. -/
theorem torusWalkWinding_eq_of_isSimplyConnected
    (R : Finset (TorusVertex width height))
    (hSC : IsSimplyConnected (torusRegionRealization R)) {v w : {v // v ∈ R}}
    (p q : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Walk v w) :
    torusWalkWinding
        (p.map (SimpleGraph.Embedding.induce (R : Set (TorusVertex width height))).toHom) =
      torusWalkWinding
        (q.map (SimpleGraph.Embedding.induce (R : Set (TorusVertex width height))).toHom) := by
  obtain ⟨L, hL⟩ := exists_isTorusRegionIntegerLift_of_isSimplyConnected R hSC v
  simp only [torusWalkWinding_of_isTorusRegionIntegerLift hL]

end TNLean.PEPS
