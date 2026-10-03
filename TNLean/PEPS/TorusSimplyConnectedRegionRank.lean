/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionRealization
import TNLean.PEPS.TorusRegionLiftGram

/-!
# Actual closure-region rank from geometric simple connectedness

Simple connectedness of the closed-cell realization supplies an integer lift
preserving the native internal unit steps. For a commuting closure pair, the
lift gauge therefore removes all internal closure operators. Applying the
actual connected-region rank theorem gives the regular boundary dimension.
Neither a lift nor a residual-flatness or block Gram identity is an input.

**Scope restriction (auxiliary geometric rank statement):** The torus dimensions
are at least three, the actual closed-cell realization is simply connected,
and the induced native graph is connected. The two connectedness conditions
are kept separate because closed cells may meet at diagonal points. The result
concerns the actual open-region matrix of one commuting closure; it is not the
full disk entropy theorem or a statement about coherent closure superpositions.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the boundary-rank
calculation in Theorem 6.9, local source lines 1935–1990 and 2027–2037.

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

/-- The actual open-region matrix of a commuting native closure has the regular
boundary rank when its cell realization is simply connected and its native
induced graph is connected. Source: SCP10, Theorem 6.9 boundary count,
lines 1935–1990 and 2027–2037. -/
theorem IsGIsometric.rank_torusClosureRegionMatrix_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset (TorusVertex width height))
    (hR : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (g h : G) (hgh : Commute g h) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularTwistedOpenRegionMatrix (torusIncidentSite a)
      (torusClosureEdgeAssignment g h) R e).rank = Fintype.card G ^ (b - 1) := by
  obtain ⟨o⟩ := hR.nonempty
  obtain ⟨L, hL⟩ := exists_isTorusRegionIntegerLift_of_isSimplyConnected R hSC o
  exact ha.rank_torusClosureRegionMatrix_of_integerLift R hR L hL g h hgh hb e

end TNLean.PEPS
