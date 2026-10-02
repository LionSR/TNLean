/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionLiftGauge
import TNLean.PEPS.RegularRegionGaugeGram
import TNLean.PEPS.RegularTorusEntropy

/-!
# Actual native closure regions with a supplied integer lift

For a commuting native closure pair, the arithmetic lift gauge removes all
internal closure operators. The actual region matrix is therefore the untwisted
matrix with transported boundary columns. Local regular isometry and connectedness
give its positive Gram matrix and, for a nonempty boundary, its regular invariant
rank. No residual-flatness hypothesis or block Gram identity is supplied.

**Scope restriction (supplied integer lift):** The region is equipped with an
integer square-lattice lift preserving every internal unit step, and the torus
dimensions are at least three. This is an auxiliary consequence of a supplied
lift, not the unrestricted disk theorem. Deriving such lifts from disk topology
and comparing the boundary transports for closure superpositions remain separate;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation in
`eq:2d:move-strings` and the proof of Theorem 6.9, local source lines 1622–1647
and 1935–2072.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- The actual region matrix of a commuting native closure is the untwisted
matrix with columns transported by the explicit integer-lift gauge.
Source: SCP10, seam deformation and boundary disentangling, lines 1622–1647
and 1935–1990. -/
theorem IsGIsometric.regularTwistedOpenRegionMatrix_torusRegionLift
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h) {b : ℕ}
    (e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularTwistedOpenRegionMatrix (torusIncidentSite a) (torusClosureEdgeAssignment g h) R e =
      (regularOpenRegionMatrix (torusIncidentSite a) R e).submatrix (Equiv.refl _)
        (regularRegionBoundaryGaugeEquiv R (torusRegionLiftGauge R L g h)
          (torusClosureEdgeAssignment g h) e) := by
  apply regularTwistedOpenRegionMatrix_eq_submatrix_of_regularRegionGaugeResidual_eq_one
  · intro z v η s
    exact (ha.isGIsometric_torusIncidentSite v).toIsGInjective.regularSiteMap_translation z η s
  · exact regularRegionGaugeResidual_torusRegionLiftGauge hL g h hgh

/-- A connected integer-lifted region of a commuting native closure has a
positive Gram scalar times its transported boundary projector, derived from
local regular isometry. Source: SCP10, lines 1935–1990. -/
theorem IsGIsometric.exists_positive_gram_torusClosureRegionMatrix_of_integerLift
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset (TorusVertex width height))
    (hR : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Connected)
    (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h) {b : ℕ}
    (e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} ≃ Fin b) :
    ∃ c : ℝ, 0 < c ∧
      (regularTwistedOpenRegionMatrix (torusIncidentSite a)
        (torusClosureEdgeAssignment g h) R e).conjTranspose *
        regularTwistedOpenRegionMatrix (torusIncidentSite a)
          (torusClosureEdgeAssignment g h) R e =
      (c : ℂ) • regularRegionGaugeBoundaryProjector R (torusRegionLiftGauge R L g h)
        (torusClosureEdgeAssignment g h) e := by
  exact exists_positive_gram_regularTwistedOpenRegionMatrix_of_regularRegionGaugeResidual_eq_one
    (torusIncidentSite a) (fun v => ha.isGIsometric_torusIncidentSite v) R hR
    (torusRegionLiftGauge R L g h) (torusClosureEdgeAssignment g h)
    (regularRegionGaugeResidual_torusRegionLiftGauge hL g h hgh) e

/-- A nonempty boundary of a connected integer-lifted native closure region has
rank equal to the regular invariant-subspace dimension. Source: SCP10,
Theorem 6.9 boundary count, lines 2027–2037. -/
theorem IsGIsometric.rank_torusClosureRegionMatrix_of_integerLift
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset (TorusVertex width height))
    (hR : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Connected)
    (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (g h : G) (hgh : Commute g h) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularTwistedOpenRegionMatrix (torusIncidentSite a)
      (torusClosureEdgeAssignment g h) R e).rank = Fintype.card G ^ (b - 1) := by
  classical
  exact rank_regularTwistedOpenRegionMatrix_of_regularRegionGaugeResidual_eq_one
    (torusIncidentSite a) (fun v => ha.isGIsometric_torusIncidentSite v) R hR
    (torusRegionLiftGauge R L g h) (torusClosureEdgeAssignment g h)
    (regularRegionGaugeResidual_torusRegionLiftGauge hL g h hgh) hb e

end TNLean.PEPS
