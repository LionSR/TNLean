/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusComplementCycleWords
import TNLean.PEPS.RegularCycleControlledBoundary

/-!
# One complementary unitary from fixed geometric winding data

Choose genuine complementary root loops whose seam crossing numbers match the
actual two-tree boundary routes. Their free-group words define one controlled
permutation of the original complementary half-edge physical basis. This unitary
is chosen before the commuting closure labels. Its action on every actual
canonical complementary block removes the relative crossing multipliers at the
boundary input transported by the inverse region map. The common reference
multiplier and the conjugated cycle constraint are retained explicitly.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of Theorem 6.9,
local source lines 1935–1990. No group-valued relative transport identity or
factorization of a contracted tensor is assumed.

**Scope restriction (geometric winding data):** Width and height are at least
three, and the actual complementary loops with the specified winding are
supplied. Their existence for the paper's disk geometry remains separate,
as recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Fixed genuine complementary loops with matching actual winding determine
one unitary, independent of all commuting closure pairs, with the exact
controlled coefficient formula for the actual complementary block.
Source: SCP10, accessible complement and disentangling, lines 1935–1990. -/
theorem exists_unitary_torusComplementDisentangling_of_winding_eq (R : Finset X)
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj] [DecidableRel TS.Adj]
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
    (f₀ : {e : Edge Γₜ // IsRegionBoundaryEdge R e})
    (p : {e : Edge Γₜ // IsRegionBoundaryEdge R e} →
      ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS)
    (hwind : ∀ f, torusWalkWinding
        ((p f).map (SimpleGraph.Embedding.induce
          ((Finset.univ \ R : Finset X) : Set X)).toHom) =
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f)) :
    ∃ U : Matrix (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R))
        (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R)) ℂ,
      U ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R)) ℂ ∧
      ∀ (g h : G) (_hgh : Commute g h)
        (c : RegularRegionCoordinates (Γ := Γₜ) (G := G) (Finset.univ \ R) TS oS)
        (θ : {e : Edge Γₜ // IsRegionBoundaryEdge R e} → G),
        (U * regularProjectorTwistedRegionMatrix (Finset.univ \ R)
            (torusClosureEdgeAssignment g h))
          ((regularRegionCoordinatesEquiv (Finset.univ \ R) TS hTS htreeS oS).symm c)
          (fun f => (regularRegionBoundaryTransport R
            (regularRegionTreeGauge R TR hTR htreeR oR (torusClosureEdgeAssignment g h)).1
            (torusClosureEdgeAssignment g h)).symm θ
              ((regionBoundaryEdgeComplEquiv (G := Γₜ) R).symm f)) =
        (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card * ∑ x : G,
          if c.1 = (fun f => x * regularCombinedBoundaryTransport R
              (regularRegionTreeGauge R TR hTR htreeR oR (torusClosureEdgeAssignment g h)).1
              (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS
                (torusClosureEdgeAssignment g h)).1 (torusClosureEdgeAssignment g h) 1 f₀ *
              θ ((regionBoundaryEdgeComplEquiv (G := Γₜ) R).symm f)) ∧
            c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual (Finset.univ \ R)
              TS hTS htreeS oS (torusClosureEdgeAssignment g h) e * x⁻¹)
          then 1 else 0 := by
  classical
  let S := Finset.univ \ R
  let U := regularComplementWalkControlMatrix (G := G) R TS hTS htreeS oS
    (fun _ => oS) (fun _ => oS) p
  refine ⟨U, regularComplementWalkControlMatrix_mem_unitaryGroup
    R TS hTS htreeS oS (fun _ => oS) (fun _ => oS) p, ?_⟩
  intro g h hgh c θ
  exact regularCycleControlledBoundaryMatrix_mul_coordinates_of_combined_relative_walk_words
    R (regularRegionTreeGauge R TR hTR htreeR oR (torusClosureEdgeAssignment g h)).1
    TS hTS htreeS oS (fun _ => oS) (fun _ => oS) p (torusClosureEdgeAssignment g h) f₀
    (regularRegionCycleWord_eval_torusClosure_of_winding_eq R TR TS hTR hTS
      htreeR htreeS oR oS f₀ p hwind g h hgh) c θ

end TNLean.PEPS
