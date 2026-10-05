/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularLocalRegionIntersection

/-!
# Regular intersection on the three-block four-leg geometry

The three core vertices form the path 0–1–2. Eight distinct exterior leaves
supply the other legs: three at each endpoint and two at the middle vertex.
Thus all three core tensors have four legs, and the union has eight independent
boundary labels. Both the ambient identity with exterior physical factors and
the localized identity on only the three core physical factors are proved.

The range identity is the regular-representation specialization of the
three-block geometry in SCP10, arXiv:1001.3807, Theorem 5.4. This does not assert
the source theorem for arbitrary semi-regular representations or arbitrary
G-injective site maps.
-/

namespace TNLean.PEPS

/-- Three four-legged core vertices and eight distinct exterior endpoints. -/
def threeBlockFourLegGraph : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v ∈ ({1, 3, 4, 5} : Finset (Fin 11))) ∨
    (u = 1 ∧ v ∈ ({2, 6, 7} : Finset (Fin 11))) ∨
    (u = 2 ∧ v ∈ ({8, 9, 10} : Finset (Fin 11)))

instance : DecidableRel threeBlockFourLegGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- The left two blocks in the source intersection geometry. -/
def threeBlockLeftRegion : Finset (Fin 11) := {0, 1}

/-- The right two blocks in the source intersection geometry. -/
def threeBlockRightRegion : Finset (Fin 11) := {1, 2}

/-- The three core blocks, with all eight exterior legs open. -/
def threeBlockRegion : Finset (Fin 11) := {0, 1, 2}

/-- Each of the three core vertices has four incident legs. -/
theorem threeBlockFourLegGraph_core_degree (v : Fin 11) (hv : v ∈ threeBlockRegion) :
    Fintype.card (IncidentEdge threeBlockFourLegGraph v) = 4 := by
  revert v
  decide

/-- The three-block region has eight distinct boundary edges. -/
theorem threeBlockFourLegGraph_boundary_card :
    Fintype.card {e : Edge threeBlockFourLegGraph //
      IsRegionBoundaryEdge threeBlockRegion e} = 8 := by
  decide

/-- The literal four-leg geometry satisfies the regular intersection identity.
The eight boundary legs and all complementary physical coordinates remain
arbitrary, rather than being contracted into a closed one-dimensional strip. -/
theorem threeBlock_regularGlobalRegionRange_intersection
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    regularGlobalRegionRange (Γ := threeBlockFourLegGraph) (G := G)
        threeBlockLeftRegion ⊓ regularGlobalRegionRange threeBlockRightRegion =
      regularGlobalRegionRange threeBlockRegion := by
  have hu : threeBlockLeftRegion ∪ threeBlockRightRegion = threeBlockRegion := by decide
  rw [← hu]
  apply regularGlobalRegionRange_inf_eq_union (b := 1)
  · decide
  · decide

/-- The regular intersection identity on exactly the three core physical
factors. The right side is the actual open-region range with eight independent
boundary virtual labels; no exterior physical factor remains. -/
theorem threeBlock_regularRegionRange_intersection
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    regularRegionRangeWithin (Γ := threeBlockFourLegGraph) (G := G)
        threeBlockRegion threeBlockLeftRegion ⊓
        regularRegionRangeWithin threeBlockRegion threeBlockRightRegion =
      (Matrix.mulVecLin (regularProjectorOpenRegionMatrix
        (Γ := threeBlockFourLegGraph) (G := G) threeBlockRegion)).range := by
  have hu : threeBlockLeftRegion ∪ threeBlockRightRegion = threeBlockRegion := by decide
  rw [← hu]
  apply regularRegionRangeWithin_inf_eq_range (b := 1)
  · decide
  · decide

end TNLean.PEPS
