/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockRegularIntersection

/-!
# Regional intersection with the source's exterior legs retained

The signatures impose no abelian, connectedness, exterior-label or global
flatness assumptions. The concrete source geometry is also instantiated with
the nonabelian permutation group on three letters.
-/

open TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

example {R S : Finset V} {b : V} (hRS : R ∩ S = {b})
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v) :
    regularGlobalRegionRange (Γ := Γ) (G := G) R ⊓ regularGlobalRegionRange S =
      regularGlobalRegionRange (R ∪ S) :=
  regularGlobalRegionRange_inf_eq_union hRS hcross

example {R S : Finset V} (hRS : R ⊆ S) :
    regularGlobalRegionRange (Γ := Γ) (G := G) S ≤ regularGlobalRegionRange R :=
  regularGlobalRegionRange_antitone hRS

example {R S : Finset V} {b : V} (hRS : R ∩ S = {b})
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v)
    (α : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) :
    IsRegularRegionHalfEdgeFlat (R ∪ S) (restrictRegularRegionHalfEdges (R ∪ S) α) ↔
      IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) ∧
      IsRegularRegionHalfEdgeFlat S (restrictRegularRegionHalfEdges S α) :=
  isRegularRegionHalfEdgeFlat_union_iff hRS hcross α

example :
    regularGlobalRegionRange (Γ := threeBlockFourLegGraph) (G := Equiv.Perm (Fin 3))
        threeBlockLeftRegion ⊓ regularGlobalRegionRange threeBlockRightRegion =
      regularGlobalRegionRange threeBlockRegion :=
  threeBlock_regularGlobalRegionRange_intersection

-- This equality lives on the three core physical factors only.
example :
    regularRegionRangeWithin (Γ := threeBlockFourLegGraph) (G := Equiv.Perm (Fin 3))
        threeBlockRegion threeBlockLeftRegion ⊓
        regularRegionRangeWithin threeBlockRegion threeBlockRightRegion =
      (Matrix.mulVecLin (regularProjectorOpenRegionMatrix
        (Γ := threeBlockFourLegGraph) (G := Equiv.Perm (Fin 3)) threeBlockRegion)).range :=
  threeBlock_regularRegionRange_intersection

example (v : Fin 11) (hv : v ∈ threeBlockRegion) :
    Fintype.card (IncidentEdge threeBlockFourLegGraph v) = 4 :=
  threeBlockFourLegGraph_core_degree v hv

example : Fintype.card {e : Edge threeBlockFourLegGraph //
    IsRegionBoundaryEdge threeBlockRegion e} = 8 :=
  threeBlockFourLegGraph_boundary_card

-- The eight exterior vertices are distinct degree-one endpoints.
example (v : Fin 11) (hv : v ∉ threeBlockRegion) :
    Fintype.card (IncidentEdge threeBlockFourLegGraph v) = 1 := by
  revert v
  decide

-- The no-cross-edge condition is a genuine geometric restriction.
example : ∃ u ∈ ({0, 1} : Finset (Fin 3)) \ {1, 2},
    ∃ v ∈ ({1, 2} : Finset (Fin 3)) \ {0, 1},
      (⊤ : SimpleGraph (Fin 3)).Adj u v := by
  decide

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.isRegularRegionHalfEdgeFlat_union_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.isRegularRegionHalfEdgeFlat_union_iff

/--
info: 'TNLean.PEPS.regularGlobalRegionRange_inf_eq_union'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularGlobalRegionRange_inf_eq_union

/--
info: 'TNLean.PEPS.threeBlock_regularGlobalRegionRange_intersection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.threeBlock_regularGlobalRegionRange_intersection

/--
info: 'TNLean.PEPS.regularRegionRangeWithin_inf_eq_range'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularRegionRangeWithin_inf_eq_range

/--
info: 'TNLean.PEPS.threeBlock_regularRegionRange_intersection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.threeBlock_regularRegionRange_intersection
