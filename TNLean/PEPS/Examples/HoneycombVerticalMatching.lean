/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.GraphStateCutConverse

/-! The vertical matching and its quotient directions on the six-by-four brick wall. -/

namespace TNLean.PEPS.VerticalMatching
private instance : Fact (1 < 6) := ⟨by decide⟩
private instance : Fact (1 < 4) := ⟨by decide⟩
abbrev Site := TorusVertex 6 4
abbrev G := honeycombGraph 6 4
def mate (v : Site) : Site :=
  if honeycombUp 6 4 v then (v.1,v.2+1) else (v.1,v.2-1)

theorem matching : ∀ v, mate (mate v) = v ∧ mate v ≠ v ∧ G.Adj v (mate v) := by decide

def anchor (v : Site) := if honeycombUp 6 4 v then v else mate v

theorem fibers : ∀ v w, anchor v = anchor w ↔ w = v ∨ w = mate v := by decide

def next (p : Site) : Finset Site :=
  {(p.1+1,p.2-1),(p.1-1,p.2-1),(p.1+1,p.2+1),(p.1-1,p.2+1)}

set_option maxRecDepth 10000 in
theorem quotient_neighbors : ∀ p q : Site, honeycombUp 6 4 p → honeycombUp 6 4 q →
    ((p ≠ q ∧ (G.Adj p q ∨ G.Adj p (mate q) ∨ G.Adj (mate p) q ∨ G.Adj (mate p) (mate q)))
      ↔ q ∈ next p) := by decide

/-- Two steps generating this square are (+1,-1) and (-1,-1) from (2,2). -/
def anchors : Finset Site := {(2,2),(3,1),(1,1),(2,0)}
def lifted : Finset Site := Finset.univ.filter fun v => anchor v ∈ anchors

theorem lifted_not_injective : ¬ Function.Injective (openRegionMap (graphStatePEPS G) lifted) := by
  intro h
  let l : GraphStateCut.Crossing G lifted := ⟨⟨((1,3),(2,3)), by decide⟩, by decide⟩
  let r : GraphStateCut.Crossing G lifted := ⟨⟨((2,3),(3,3)), by decide⟩, by decide⟩
  have eq : GraphStateCut.inside G lifted l = GraphStateCut.inside G lifted r := by decide
  exact (by decide : l ≠ r) ((GraphStateCut.injective_iff G lifted).1 h eq)

end TNLean.PEPS.VerticalMatching
