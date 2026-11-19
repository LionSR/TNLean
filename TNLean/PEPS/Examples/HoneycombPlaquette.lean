/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.HoneycombCluster

/-! Edgewise contraction of six graph-state bonds with six outgoing legs.
The edge lists are parameters: identifying them with all the incidences of a
honeycomb face is a separate geometric step. -/

open scoped BigOperators
open ManyBody (Edge)

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- Sum the six internal bond indices while fixing the six boundary indices.
Each factor is the same oriented leg used in graphStatePEPS.component. -/
noncomputable def sixBondContraction (inner outer : Fin 6 → Edge G)
    (site : Fin 6 → V) (s : V → Fin 2) (β : Fin 6 → Fin 2) : ℂ :=
  ∑ η : Fin 6 → Fin 2,
    (∏ i, graphStateLeg G (inner i).1.1 (inner i) (η i) (s (inner i).1.1) *
      graphStateLeg G (inner i).1.2 (inner i) (η i) (s (inner i).1.2)) *
    ∏ i, graphStateLeg G (site i) (outer i) (β i) (s (site i))

/-- Each contracted internal bond contributes the normalized controlled-Z sign.
The remaining factors are the six boundary identity or Hadamard entries. -/
theorem sixBondContraction_factor (inner outer : Fin 6 → Edge G)
    (site : Fin 6 → V) (s : V → Fin 2) (β : Fin 6 → Fin 2) :
    sixBondContraction G inner outer site s β =
      (∏ i, hadamardEntry (s (inner i).1.1) (s (inner i).1.2)) *
      ∏ i, graphStateLeg G (site i) (outer i) (β i) (s (site i)) := by
  classical
  unfold sixBondContraction
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun (i : Fin 6) (b : Fin 2) =>
    graphStateLeg G (inner i).1.1 (inner i) b (s (inner i).1.1) *
      graphStateLeg G (inner i).1.2 (inner i) b (s (inner i).1.2))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h : (inner i).1.1 ≠ (inner i).1.2 := (inner i).2.1.ne
  simp [graphStateLeg, h]

end TNLean.PEPS

namespace TNLean.PEPS.HoneycombFace

private instance : Fact (1 < 6) := ⟨by decide⟩
private instance : Fact (1 < 4) := ⟨by decide⟩

abbrev Site := TorusVertex 6 4
abbrev graph := honeycombGraph 6 4

/-- Counterclockwise boundary, starting at the lower left corner. -/
def vertex : Fin 6 → Site := ![(0,0), (1,0), (2,0), (2,1), (1,1), (0,1)]

/-- Endpoint outside the face, in the same cyclic order. -/
def exterior : Fin 6 → Site := ![(5,0), (1,3), (3,0), (3,1), (1,2), (5,1)]

set_option maxRecDepth 10000 in
/-- Each face vertex has exactly three neighbours: its cyclic predecessor, its cyclic successor,
and the exterior endpoint assigned to that vertex. -/
theorem incidence : ∀ (i : Fin 6) (w : Site), graph.Adj (vertex i) w ↔
    w = vertex (i - 1) ∨ w = vertex (i + 1) ∨ w = exterior i := by decide

/-- The six cyclic indices label distinct torus sites, so the face has six vertices. -/
theorem distinct_sites : ∀ i j, vertex i = vertex j → i = j := by decide

/-- Every listed exterior endpoint lies outside the six-vertex face. -/
theorem exterior_outside : ∀ i j, exterior i ≠ vertex j := by decide

private def bond (a b : Site) (h : graph.Adj a b) : Edge graph :=
  if hab : a < b then ⟨(a,b), hab, h⟩
  else ⟨(b,a), lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm h.ne), h.symm⟩

/-- The internal bond from a face vertex to its cyclic successor. Its stored endpoints
are ordered by the ambient torus vertex order. -/
def inner (i : Fin 6) : Edge graph :=
  bond _ _ ((incidence i _).2 (Or.inr (Or.inl rfl)))

/-- The crossing bond from a face vertex to its unique exterior neighbour. Its stored
endpoints are ordered by the ambient torus vertex order. -/
def outer (i : Fin 6) : Edge graph :=
  bond _ _ ((incidence i _).2 (Or.inr (Or.inr rfl)))

/-- With boundary bits fixed, summing the six internal bond indices gives one
normalized controlled-Z sign per internal bond and one oriented identity or
Hadamard entry per crossing bond. -/
theorem contraction (s : Site → Fin 2) (β : Fin 6 → Fin 2) :
    sixBondContraction graph inner outer vertex s β =
      (∏ i, hadamardEntry (s (inner i).1.1) (s (inner i).1.2)) *
      ∏ i, graphStateLeg graph (vertex i) (outer i) (β i) (s (vertex i)) :=
  sixBondContraction_factor graph inner outer vertex s β

end TNLean.PEPS.HoneycombFace
